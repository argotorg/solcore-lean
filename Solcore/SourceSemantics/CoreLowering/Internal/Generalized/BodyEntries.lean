import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.Ancestry
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures

/-!
# Generalized locals: body entries

Entry into generalized local bodies: contextual materialization and allocation, associations, parameter admission and the body compiler.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization
/-! A stored closure retains the Source view of its actual allocation context.
The real local read selects the cumulative candidate. Its matcher fixes the
new substitution, so closed earlier substitutions transport that retained view
to the accepted candidate body. The same Packet and capture environment supply
Code; no body execution law or equality of unrelated ancestry states is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization
open Core Frontend SourceInference TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open LambdaMetadataViews
open CallableAncestryProfiles.SourceComposition

private theorem node_substitution {source view : Node} (related : NodeView source view)
    (substitution : Substitution) :
    NodeView (source.applySubstitution substitution) (view.applySubstitution substitution) := by
  cases related with
  | expression id form =>
      exact .expression id (congrArg (ExpressionForm.applySubstitution substitution) form)
  | statement node => exact .statement _

private theorem nodes_substitution {source view : List Node}
    (related : DataPatternValues.ListRel NodeView source view) (substitution : Substitution) :
    DataPatternValues.ListRel NodeView
      (source.map (Node.applySubstitution substitution))
      (view.map (Node.applySubstitution substitution)) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (node_substitution head substitution) ih

theorem substitute_view {source view : TypedSource} (related : MetadataView source view)
    (substitution : Substitution) :
    MetadataView (source.applySubstitution substitution) (view.applySubstitution substitution) :=
  ⟨related.owner, congrArg (List.map (TypedBinder.applySubstitution substitution)) related.inputs,
    related.roots, nodes_substitution related.nodes substitution⟩

/-- This is an attachment to the existing Snapshot. Creation supplies the
current body's view and its actual closed native context. -/
structure Attachment (function : Dynamic.GeneralizedClosure)
    (binding : SourceCoreLocalPolymorphism.Binding) (active : Substitution) : Prop where
  closed : RangesClosed active
  view : MetadataView function.source (binding.source.applySubstitution active)

theorem Attachment.named {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding}
    (same : function.source = binding.source) : Attachment function binding [] :=
  ⟨RangesClosed.empty, by rw [EmptySourceSubstitution.source, same]; exact .refl _⟩

variable {catalog : SourceCoreLocalPolymorphism.Catalog} {caller : SourceCoreLocalPolymorphism.Key}
  {active : Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Core.Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem lookup_eq
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType) :
    ∀ metavariable, semantic.lookup? metavariable = receipt.child.lookup? metavariable := by
  have matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme actual =
      some receipt.child := by
    rw [sameScheme, sameType, ← receipt.rawType]
    exact receipt.matched
  exact CallableClosedSchemeSubstitutionAgreement.runtime_instantiation_lookup_eq matched instantiation

theorem source_view
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actual : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actual requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actual = receipt.node.rawType)
    (attachment : Attachment function receipt.binding active)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw) :
    MetadataView
      (function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source
      packet.original.emission.prepared.source := by
  change MetadataView (function.source.applySubstitution semantic) _
  rw [CallableFlexibleSubstitutionAgreement.typedSource_congr
    (lookup_eq receipt instantiation sameScheme sameType) function.source]
  rw [GeneralizedLocalLambdaEmissionFacts.Emission.source, candidateSource,
    receipt.candidate_key, CallableAncestryProfiles.SourceComposition.source _ _ attachment.closed]
  exact substitute_view attachment.view receipt.child

theorem header_of_view
    {function : Dynamic.GeneralizedClosure} {semantic : Substitution} {evidence : Dynamic.EvidenceEnvironment}
    {inputs : Inputs} {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Core.Expr}
    (packet : Packet inputs candidate raw)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    (view : MetadataView (function.instantiate semantic evidence).source
      packet.original.emission.prepared.source) :
    (function.instantiate semantic evidence).parameters = packet.parameters ∧
    (function.instantiate semantic evidence).resultType = packet.result ∧
    (function.instantiate semantic evidence).body = packet.statements := by
  obtain ⟨node, occurrence, form, _⟩ := captures.occurrence
  have found := lookupExpression?_complete unique occurrence
  have substituted := SourceTypedRuntime.TypedSource.lookupExpression?_applySubstitution
    function.source semantic function.initializer node found
  obtain ⟨sameNode, sameFound, _, sameForm⟩ := view.expression packet.found
  change (function.source.applySubstitution semantic).lookupExpression? inputs.initializer = some sameNode at sameFound
  rw [initializer] at substituted
  have nodes := Option.some.inj (substituted.symm.trans sameFound)
  have forms := (congrArg ExpressionNode.form nodes).trans (sameForm.trans packet.form)
  simp only [ExpressionNode.applySubstitution, form, ExpressionForm.applySubstitution] at forms
  exact ExpressionForm.lambda.inj forms

theorem code_at_read
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {function : Dynamic.GeneralizedClosure} {context : Solcore.SourceSemantics.Context}
    {callerEvidence produced : Dynamic.EvidenceEnvironment} {actualType : TypeSystem.Ty}
    {requirements : List RequirementId} {semantic : Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      function.binder actualType requirements semantic produced)
    (sameScheme : function.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    (attachment : Attachment function receipt.binding active)
    (candidateSource : receipt.candidate.origin.source = receipt.binding.source)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {inputs : Inputs} {raw : Core.Expr}
    (packet : Packet inputs receipt.candidate raw)
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    (captures : Dynamic.GeneralizedClosureCaptures function.definitionContext function.source function.captured
      function.binder function.initializer function)
    (unique : NodeOccurrencesUnique function.source)
    (initializer : function.initializer = inputs.initializer)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw receipt.candidate.type prepared.layouts.definitions)
    (profile : checked.catalog.callableContracts = true)
    (native : CallableIndexedHistory.NativeFrame) :
    let instantiated := function.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ code : CallableIndexedLambdaValues.Code prepared instantiated inputs.scope captured.administrative,
      code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared ∧
      code.active = packet.original.emission.prepared.substitution ∧
      code.id = inputs.initializer ∧ code.lowered = packet.original.lowered ∧
      code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel ∧
      code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared ∧
      code.fuel = packet.fuel ∧ code.descriptor.id = indexed.descriptor.id ∧
      HEq code.receipt packet.certificate ∧
      code.view = packet.original.emission.prepared.source ∧
      code.reasonAt = inputs.reasonAt ∧
      CallableIndexedLambdaValues.value code captured.embedding native actual =
        GeneralizedLocalInstanceValues.value indexed captured.embedding native actual := by
  have view := source_view receipt instantiation sameScheme sameType attachment candidateSource packet
  obtain ⟨parameters, result, body⟩ := header_of_view packet captures unique initializer view
  have typedLowered : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      packet.original.lowered.expression (LanguageResult.resultType packet.original.lowered.type)
      prepared.layouts.definitions := by
    rw [packet.original.extracted, ← packet.original.nativeType]
    exact LanguageResult.success_hasType typed
  obtain ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons⟩ :=
    indexed.code_at_read _ captured.administrative parameters result body profile view typedLowered
  exact ⟨code, compilation, active, id, lowered, policy, lowerBody, fuel, descriptor, certificate, codeView, reasons,
    GeneralizedLocalMaterializedCode.value_eq indexed code lowered policy id captured.embedding native actual⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualMaterialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAllocation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
/-! Materialized local functions retain their real compiler row, Source
instantiation, lexical capture and read-time view. The relation records no
execution law for the body and does not identify the two native contexts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open GeneralizedLocalDescriptorOrigin (Origin)

structure Materialization (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) where
  descriptor : Dynamic.GeneralizedClosure
  binding : SourceCoreLocalPolymorphism.Binding
  lexical : TypeSystem.Substitution
  inputs : Inputs
  candidate : SourceCoreLocalPolymorphism.Instance
  raw : Expr
  packet : Packet inputs candidate raw
  indexed : Indexed compiled.indexed packet
  bodyProfile : GeneralizedLocalBodyProfile.Profile inputs.locals inputs.current.owner
    packet.original.emission.prepared.source inputs.initializer
  sameLexical : indexed.lexical = lexical
  owner : inputs.current.owner = binding.caller
  initializer : inputs.initializer = binding.initializer
  candidateSource : candidate.origin.source = binding.source
  candidateBinder : candidate.origin.binder.id = binding.binder.id
  descriptorSource : descriptor.source = binding.source
  descriptorInitializer : descriptor.initializer = binding.initializer
  binderScheme : descriptor.binder.scheme = binding.binder.scheme
  origin : Origin compiled.indexed descriptor binding lexical
  namedLexical : lexical = []
  namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩
  descriptorUnique : NodeOccurrencesUnique descriptor.source
  sourceCaptures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
    descriptor.captured descriptor.binder descriptor.initializer descriptor
  context : Solcore.SourceSemantics.Context
  callerEvidence : Dynamic.EvidenceEnvironment
  produced : Dynamic.EvidenceEnvironment
  actualType : TypeSystem.Ty
  requirements : List RequirementId
  semantic : TypeSystem.Substitution
  instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
    actualType requirements semantic produced
  materialized : function = descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
  actual : Environment
  captured : Captures compiled.indexed mapping world inputs.scope function.captured actual
  capturedDeclarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.context
  frameLocation : Core.Location
  frameReference : captured.canonical[GeneralizedLocalInstanceValues.referenceIndex indexed]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type frameLocation)
  code : Code compiled.indexed function inputs.scope captured.administrative
  compilation : code.compilation = GeneralizedLocalLambdaCompilation.context inputs packet.original.emission.prepared
  active : code.active = packet.original.emission.prepared.substitution
  lowered : code.lowered = packet.original.lowered
  codeId : code.id = inputs.initializer
  policy : code.policy = GeneralizedLocalLambdaCompilation.policy inputs packet.original.emission.prepared packet.fuel
  lowerBody : code.lowerBody = GeneralizedLocalLambdaCompilation.lowerBody inputs packet.original.emission.prepared
  fuel : code.fuel = packet.fuel
  descriptorId : code.descriptor.id = indexed.descriptor.id
  certificate : HEq code.receipt packet.certificate
  view : code.view = packet.original.emission.prepared.source
  reasons : code.reasonAt = inputs.reasonAt
  source : function.source = packet.original.emission.prepared.source
  rawTyped : RuntimeValueHasType world (CallableIndexedLambdaValues.value code captured.embedding origin.native actual)
    candidate.type compiled.indexed.layouts.definitions
  ownership : LocalIdentityOwnership function.source
  issuer : GeneralizedLocalDiagnosticIssuer.Receipt compiled.indexed inputs
  unique : NodeOccurrencesUnique function.source

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure}

def Materialization.extend (material : Materialization compiled mapping world function)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Materialization compiled futureMapping futureWorld function :=
  { material with captured := material.captured.extend maps worlds
                  rawTyped := material.rawTyped.weaken worlds }

theorem Materialization.frame_reference (material : Materialization compiled mapping world function) :
    material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type material.frameLocation) := by
  simpa only [Code.referenceIndex, material.compilation, GeneralizedLocalInstanceValues.referenceIndex]
    using material.frameReference

theorem Materialization.source_receipt (material : Materialization compiled mapping world function) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      material.code.compilation.owner material.code.active function.source :=
  GeneralizedLocalMaterializedCode.source_receipt material.indexed material.code
    material.compilation material.active material.source

theorem Materialization.native_type (material : Materialization compiled mapping world function) :
    material.candidate.type = CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore := by
  have same := GeneralizedLocalMaterializedCode.value_eq material.indexed material.code material.lowered
    material.policy material.codeId
    material.captured.embedding material.origin.native material.actual
  have shape := Value.closure.inj (Value.pair.inj (Value.pair.inj same).1).2
  have result := (Ty.sum.inj shape.2.1).2
  rw [shape.1, result]
  exact material.indexed.nativeType

/-- The compiler-selected read wrapper and the captured reference remain
available after the read has returned and the caller has changed. -/
structure View (material : Materialization compiled mapping world function) where
  owner : SourceCoreLocalPolymorphism.Key
  active : TypeSystem.Substitution
  source : TypedSource
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  original : SourceCoreBasic.LoweredExpr
  lowered : SourceCoreBasic.LoweredExpr
  accepted : SourceCoreCallableIndexedAncestry.lowerView compiled.indexed.ancestry owner active source scope
    expression original = .ok lowered
  id : Word
  referenceIndex : Nat
  emitted : lowered.expression = SourceCoreCallableIndexedAncestry.viewLower compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore id material.code.descriptor.id
    referenceIndex original.expression
  callerNative : NativeFrame
  callerGhost : GhostFrame
  caller : MetadataState
  carried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    callerNative callerGhost (some caller)
  recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
    material.origin.ghost caller material.origin.metadata id material.code.descriptor.id
  initializer : material.descriptor.initializer = recipe.read.entry.view.principal.initializer
  scheme : material.descriptor.binder.scheme = recipe.read.binder.scheme
  actualType : material.actualType = recipe.read.node.rawType
  embedding : Renaming
  environment : Environment
  location : Core.Location
  reference : environment[embedding referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)
  lexicalReference : material.captured.canonical[material.code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location)

theorem View.materialized_pair {material : Materialization compiled mapping world function} (view : View material) :
    CallableAppliedDynamicSourceMaterialization.Pair compiled.indexed.ancestry.graph.inputs
      (.appliedView view.id material.code.descriptor.id view.callerGhost material.origin.ghost)
      (view.recipe.read.after material.origin.metadata) function.source := by
  have captures : Dynamic.GeneralizedClosureCaptures material.descriptor.definitionContext material.descriptor.source
      material.descriptor.captured material.descriptor.binder view.recipe.read.entry.view.principal.initializer
      material.descriptor := by
    rw [← view.initializer]
    exact material.sourceCaptures
  have result := material.origin.materialize view.recipe captures material.descriptorUnique
    material.instantiation view.scheme view.actualType
  simpa only [← material.materialized] using result.1

def View.native {material : Materialization compiled mapping world function} (view : View material) : Value :=
  GeneralizedLocalReadView.value compiled.indexed.ancestry.layout.frame
    material.code.receipt.parameterCore material.code.receipt.resultCore view.id material.code.descriptor.id
    view.referenceIndex view.embedding view.callerNative (.inLeft .word .unit)
    (.closure material.code.receipt.parameterCore (LanguageResult.resultType material.code.receipt.resultCore)
      (material.code.body.rename material.captured.embedding.lift.lift)
      (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual))
    view.environment

def View.extend {material : Materialization compiled mapping world function} (view : View material)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    View (material.extend maps worlds) :=
  { view with }

inductive Association (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | viewed {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
      (view : View material)
      (typed : RuntimeValueHasType world view.native
        (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association compiled mapping world function view.native material.code.receipt.loweredParameters
        material.code.receipt.parameterCore material.code.receipt.resultCore

variable {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def Association.AtFrame
    (member : Association compiled mapping world function native bindings parameter result)
    (location : Core.Location) : Prop :=
  match member with
  | .viewed _ view _ => view.location = location

theorem Association.projection
    (member : Association compiled mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project (FunctionValues.sourceType function) =
      .ok (CallableContract.functionType parameter result) := by
  cases member with
  | viewed material _ _ => exact material.code.projection

theorem Association.runtime_hasType
    (member : Association compiled mapping world function native bindings parameter result) :
    RuntimeValueHasType world native (CallableContract.functionType parameter result) compiled.indexed.layouts.definitions := by
  cases member with
  | viewed _ _ typed => exact typed

def Association.extend
    (member : Association compiled mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association compiled futureMapping futureWorld function native bindings parameter result := by
  cases member with
  | viewed material view typed =>
    exact .viewed (material.extend maps worlds) (view.extend maps worlds) (typed.weaken worlds)

theorem Association.stage_origin
    (member : Association compiled mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | viewed material view _ =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    have sourceReceipt := material.source_receipt
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at sourceReceipt
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted material.code.descriptor
      sourceReceipt material.code.viewOfSource material.unique material.code.found
      (material.code.form.trans material.code.sourceForm) _

theorem Association.observation
    (member : Association compiled mapping world function native bindings parameter result)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.Observation compiled.compatible.checked.catalog registry identities
      (CallableContract.functionType parameter result) (.closure function) native := by
  cases member with
  | viewed _ _ _ => exact .contractedAnonymous _ _ _ _ _ profile

theorem Association.source_binders
    (member : Association compiled mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | viewed material _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) material.code)).symm

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
/-! The actual materialized closure enters its emitted body through the retained
lexical snapshot, the read recipe, the manifest, and the marked parameter fold.
Every source cell uses the same relation throughout the prefix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedLambdaEntryPrefix (parameters prefix_accepted copies_accepted bodyEmbedding body_respects)
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open GeneralizedLocalDescriptorOrigin

private theorem body_agrees {canonical actual : Environment} {embedding : Renaming}
    (agrees : EnvironmentsAgree embedding canonical actual) (argument lexical saved : Value) :
    EnvironmentsAgree (bodyEmbedding embedding) (argument :: canonical)
      (.unit :: saved :: argument :: lexical :: actual) := by
  intro index value found
  cases index with
  | zero => exact found
  | succ index => exact agrees found

private theorem reference_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Core.Context} {index location : Nat} {type : Ty}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some (.cellRef type location)) : world[location]? = some type := by
  have atType : context[index]? = some (.cell type) := by
    rw [← typed.type_tags]
    simp [List.getElem?_map, found, Value.type]
  obtain ⟨value, selected, related⟩ := typed.lookup atType
  have same := Option.some.inj (selected.symm.trans found)
  subst value
  cases related with | cellRef typed => exact typed

structure Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    (registry : SourceCoreRawMetadata.Registry)
    (cells : GenericHeap.CellModel prepared.layouts.definitions)
    (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location)
    (callerNative : NativeFrame) (callerGhost : GhostFrame) (caller : MetadataState) (id : Word)
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.appliedView id code.descriptor.id callerGhost origin.ghost) (some (recipe.read.after origin.metadata))
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CellAwareLambdaViewPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length
    location next values functions registry cells function inputs.context scope code.receipt.loweredParameters
    arguments before (store.set location (encode prepared.ancestry.layout.frame next)) mapping world
    captured.administrative actualContext actual embedding code.receipt.copiedBody code.receipt.body
  wrap : ∀ {result bodyStore}, Evaluates entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) result bodyStore →
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame origin.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result
      (bodyStore.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
  unwrap : ∀ {result finalStore},
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame origin.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore →
    ∃ bodyStore, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))
  unmapped : location ∉ mapping
  referenceTyped : world[location]? = some prepared.ancestry.layout.frame.type
  currentRead : store.read? location = some (encode prepared.ancestry.layout.frame
    (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))

namespace Stateful

theorem entry_exists_with_spine_of_input_ids {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope captured.administrative viewRelation) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (inputIds : function.source.inputs.map TypedBinder.id = code.view.inputs.map TypedBinder.id)
    (copiedIds : ∀ id, (SourceSemantics.CaptureBinders.copiedBinder? function.source id).isSome =
      (SourceSemantics.CaptureBinders.copiedBinder? code.view id).isSome)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel prepared.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame cells)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
    (unmapped : location ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before,
      store.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
          (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))), captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer location
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe,
      ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  let layout := prepared.ancestry.layout.frame
  let argument := DataPatternValues.packValues nativeArguments
  let current := SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative
  let saved := encode layout current
  let lexicalValue := encode layout origin.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native current
  have registered := CallableIndexedAmbient.frame_registered prepared
  have nextHistory := GeneralizedLocalCallPrefix.applied_history origin callerCarried recipe
  have refTyped := reference_typed captured.represented.runtime_hasTypes reference
  have written : store.write? location (encode layout next) = some (store.set location (encode layout next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  have installedHeaps := heaps.write_administrative
    (fun found => unmapped (List.mem_of_getElem? found)) refTyped
    (encode_runtime_typed world registered next) written
  have installedRead := Store.write?_reads_written written
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨manifestDescriptor, fields, emitted⟩ := CallableIndexedLambdaManifest.of_hook hook
  let actual := .unit :: saved :: argument :: lexicalValue :: capturedActual
  have actualLayout : EnvironmentsAgree (bodyEmbedding captured.embedding) (argument :: captured.canonical) actual :=
    body_agrees captured.agrees argument lexicalValue saved
  have actualTyped : RuntimeEnvironmentHasTypes world actual
      (.unit :: layout.type :: SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) ::
        layout.type :: captured.actualContext) prepared.layouts.definitions :=
    .cons .unit (.cons (encode_runtime_typed world registered current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented)
        (.cons (encode_runtime_typed world registered origin.native) captured.typed)))
  obtain ⟨manifest, manifestTyped, manifestAgreement⟩ := CallableIndexedLambdaManifest.agreement
    captured.represented actualLayout manifestDescriptor fields code.receipt.copiedBody
      (store.set location (encode layout next))
  obtain ⟨entry, added, copiedCanonical, prefixLength, canonicalEq, slots, transition⟩ :=
    CellAwareLambdaViewPrefix.Stateful.entry_of_accepted_with_spine_of_copies functions ordinaryCells
      code.allocationError protocol producer transport rebinds inputIds copiedIds (prefix_accepted code)
      (copies_accepted code) (parameters code) inputs.kinds inputs.extended
      rfl registered represented captured.represented installedHeaps locals
      (GenericExpressionMeaning.agree_prefix actualLayout manifest) (body_respects captured.respects _ layout.type _)
      (.cons manifestTyped actualTyped) (inputs.referenceIndex ▸ reference) installedRead unmapped initial readyAt
  have agreement : ContinuationAgreement actual (store.set location (encode layout next))
      (code.receipt.rawBody.rename (bodyEmbedding captured.embedding)) entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) := by
    rw [emitted]
    exact manifestAgreement.trans entry.agreement
  have frame := GeneralizedLocalCallFrame.agreement origin captured code callerCarried recipe
    (argument := argument) reference read
  exact ⟨⟨next, nextHistory, _, _, _, entry,
    fun evaluated => frame.1 (agreement.wrap evaluated),
    fun evaluated => by
      obtain ⟨bodyStore, bodyEval, finalEq⟩ := frame.2 evaluated
      exact ⟨bodyStore, agreement.unwrap bodyEval, finalEq⟩,
    unmapped, refTyped, read⟩, added, copiedCanonical, prefixLength, canonicalEq, slots, transition⟩

/-- Compatibility with full-table view evidence. -/
theorem entry_exists_with_spine {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} (origin : Origin prepared descriptor binding lexical)
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel prepared.layouts.definitions}
    (ordinaryCells : GenericHeap.OrdinaryCells
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) cells)
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog values.checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame cells)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world code.receipt.loweredParameters arguments nativeArguments)
    {before : Dynamic.Heap} {store : Store} {location : Location}
    {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
    (callerCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
      callerNative callerGhost (some caller))
    (recipe : CallableAppliedViewProvenance.Recipe prepared.ancestry.graph.inputs callerGhost
      origin.ghost caller origin.metadata id code.descriptor.id)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)))
    (unmapped : location ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before,
      store.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
          (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))), captured.canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer location
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id origin.native
        (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : Entry origin captured code inputs functions registry cells arguments nativeArguments before store
      location callerNative callerGhost caller id recipe,
      ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  exact entry_exists_with_spine_of_input_ids origin captured code inputs
    (congrArg (List.map TypedBinder.id) code.viewOfSource.inputs)
    (fun id => by rw [LambdaMetadataViews.MetadataView.copiedBinder code.viewOfSource]) functions ordinaryCells
    protocol producer transport rebinds represented callerCarried recipe heaps locals reference read unmapped initial
    readyAt

end Stateful
end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
/-! The live public authority pool supplies the actual materialized-call entry.
The transient read frame is replaced by the child frame certified by the real
read recipe. Marked parameters retain the same pool and mixed cell relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedParameterMeaning
open GeneralizedLocalDescriptorOrigin

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} (origin : Origin compiled.indexed descriptor binding lexical)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) cells)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerState : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {callerNative : NativeFrame} {callerGhost : GhostFrame} {caller : MetadataState} {id : Word}
  (callerCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    callerNative callerGhost (some caller))
  (recipe : CallableAppliedViewProvenance.Recipe compiled.indexed.ancestry.graph.inputs callerGhost
    origin.ghost caller origin.metadata id code.descriptor.id)

include ordinaryCells represented callerCarried in
/-- The selected row is allowed to contain the genuine transient read frame.
Only the installed child must be stable before marked allocation begins. -/
theorem parameters_with_state
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative))) :
    ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
      origin captured code inputs functions registry cells arguments nativeArguments before store
      owner.key.frameLocation callerNative callerGhost caller id recipe,
    ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
      entry.entry.canonical = added ++ copied ∧
      (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
      ProtectedStateTransition.Transition (protocol headers keys) callerState
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
  have physical : (callerState.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (callerState.rows owner.position).frame_eq
  have unmapped : owner.key.frameLocation ∉ mapping := by
    simpa only [physical] using (callerState.rows owner.position).authority.unmapped
  have nextHistory := GeneralizedLocalCallPrefix.applied_history origin callerCarried recipe
  let next := SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    code.descriptor.id origin.native (SourceCoreCallableIndexedDispatch.readFrame id code.descriptor.id callerNative)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) headers keys cells
  let installed := install callerState owner.position (.stable nextHistory)
  let initial : State headers keys ⟨scope, mapping, world, before,
      store.set owner.key.frameLocation (encode compiled.indexed.ancestry.layout.frame next), captured.canonical⟩ := installed
  have readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer owner.key.frameLocation next := by
    intro index reached read
    exact CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position read nextHistory
  obtain ⟨entry, added, copied, length, spine, slots, reached, parameterRelated⟩ :=
    GeneralizedLocalBodyEntry.Stateful.entry_exists_with_spine (values := .initial compiled.compatible.checked)
      origin captured code inputs functions ordinaryCells (protocol headers keys) producer
      (administrativeTransport headers keys) (rebinds headers keys) represented callerCarried recipe
      heaps locals reference read unmapped initial readyAt
  have installedRelated : Relates callerState initial := install_related callerState owner.position (.stable nextHistory)
  exact ⟨entry, added, copied, length, spine, slots, reached, installedRelated.trans parameterRelated⟩

/-- Original Source typing and the actual allocation produce body admission.
No source type is recovered from an erased native payload type. -/
theorem source_admission
    (entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
      origin captured code inputs functions registry cells arguments nativeArguments before store
      owner.key.frameLocation callerNative callerGhost caller id recipe)
    (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types) :
    Dynamic.SourceRuntimeValid program inputs.context function.source ∧
      function.evidence.Covers inputs.context ∧
      Dynamic.HeapWellTyped inputs.context entry.entry.heap ∧
      Dynamic.EnvironmentAgrees entry.entry.heap inputs.context.locals entry.entry.environment ∧
      ∃ finalContext facts,
        StatementsHaveType function.source { returnType := function.resultType } inputs.context function.body finalContext facts ∧
        BodyCompletes function.resultType facts := by
  have runtime := CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have actualArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have reached := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.entry.copy)
    (actualArguments.mono entry.entry.copy.metadata_extends) entry.entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have typed := reached.transportClosed fields.signatures frame.code.closed (fields.targetClosed frame.code.closed)
    frame.code.variables_closed (fields.targetResidualVariablesOpen frame.code.residual_variables_open)
  exact ⟨runtime.1, runtime.2, typed, entry.entry.locals,
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOwnedBodyEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
/-! A materialized read temporarily installs a read frame. Replacing that
frame by the actual child history recovers stable rows without pretending the
intermediate read frame was already stable. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {index reachedIndex : ProtectedStateTransition.Index}

def StableAway (saved : State headers keys index) (selected : Fin keys.length) : Prop :=
  ∀ i : Fin keys.length, keys[i.val].frameLocation ≠ keys[selected.val].frameLocation →
    ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (saved.rows i).authority.current (saved.rows i).authority.ghost metadata

/-- Actual read installation leaves all physically different rows stable. -/
theorem away_after_install (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableRows saved) {native : NativeFrame} {ghost : GhostFrame}
    (current : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost) :
    StableAway (install saved selected current) selected := by
  intro i different
  have native := CallableIndexedAuthorityPool.Pool.install_current saved selected i current
  have ghost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i current
  change ((install saved selected current).rows i).authority.current = _ at native
  change ((install saved selected current).rows i).authority.ghost = _ at ghost
  obtain ⟨metadata, history⟩ := stable i
  refine ⟨metadata, ?_⟩
  erw [native, ghost, if_neg different, if_neg different]
  exact history

/-- The child replaces every alias of its physical frame, while other rows
retain their actual histories from before the read. -/
theorem install_rows (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableAway saved selected) {next : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (install saved selected (.stable history)) := by
  intro i
  have current := CallableIndexedAuthorityPool.Pool.install_current saved selected i (.stable history)
  have actualGhost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i (.stable history)
  change ((install saved selected (.stable history)).rows i).authority.current = _ at current
  change ((install saved selected (.stable history)).rows i).authority.ghost = _ at actualGhost
  by_cases same : keys[i.val].frameLocation = keys[selected.val].frameLocation
  · refine ⟨metadata, ?_⟩
    erw [current, actualGhost, if_pos same, if_pos same]
    exact history
  · obtain ⟨oldMetadata, oldHistory⟩ := stable i same
    refine ⟨oldMetadata, ?_⟩
    erw [current, actualGhost, if_neg same, if_neg same]
    exact oldHistory

theorem after_parameters (saved : State headers keys index) (reached : State headers keys reachedIndex)
    (selected : Fin keys.length) (stable : StableAway saved selected)
    {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata)
    (frame : AdministrativePreserved index.mapping
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reachedIndex.mapping reachedIndex.store) :
    StableRows reached :=
  StableRows.after_administrative (install saved selected (.stable history)) reached
    (install_rows saved selected stable history) frame

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalParameterAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedCall
/-! The outer read wrapper and inner lexical wrapper compose around the same
real frame cell. A completed body retains all other writes and allocations,
while both successful and failed calls restore the current caller's frame. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {material : Materialization compiled mapping world function}

def View.transient (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.readFrame view.id material.code.descriptor.id view.callerNative

def View.selected (view : View material) : NativeFrame :=
  SourceCoreCallableIndexedDispatch.selectedFrame compiled.indexed.ancestry.graph.table
    material.code.descriptor.id material.origin.native view.transient

def View.bodyEnvironment (view : View material) (argument : Value) : Environment :=
  .unit :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient :: argument ::
    SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual

def View.entry (view : View material) (argument : Value) : Environment :=
  argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative ::
    CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual :: view.environment

def View.body (view : View material) : Expr :=
  (SourceCoreCallableIndexedAncestry.viewBody compiled.indexed.ancestry.layout.frame view.id material.code.descriptor.id
    view.referenceIndex).rename view.embedding.lift.lift.lift

theorem View.agreement (view : View material) {argument saved : Value} {store : Store}
    (current : store.read? view.location = some saved) :
    let selected := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.selected
    (∀ {output finalStore},
      Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
        (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
        output finalStore →
      Evaluates (view.entry argument) store view.body output (finalStore.set view.location saved)) ∧
    (∀ {output finalStore}, Evaluates (view.entry argument) store view.body output finalStore →
      ∃ bodyStore,
        Evaluates (view.bodyEnvironment argument) (store.set view.location selected)
          (material.code.receipt.rawBody.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding material.captured.embedding))
          output bodyStore ∧ finalStore = bodyStore.set view.location saved) := by
  let transient := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.transient
  have bound : view.location < store.length := (List.getElem?_eq_some_iff.mp current).choose
  have installed : Store.read? (store.set view.location transient) view.location = some transient :=
    Store.write?_reads_written (Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩)
  have inner := GeneralizedLocalCallFrame.agreement material.origin material.captured material.code
    view.carried view.recipe view.lexicalReference installed (argument := argument)
  have outer := GeneralizedLocalReadView.agreement view.reference current
    (parameter := material.code.receipt.parameterCore) (result := material.code.receipt.resultCore)
    (id := view.id) (target := material.code.descriptor.id) (caller := view.callerNative)
    (identity := .inLeft .word .unit)
    (innerBody := material.code.body.rename material.captured.embedding.lift.lift)
    (innerEnvironment := SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame material.origin.native :: material.actual)
    (argument := argument)
  constructor
  · intro output finalStore evaluated
    have bodyEvaluation := inner.1 (by simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using evaluated)
    simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using outer.1 bodyEvaluation
  · intro output finalStore evaluated
    obtain ⟨innerStore, innerEvaluation, outerEq⟩ := outer.2 evaluated
    obtain ⟨bodyStore, bodyEvaluation, innerEq⟩ := inner.2 innerEvaluation
    refine ⟨bodyStore, ?_, ?_⟩
    · simpa only [List.set_set, View.bodyEnvironment, View.selected, View.transient, View.entry, View.body, CallableIndexedLambdaValues.value] using bodyEvaluation
    · simpa only [innerEq, List.set_set] using outerEq

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
/-! A materialized instance retains its actual compiler callback. Terminal
body certificates are extracted from that accepted action, with the actual
metadata view and full Source parameter context kept explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalLambdaCompilation (representation binder)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)

def policy : SourceCoreLoops.Policy :=
  let actual := representation material.inputs material.packet.original.emission.prepared
  { actual.loopsWithSourceCells actual.expressions.sourceCells
      material.packet.original.emission.prepared.caller.function.solvedRequirements
      material.inputs.assignments material.inputs.diagnostics material.inputs.current.owner
      (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := binder material.inputs material.packet.original.emission.prepared }

theorem callback : material.code.lowerBody
    (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy (policy material) := by
  rw (occs := .pos [1]) [material.lowerBody]
  rfl

theorem expression_reader : (policy material).lowerExpression =
    FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

theorem statement_reader : (policy material).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

/-- The original accepted lambda body supplies its terminal receipt. Neither
recompilation of a different Source view nor a body execution law is required. -/
theorem terminal_receipt {expression : ExpressionId}
    (terminal : Terminal material.code.view expression function.body) :
    Nonempty (Receipt (policy material) material.code.fuel material.code.view
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      expression function.body material.code.receipt.resultCore material.code.reasonAt
      material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body) := by
  exact CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (statement_reader material) terminal
    (CallableIndexedLambdaSemanticInvocation.loops_accepted
      (values := .initial compiled.compatible.checked) material.code (policy material) (callback material))

/-- Complete Source lambda typing supplies the actual parameter context.
The real global layout fixes the native reference slot independently of types. -/
theorem entry_context {program : Program} (frame : Dynamic.ClosureFrame program function)
    (ownership : LocalIdentityOwnership function.source)
:
    Nonempty (CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code) := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) material.code ownership contains form
  have reference : material.code.referenceIndex =
      material.inputs.scope.length + 1 + compiled.indexed.base.globals.length := by
    unfold CallableIndexedLambdaValues.Code.referenceIndex
    rw [material.compilation]
    change material.inputs.scope.length + material.inputs.current.administrativePrefix + material.inputs.current.globals.length = _
    rw [material.indexed.administrativePrefix, material.indexed.globals]
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique extended bodyTyped completes =>
    exact ⟨⟨_, _, extended, kinds, reference⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
/-! An ordinary local read inside an actually materialized lambda obtains its
static certificate from that lambda's contextual compiler. Finite metadata
checks select the ordinary branch; no expression or body law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalInstanceCompilation (Inputs)

abbrev Site (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryReadSite.Observations inputs.locals inputs.current.owner source id

abbrev site? (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryReadSite.observations? inputs.locals inputs.current.owner source id

private theorem contextual {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (parent : Option SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner parent source id = .ok source := by
  simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure,
    site.form, site.ordinary, Bool.false_eq_true, ↓reduceIte]

private theorem special {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    GeneralizedLocalLambdaCompilation.special inputs prepared fuel
      (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.requirements, site.coercions]
    rfl
  have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
      (GeneralizedLocalLambdaCompilation.representation inputs prepared).expressions.projectType
      prepared.caller (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) = .ok none := by
    simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, ordinary,
      site.requirements, site.coercions]
  have noInitializer : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.initializer = id)) = none :=
    site.notInitializer
  have noGeneralized : inputs.locals.bindings.any (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.binder.id = site.binder)) = false :=
    site.ordinary
  unfold GeneralizedLocalLambdaCompilation.special
  change (do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner (some prepared) source id
    _) = .ok none
  rw [contextual site]
  simp only [bind, Except.bind, pure, Except.pure, site.found,
    noInitializer, Option.filter_none]
  rw [evidence]
  simp only [site.form, noGeneralized, Bool.false_eq_true, ↓reduceIte]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  {id : ExpressionId} (site : Site material.inputs material.code.view id)

include site in
/-- The actual prepared representation supplies both the read callback and the
ordinary branch of the contextual override at this exact Source occurrence. -/
theorem policy_on {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word} :
    CompatibleExpressionProducts.PolicyOn material.code.policy material.code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view scope reasonAt (fun child => child = id) := by
  constructor
  · intro child same _ childCompiler budget
    subst child
    rw [material.policy, material.compilation]
    exact special site material.packet.original.emission.prepared material.packet.fuel childCompiler budget scope reasonAt
  · intro child same _
    subst child
    rw [material.policy]
    change (do
      let source ← SourceCoreGeneralFunctions.contextualSource material.inputs.program material.inputs.current.plan
        material.inputs.locals material.inputs.current.owner (some material.packet.original.emission.prepared)
        material.code.view id
      _) = _
    rw [contextual site]
    simp only [bind, Except.bind]
    unfold GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl

theorem of_accepted {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    (typed : ExpressionHasType material.code.view context id site.node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view context material.code.compilation.solvedRequirements
      reasonAt scope id lowered := by
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations
    (policy_on material site) ?_ ?_ (.read site.found site.form) rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have nodeEq := Option.some.inj (site.found.symm.trans found)
    subst node
    simp [site.form, ExpressionForm.references] at member
  · intro child node same _ found
    subst child
    have nodeEq := Option.some.inj (site.found.symm.trans found)
    exact nodeEq ▸ site.coercions

/-- The actual reference form selects the read leaf of the finite compiler
certificate, so body execution needs no generic child or literal law. -/
theorem lowered_read {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    (typed : ExpressionHasType material.code.view context id site.node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      material.code.view context reasonAt scope id lowered := by
  obtain ⟨tree, sites⟩ := of_accepted material site unique declarations typed accepted
  clear sites
  cases tree with
  | read receipt => exact receipt
  | literal receipt =>
    obtain ⟨node, found, literal⟩ := receipt
    have same := Option.some.inj (found.symm.trans site.found)
    subst node
    generalize lowered.type = nativeType at literal
    generalize lowered.expression = nativeCode at literal
    cases literal with
    | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
    | resolvedWord form _ | resolvedInteger form _ =>
      rw [site.form] at form
      cases form
  | group metadata form _ _ _ | pair metadata form _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans site.found)
    cases same
    rw [site.form] at form
    cases form

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate
/-! A finite ordinary expression tree inside an actually materialized lambda obtains its
static certificate from that lambda's contextual compiler. Finite metadata
checks select the ordinary branch; no expression or body law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalInstanceCompilation (Inputs)

abbrev Site (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryExpressionProfile.Site inputs.locals inputs.current.owner source id

abbrev site? (inputs : Inputs) (source : TypedSource) (id : ExpressionId) :=
  GeneralizedLocalOrdinaryExpressionProfile.site? inputs.locals inputs.current.owner source id

private theorem contextual {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (parent : Option SourceCoreLocalEvidence.Prepared) :
    SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner parent source id = .ok source := by
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]
  | read name binder =>
    have ordinary := site.ordinary name binder shape
    simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure,
      shape, ordinary, Bool.false_eq_true, ↓reduceIte]
  | group inner | pair left right => simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]

private theorem special {inputs : Inputs} {source : TypedSource} {id : ExpressionId}
    (site : Site inputs source id) (prepared : SourceCoreLocalEvidence.Prepared) (fuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    GeneralizedLocalLambdaCompilation.special inputs prepared fuel
      (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some site.node.requirements := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.coercions]
    change (if site.node.requirements.length < 0 then none else
      if site.node.requirements = site.node.requirements.take (site.node.requirements.length - 0) ++ [] then
        some (site.node.requirements.take (site.node.requirements.length - 0)) else none) = some site.node.requirements
    simp
  have evidence : SourceCoreEvidence.lowerWithProjector inputs.program
      (GeneralizedLocalLambdaCompilation.representation inputs prepared).expressions.projectType
      prepared.caller (GeneralizedLocalLambdaCompilation.context inputs prepared) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy inputs.native prepared.substitution) = .ok none := by
    have supported := site.form
    have requirements := site.requirements
    generalize shape : site.node.form = form at supported requirements
    cases supported with
    | literal atomic =>
      cases atomic with
      | integer literal resolution =>
        simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, site.coercions]
      | unit | bool name value | word literal =>
        simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
    | read name binder | group inner | pair left right =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  have noInitializer : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.initializer = id)) = none :=
    site.notInitializer
  unfold GeneralizedLocalLambdaCompilation.special
  change (do
    let source ← SourceCoreGeneralFunctions.contextualSource inputs.program inputs.current.plan inputs.locals
      inputs.current.owner (some prepared) source id
    _) = .ok none
  rw [contextual site]
  simp only [bind, Except.bind, pure, Except.pure, site.found, noInitializer, Option.filter_none]
  rw [evidence]
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp
  | read name binder =>
    simp only
    have noGeneralized : inputs.locals.bindings.any (fun binding =>
        decide (binding.caller = (GeneralizedLocalLambdaCompilation.context inputs prepared).owner ∧ binding.binder.id = binder)) = false :=
      site.ordinary name binder shape
    rw [noGeneralized]
    rfl
  | group inner | pair left right => simp

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  {id : ExpressionId} (site : Site material.inputs material.code.view id)

include site in
/-- The actual prepared representation supplies both the read callback and the
ordinary branch of the contextual override at this exact Source occurrence. -/
theorem policy_on {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word} :
    CompatibleExpressionProducts.PolicyOn material.code.policy material.code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view scope reasonAt (fun child => child = id) := by
  constructor
  · intro child same _ childCompiler budget
    subst child
    rw [material.policy, material.compilation]
    exact special site material.packet.original.emission.prepared material.packet.fuel childCompiler budget scope reasonAt
  · intro child same _
    subst child
    rw [material.policy]
    change (do
      let source ← SourceCoreGeneralFunctions.contextualSource material.inputs.program material.inputs.current.plan
        material.inputs.locals material.inputs.current.owner (some material.packet.original.emission.prepared)
        material.code.view id
      _) = _
    rw [contextual site]
    simp only [bind, Except.bind]
    unfold GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl
  · rw [material.policy]
    unfold GeneralizedLocalLambdaCompilation.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl

theorem of_accepted {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view id)
    (unique : NodeOccurrencesUnique material.code.view)
    (declarations : CompatibleExpressionReads.ScopeDeclarations material.code.view scope context)
    {node : ExpressionNode} (found : material.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType material.code.view context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody fuel
      material.code.compilation material.code.view scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view context material.code.compilation.solvedRequirements
      reasonAt scope id lowered := by
  obtain ⟨site⟩ := tree.site
  let allowed := GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view
  have policies : CompatibleExpressionProducts.PolicyOn material.code.policy material.code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) material.code.view scope reasonAt allowed := by
    constructor
    · intro child admitted shape compiler budget
      obtain ⟨childSite⟩ := admitted.site
      exact (policy_on material childSite (scope := scope) (reasonAt := reasonAt)).special child rfl shape compiler budget
    · intro child admitted shape
      obtain ⟨childSite⟩ := admitted.site
      exact (policy_on material childSite (scope := scope) (reasonAt := reasonAt)).read child rfl shape
    · exact (policy_on material site (scope := scope) (reasonAt := reasonAt)).lower
    · exact (policy_on material site (scope := scope) (reasonAt := reasonAt)).leaf
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations
    policies (fun admitted found member => admitted.children found member) ?_ tree.syntax tree found typed accepted
  intro child childNode admitted _ childFound
  obtain ⟨childSite⟩ := admitted.site
  exact Option.some.inj (childSite.found.symm.trans childFound) ▸ childSite.coercions

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedProvenance
/-! The real child compiler and retained issuer supply materialized body scope
and diagnostics. Original source identities survive the actual substitution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
open Core Frontend SourceInference GeneralHeap
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

/-- The instantiated body selects its own recursive Source scope from the
actual descriptor and compiler preparation, without a lexical History. -/
theorem Materialization.scope_at (material : Materialization compiled mapping world function) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan material.code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar material.code.active function) := by
  have receipt := material.source_receipt
  rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1] at receipt
  exact CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope material.code receipt material.unique

theorem Materialization.original_source (material : Materialization compiled mapping world function) :
    ∃ original : SourceSpecialization.SpecializedFunction,
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan material.inputs.current.owner = .ok original ∧
      material.descriptor.source = original.function.typedBody ∧
      function.source = original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution := by
  obtain ⟨original, selected, same, _active, source⟩ :=
    LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
  refine ⟨original, ?_, ?_, material.source.trans source⟩
  · simpa only [material.indexed.plan, ← material.indexed.owner] using selected
  · exact material.descriptorSource.trans (material.candidateSource.symm.trans same.symm)

private theorem reference_original {substitution : TypeSystem.Substitution} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId}
    (form : (node.applySubstitution substitution).form = .reference name (.local binder)) :
    node.form = .reference name (.local binder) := by
  cases original : node.form <;>
    simp_all [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution]
  rename_i originalName resolution
  cases resolution <;> simp_all [ReferenceResolution.applySubstitution]


/-- A body read uses its original issued token in the actual public receiving
inventory. No diagnostic premise is supplied by the caller of the body. -/
theorem Materialization.uninitialized (material : Materialization compiled mapping world function)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (material.code.reasonAt id) := by
  obtain ⟨original, selected, descriptorSource, source⟩ := material.original_source
  have unique : NodeOccurrencesUnique original.function.typedBody := descriptorSource ▸ material.descriptorUnique
  have contained : ContainsExpression
      (original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution) id node :=
    source ▸ lookupExpression?_sound found
  have nodeContained : ContainsNode
      (original.function.typedBody.applySubstitution material.packet.original.emission.prepared.substitution)
      (.expression id) (.expression node) := ⟨contained.1, congrArg NodeId.expression contained.2⟩
  obtain ⟨originalNode, originalContained, transformed⟩ :=
    FlexibleSubstitution.containsNode_of_applySubstitution nodeContained
  cases originalNode with
  | statement originalNode => cases transformed
  | expression originalNode =>
    have same : originalNode.applySubstitution material.packet.original.emission.prepared.substitution = node :=
      Node.expression.inj transformed
    have originalForm := reference_original (same.symm ▸ form)
    have originalContains : ContainsExpression original.function.typedBody id originalNode :=
      ⟨originalContained.1, NodeId.expression.inj originalContained.2⟩
    obtain ⟨issued, present, callback, own, ownFound⟩ := material.issuer
    obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
      CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
        selected unique originalContains originalForm ownFound
    apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
    apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
      (by simpa only [material.reasons, callback, token] using decoded)
    exact .readUninitialized location binder

/-- Every actual body leaf uses its original issued token. -/
theorem Materialization.body_uninitialized (material : Materialization compiled mapping world function)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (material.code.reasonAt id) :=
  material.uninitialized receiver found form location

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
/-! The materialized association retains the actual contextual binder compiler.
Its original Source frame and ordered argument row determine native arguments;
no count or raw type is recovered from a projected type alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation

private theorem binder_projection {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerBinder checked source scope binder = .ok type) :
    checked.catalog.project binder.scheme.body = .ok type := by
  apply CompatibleExpressionReads.projectType_of_accepted
  simp only [SourceCoreCompatibleDataExpressions.lowerBinder, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  exact accepted

private theorem parameter_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {representation : SourceCoreGeneralFunctions.Representation} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {policy : SourceCoreFunctions.Policy} {source : TypedSource} {scope finalScope : SourceCoreLocalCell.Scope}
    {parameters : List TypedBinder} {bindings : List CallableIndexedParameterCertificates.Binding}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (bindings, finalScope))
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals owner active)
    (ordinaryPolicy : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder checked)
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = []) :
    ∀ binding ∈ bindings, checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  have tree := FunctionCode.Parameters.of_accepted accepted
  clear accepted
  induction tree with
  | nil => simp
  | @cons scope finalScope parameter parameters type bindings head tail ih =>
    rw [binderPolicy, SourceCoreGeneralFunctions.contextualBinder,
      monomorphic parameter (by simp), List.isEmpty_nil, if_pos rfl, ordinaryPolicy] at head
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact binder_projection head
    · exact ih (fun binder h => monomorphic binder (List.mem_cons_of_mem _ h)) binding member

private theorem frame_monomorphic {program : Program} {function : Dynamic.Closure}
    (frame : Dynamic.ClosureFrame program function) :
    ∀ binder ∈ function.parameters, binder.scheme.quantified = [] := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique extended bodyTyped completes =>
    exact CallableIndexedOwnedLambdaBinderProjections.monomorphic extended

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem projected_bindings (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases member with
  | viewed material _ _ =>
    apply parameter_projections material.code.receipt.parametersCompiled
    · rw [material.policy]
      rfl
    · unfold GeneralizedLocalLambdaCompilation.representation
      rw [material.indexed.represented]
      rfl
    · exact frame_monomorphic frame

theorem parameter_core (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  have projections := projected_bindings member frame
  cases member with
  | viewed material _ _ =>
    apply CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack material.code profile projections
    have projector : material.code.policy.projectType =
        SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked := by
      rw [material.policy]
      change (GeneralizedLocalLambdaCompilation.representation material.inputs
        material.packet.original.emission.prepared).expressions.projectType = _
      unfold GeneralizedLocalLambdaCompilation.representation
      rw [material.indexed.represented]
      rfl
    have result := material.code.receipt.resultProjected
    rw [projector] at result
    exact CompatibleExpressionReads.projectType_of_accepted result

/-- The independent Source count fixes the packing ambiguity at zero and one.
Both raw and native ordered bundles then align with the actual binder list. -/
theorem arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    (member : Association compiled mapping world function native bindings parameter result)
    {program : Program} (frame : Dynamic.ClosureFrame program function)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (arity : sources.length = function.parameters.length)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes types = parameter) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values := by
  have bindingArity : sources.length = bindings.length := by
    have lengths := congrArg List.length member.source_binders
    simp only [List.length_map] at lengths
    exact arity.trans lengths.symm
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented bindingArity
    (sourceBundle.trans (congrArg TypeSystem.Ty.productMany member.source_binders).symm)
    (nativeBundle.trans (parameter_core member frame profile))

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAssociation
/-! An actual stored Snapshot carries the allocation body's Source view. The
real read and matching cumulative candidate recover Code and the existing
Materialization, including its accepted body and unchanged capture environment.
The native lexical context may be any closed context, not just a named entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {mapping : LocationMap} {world : StoreTyping}
  {caller : SourceCoreLocalPolymorphism.Key} {active : TypeSystem.Substitution} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem materialize_snapshot
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller active source scope id reason lowered)
    {descriptor : Dynamic.GeneralizedClosure} {native : Value}
    {frameLocation : Core.Location}
    (row : GeneralizedLocalAcceptedInstances.Snapshot compiled.indexed mapping world descriptor
      receipt.binding active frameLocation
      (GeneralizedLocalContextualMaterialization.Attachment descriptor receipt.binding active)
      receipt.candidate native)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source descriptor.captured
      descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply active)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = active ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding material.origin.native material.actual := by
  cases row with
  | retained packet indexed acceptedBody sameLexical owner instanceInitializer candidateSource candidateBinder attachment origin captured declarations ownership issuer frameReference typed runtimeTyped =>
    have initializerEq := initializer.trans instanceInitializer.symm
    obtain ⟨code, compilation, activeEq, _id, loweredEq, _policy, _lowerBody, _fuel, _descriptor, _certificate, codeView, reasons, valueEq⟩ :=
      GeneralizedLocalContextualMaterialization.code_at_read receipt instantiation sameScheme sameType
        attachment candidateSource packet indexed captures unique initializerEq captured typed profile origin.native
    have materializedUnique : NodeOccurrencesUnique
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)).source := by
      change ((descriptor.source.applySubstitution semantic).nodes.map Node.occurrenceId).Nodup
      change (descriptor.source.nodes.map Node.occurrenceId).Nodup at unique
      simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using unique
    let material : Materialization compiled mapping world
        (descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)) :=
      { descriptor := descriptor, binding := receipt.binding, lexical := active
        inputs := _, candidate := receipt.candidate, raw := _, packet := packet, indexed := indexed, body := acceptedBody
        sameLexical := sameLexical, owner := owner, initializer := instanceInitializer
        candidateSource := candidateSource, candidateBinder := candidateBinder, descriptorInitializer := initializer
        origin := origin, descriptorUnique := unique, sourceCaptures := captures, context := context, callerEvidence := callerEvidence
        produced := produced, actualType := actualType, requirements := requirements, semantic := semantic
        instantiation := instantiation, materialized := rfl, actual := _, captured := captured
        capturedDeclarations := GeneralizedLocalScopeDeclarations.materialized declarations semantic (produced ++ callerEvidence.applySubstitution semantic)
        frameLocation := frameLocation, frameReference := frameReference, code := code
        compilation := compilation, active := activeEq, lowered := loweredEq, codeId := _id, policy := _policy, lowerBody := _lowerBody,
        fuel := _fuel, descriptorId := _descriptor, certificate := _certificate, view := codeView, reasons := reasons,
        rawTyped := valueEq.symm ▸ runtimeTyped,
        ownership := FlexibleSubstitution.LocalIdentityOwnership.applySubstitution semantic ownership,
        issuer := issuer, unique := materializedUnique }
    exact ⟨material, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, valueEq.symm⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalContextualAssociation
end
