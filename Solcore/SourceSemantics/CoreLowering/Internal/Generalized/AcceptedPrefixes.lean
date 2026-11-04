import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.AcceptedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyReads

/-!
# Generalized locals: accepted prefixes

The accepted initializer, located rows, prefixes, allocation and reads of generalized locals.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
/-! The entire ordered initializer bundle is formed from real indexed packets.
No candidate body profile or future execution is required. Its full source
attachment and actual capture frame survive descriptor storage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalDescriptorOrigin (Origin)

/-- A candidate keeps its actual compiler packet and complete lexical key. -/
def IndexedRows {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs) (lexical : Substitution)
    (candidates : List Instance) (closures : List Core.Expr) : Prop :=
  ListRel (fun candidate raw => Nonempty (Sigma fun packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw =>
    { indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet // indexed.lexical = lexical })) candidates closures

structure Receipt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (inputs : Inputs)
    (binding : Binding) (active : Substitution) (lowered : SourceCoreBasic.LoweredExpr) where
  original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered
  rows : IndexedRows prepared inputs active (binding.atContext active) original.closures
  sources : ∀ candidate ∈ binding.atContext active, candidate.origin.source = binding.source
  binders : ∀ candidate ∈ binding.atContext active, candidate.origin.binder.id = binding.binder.id

/-- Old profiled bundles embed by retaining the identical packet at each position. -/
theorem of_profiled {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalInitializerPackets.Receipt prepared inputs binding active lowered) :
    Nonempty (Receipt prepared inputs binding active lowered) := by
  refine ⟨⟨receipt.original, ?_, receipt.sources, receipt.binders⟩⟩
  have rows := receipt.rows
  generalize binding.atContext active = candidates at rows ⊢
  generalize receipt.original.closures = closures at rows ⊢
  induction rows with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨⟨packet, indexed, _⟩⟩ := head
    exact .cons ⟨⟨packet, indexed⟩⟩ ih

private theorem indexed_type {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {candidate : Instance} {raw : Core.Expr}
    {packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw}
    (indexed : GeneralizedLocalLambdaGeneration.Indexed prepared packet)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context raw type definitions) : type = candidate.type := by
  rw [indexed.emitted] at typed
  cases typed with
  | pair tagged identifier =>
    cases identifier
    cases tagged with
    | pair marker function =>
      cases marker with
      | inLeft _ marker =>
        cases marker
        cases function with
        | letE snapshot closure =>
          cases closure
          exact indexed.nativeType.symm

private theorem rows_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {lexical : Substitution} {candidates : List Instance} {closures : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates closures)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context (ProductBundle.expression closures) type definitions) :
    type = ProductBundle.type (candidates.map (·.type)) ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions) candidates closures := by
  induction rows generalizing type with
  | nil => cases typed; exact ⟨rfl, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    obtain ⟨⟨packet, indexed, _lexical⟩⟩ := head
    cases tail with
    | nil =>
      have same := indexed_type indexed typed
      exact ⟨same, .cons (same ▸ typed) .nil⟩
    | cons next restRows =>
      cases typed with
      | pair left right =>
        have first := indexed_type indexed left
        obtain ⟨remainingType, remainingTyped⟩ := ih right
        exact ⟨by simp only [List.map_cons, ProductBundle.type, first, remainingType],
          .cons (first ▸ left) remainingTyped⟩

/-- Static typing of the actual emitted bundle recovers every row's exact
native type from its authentic snapshot-lambda header. -/
theorem Receipt.raw_typed {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {binding : Binding} {active : Substitution} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding active lowered)
    {context : Core.Context} {definitions : DataEnvironment} {type : Core.Ty}
    (typed : HasType context lowered.expression type definitions) :
    type = LanguageResult.resultType lowered.type ∧
      ListRel (fun candidate raw => HasType context raw candidate.type definitions)
        (binding.atContext active) receipt.original.closures := by
  rw [receipt.original.emitted] at typed
  have loweredType : lowered.type = binding.bundleType active :=
    congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
  rw [loweredType]
  cases typed with
  | inRight _ bundle =>
    obtain ⟨same, rows⟩ := rows_typed receipt.rows bundle
    exact ⟨by simpa only [Binding.bundleType, LanguageResult.resultType] using congrArg (Core.Ty.sum .word) same, rows⟩

private theorem bundle_evaluates {actual : Core.Environment} {store : Store} {embedding : Renaming}
    {expressions : List Core.Expr} {values : List Value}
    (rows : ProductBundle.Pointwise (fun expression value =>
      Evaluates actual store (expression.rename embedding) value store) expressions values) :
    Evaluates actual store ((ProductBundle.expression expressions).rename embedding)
      (ProductBundle.value values) store := by
  induction rows with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact head
    | cons next rest => exact .pair head ih

/-- Every row is formed from its accepted compiler packet and the same actual
capture environment. The recorded lexical key is the initializer's key. -/
theorem rows_form_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    {candidates : List Instance} {expressions : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates expressions)
    (sources : ∀ candidate ∈ candidates, candidate.origin.source = binding.source)
    (binders : ∀ candidate ∈ candidates, candidate.origin.binder.id = binding.binder.id)
    (sourceAttachment : Prop) (attached : sourceAttachment)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : ListRel (fun candidate raw => HasType
      (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions) candidates expressions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      ProductBundle.Pointwise (fun expression value =>
        Evaluates actual store (expression.rename captured.embedding) value store) expressions values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.RepresentsWith prepared mapping world
        function binding lexical sourceAttachment) candidates values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Snapshot prepared mapping world
        function binding lexical location sourceAttachment) candidates values := by
  induction rows with
  | nil => exact ⟨[], .nil, .nil, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    cases typed with
    | cons rawTyped restTyped =>
      obtain ⟨packet, indexed, sameLexical⟩ := head
      have sameIndex : GeneralizedLocalInstanceValues.referenceIndex indexed =
          SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope := rfl
      obtain ⟨evaluated, framed⟩ := GeneralizedLocalAcceptedInstances.formation_at_frame_with indexed sameLexical
        owner initializer (sources candidate (by simp)) (binders candidate (by simp))
        sourceAttachment attached origin captured declarations ownership issuer rawTyped stored (sameIndex ▸ reference) read
      obtain ⟨values, evaluations, representedRows, framedRows⟩ := ih (fun child member => sources child (List.mem_cons_of_mem _ member))
        (fun child member => binders child (List.mem_cons_of_mem _ member)) restTyped
      exact ⟨_, .cons evaluated evaluations, .cons ⟨location, framed⟩ representedRows, .cons framed framedRows⟩

theorem rows_form {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    {candidates : List Instance} {expressions : List Core.Expr}
    (rows : IndexedRows prepared inputs lexical candidates expressions)
    (sources : ∀ candidate ∈ candidates, candidate.origin.source = binding.source)
    (binders : ∀ candidate ∈ candidates, candidate.origin.binder.id = binding.binder.id)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : ListRel (fun candidate raw => HasType
      (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      raw candidate.type prepared.layouts.definitions) candidates expressions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      ProductBundle.Pointwise (fun expression value =>
        Evaluates actual store (expression.rename captured.embedding) value store) expressions values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Represents prepared mapping world
        function binding lexical) candidates values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Framed prepared mapping world
        function binding lexical location) candidates values := by
  exact rows_form_with rows sources binders (function.source = binding.source) descriptorSource owner initializer
    origin captured declarations ownership issuer typed stored reference read

/-- The production initializer produces the complete bundle in the original
store. Its Source attachment retains the real binding and captured metadata. -/
theorem formation_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.RepresentsWith prepared mapping world
        function binding lexical (sourceAttachment function binding lexical)) (binding.atContext lexical) values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Snapshot prepared mapping world
        function binding lexical location (sourceAttachment function binding lexical)) (binding.atContext lexical) values ∧
      GeneralizedLocalDescriptorHeap.Stored (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)
        mapping world function (ProductBundle.value values) lowered.type := by
  obtain ⟨values, evaluations, rows, frames⟩ := rows_form_with receipt.rows receipt.sources receipt.binders (sourceAttachment function binding lexical) attached owner initializer origin captured declarations ownership issuer
    (receipt.raw_typed typed).2 stored reference read
  refine ⟨values, ?_, rows, frames, ?_⟩
  · rw [receipt.original.emitted]
    exact .inRight (bundle_evaluates evaluations)
  · have payload : lowered.type = binding.bundleType lexical :=
      congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
    rw [payload]
    exact attachment.stored rows

theorem formation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Represents prepared mapping world
        function binding lexical) (binding.atContext lexical) values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Framed prepared mapping world
        function binding lexical location) (binding.atContext lexical) values ∧
      GeneralizedLocalDescriptorHeap.Stored (GeneralizedLocalAcceptedInstances.model prepared)
        mapping world function (ProductBundle.value values) lowered.type := by
  exact formation_with receipt (fun function binding _ => function.source = binding.source)
    descriptorSource owner initializer origin attachment captured declarations ownership issuer typed stored reference read

/-- General lexical creation uses the actual paired Source carried in every snapshot. -/
theorem formation_tracked {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding lexical lowered)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native)) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.RepresentsWith prepared mapping world
        function binding lexical True) (binding.atContext lexical) values ∧
      ProductBundle.Pointwise (GeneralizedLocalAcceptedInstances.Snapshot prepared mapping world
        function binding lexical location True) (binding.atContext lexical) values ∧
      GeneralizedLocalDescriptorHeap.Stored (GeneralizedLocalAcceptedInstances.trackedModel prepared)
        mapping world function (ProductBundle.value values) lowered.type := by
  exact formation_with receipt (fun _ _ _ => True) True.intro owner initializer origin attachment
    captured declarations ownership issuer typed stored reference read

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
/-! The new instance relation retains the exact frame across storage and reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism GeneralizedLocalAcceptedInstances GeneralizedLocalLocatedRows

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
  {location : Dynamic.Location} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

def Located.FramesWith (sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop) (located : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  ProductBundle.Pointwise (Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
    (binding.atContext lexical) located.values

variable {sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop}

theorem Located.FramesWith.transport
    {previous : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store}
    {next : Located (modelWith prepared sourceAttachment) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : Located.FramesWith sourceAttachment previous frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : Located.FramesWith sourceAttachment next frameLocation := by
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  change ProductBundle.Pointwise _ _ _ at frames
  generalize binding.atContext lexical = selected at frames ⊢
  generalize previous.values = payload at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend maps worlds) ih

theorem Located.preserves_snapshot
    (located : Located (modelWith prepared sourceAttachment) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : Located.FramesWith sourceAttachment located frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical) receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : prepared.base.locals.binding binding.caller binding.binder.id = .ok binding := located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨target, referenceAt, reference⟩ := environments.lookup_visible lookup receipt.slot
  have sameTarget : target = located.target := Option.some.inj (reference.mapped.symm.trans located.reference.mapped)
  subst target
  have payload : receipt.payloadType = binding.bundleType lexical := by
    simpa [OptionalCell.cellType] using Option.some.inj (reference.typed.symm.trans located.reference.typed)
  have bundleType : binding.bundleType active = binding.bundleType lexical := by
    have checked := receipt.bundleType
    rw [sameBinding] at checked
    exact checked.trans payload
  have sameRows : receipt.binding.atContext active = binding.atContext lexical := by
    rw [sameBinding]
    exact (GeneralizedLocalBundleContexts.atContext_eq_of_bundleType context binding bundleType.symm).symm
  have rows : ProductBundle.Pointwise (Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
      (receipt.binding.atContext active) located.values := sameRows ▸ frames
  obtain ⟨native, framed, evaluated⟩ := GeneralizedLocalBundleReadMeaning.preserves receipt rows referenceAt located.nativeRead
  exact ⟨native, framed, (readOnly receipt).evaluation_rename evaluated agrees⟩

def Located.Frames (located : Located (model prepared) function binding lexical location mapping world heap store)
    (frameLocation : Core.Location) : Prop :=
  Located.FramesWith (fun function binding _ => function.source = binding.source) located frameLocation

theorem Located.Frames.transport
    {previous : Located (model prepared) function binding lexical location mapping world heap store}
    {next : Located (model prepared) function binding lexical location futureMapping futureWorld after finalStore}
    {frameLocation : Core.Location} (frames : Located.Frames previous frameLocation)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (sameValues : next.values = previous.values) : Located.Frames next frameLocation := by
  exact Located.FramesWith.transport frames maps worlds sameValues

theorem Located.preserves_framed
    (located : Located (model prepared) function binding lexical location mapping world heap store)
    {frameLocation : Core.Location} (frames : Located.Frames located frameLocation)
    {catalog : SourceCoreDataCatalog.Catalog} {caller : Key} {active : Substitution}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Core.Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate prepared.base.locals caller active source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (context : GeneralizedLocalBundleContexts.ContextExtension lexical active)
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical prepared.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ native, Framed prepared mapping world function binding lexical frameLocation receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  exact Located.preserves_snapshot located frames receipt sameCaller sameBinder context environments lookup agrees

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedLocatedRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
/-! Actual generalized declarations reach their emitted continuation for any
accepted candidate body. Ordered stored rows, the creation frame, and the real
marked allocator survive in both execution directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest sequence)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)

/-- The marked allocation keeps the located rows and their creation frame. -/
theorem framed_after_allocation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request}
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts owner active request)
    {function : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
    {lexical : TypeSystem.Substitution} {values : List Value}
    (payload : request.payloadType = binding.bundleType lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)) mapping world heap store)
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalAcceptedInstances.RepresentsWith prepared mapping world function binding lexical (sourceAttachment function binding lexical))
      (binding.atContext lexical) values)
    {frameLocation : Core.Location}
    (frames : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      (GeneralizedLocalAcceptedInstances.Snapshot prepared mapping world function binding lexical frameLocation (sourceAttachment function binding lexical))
      (binding.atContext lexical) values)
    {native : NativeFrame} {captured : Value} {location : Dynamic.Location}
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    (capturedTyped : RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
      prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized heap function location after) :
    ∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical location
      (mapping ++ [store.length + 2])
      (world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType]) after
      (store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        .inRight .unit (SourceCoreLocalPolymorphism.ProductBundle.value values)]), GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation := by
  have captureType : allocation.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType allocation.entry.key.scope = _
    rw [allocation.keyExact]
    rfl
  have markerTyped : RuntimeValueHasType world (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
      allocation.entry.layout.type prepared.layouts.definitions :=
    .constructed allocation.registered.payloadLookup (captureType.symm ▸ capturedTyped)
  obtain ⟨located, sameValues⟩ := (GeneralizedLocalLocatedRows.of_marked_allocation_values heaps attachment rows
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered native) markerTyped allocated).2
  have finalFrames : GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation := by
    change SourceCoreLocalPolymorphism.ProductBundle.Pointwise _ _ _
    rw [sameValues]
    clear sameValues located rows
    generalize binding.atContext lexical = candidates at frames ⊢
    induction frames with
    | nil => exact .nil
    | cons head _ ih => exact .cons (head.extend ⟨_, rfl⟩ ⟨_, rfl⟩) ih
  rw [payload]
  exact ⟨located, finalFrames⟩


theorem complete_with_at_source {allocationSource : TypedSource} {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalAcceptedInitializer.formation_with
    receipt sourceAttachment attached owner initializer origin attachment captured declarations ownership issuer nativeTyped heaps.runtime_hasTypes
    (index ▸ reference) read
  obtain ⟨marker, _markerCaptures, markerTyped, allocatedNative, environments, finalHeaps, finalLocals,
      agrees, typed, finalReference, finalRead, preserved, transition⟩ :=
    CellAwareGeneralizedAllocation.allocate_initialized_at_source producer rfl registered extended ordinary
      allocation annotation same attachment.captures stored captured.represented heaps locals
      captured.agrees captured.typed reference read allocated initial ready
  have located := framed_after_allocation allocation
    (congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted)
    attachment heaps rows frames registered markerTyped (native := origin.native) allocated
  exact ⟨values, marker, CellAwareGeneralizedDeclaration.sequence_agreement initialized allocatedNative,
    fun completed => CellAwareGeneralizedContinuation.smaller initialized allocatedNative completed,
    environments, finalHeaps, finalLocals, agrees, typed, finalReference, finalRead, preserved, located, transition⟩

/- Compatibility wrapper using the semantic source for the allocation request. -/
theorem complete_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with_at_source (allocationSource := function.source) receipt sourceAttachment attached owner initializer origin attachment
    extended ordinary allocation annotation same producer registered captured declarations ownership issuer nativeTyped
    heaps locals reference index read allocated initial ready output body

theorem complete {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.model prepared)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.model prepared))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.model prepared))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.Frames located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with receipt (fun function binding _ => function.source = binding.source) descriptorSource
    owner initializer origin attachment extended ordinary allocation annotation same producer registered captured
    declarations ownership issuer nativeTyped heaps locals reference index read allocated initial ready output body

/-- The actual paired Source reaches the emitted body continuation without a canonical Source equality. -/
theorem complete_tracked {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : function.source.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest function.source inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared)))
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared))
      mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals function.captured)
    (reference : captured.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, captured.canonical⟩)
    (ready : producer.Ready initial frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker,
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := store ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := world ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := mapping ++ [store.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (store.length + 2)
      ContinuationAgreement actual store
        ((sequence output lowered.expression annotation.expression body).rename captured.embedding)
        (nextRef :: bundle :: actual) nextStore
        (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store
          ((sequence output lowered.expression annotation.expression body).rename captured.embedding) value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: bundle :: actual) nextStore
          (body.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld captured.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: function.captured) (nextRef :: captured.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.trackedModel prepared))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: function.captured) ∧
      EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) captured.embedding).lift
        (nextRef :: captured.canonical) (nextRef :: bundle :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: bundle :: actual)
        (OptionalCell.referenceType lowered.type :: lowered.type :: captured.actualContext) prepared.layouts.definitions ∧
      (nextRef :: captured.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical sourceLocation
        nextMap nextWorld after nextStore, GeneralizedLocalAcceptedLocatedRows.Located.FramesWith (fun _ _ _ => True) located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore, nextRef :: captured.canonical⟩ := by
  exact complete_with receipt (fun _ _ _ => True) True.intro owner initializer origin attachment
    extended ordinary allocation annotation same producer registered captured declarations ownership issuer nativeTyped
    heaps locals reference index read allocated initial ready output body

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
/-! An accepted generalized declaration snapshots its scope. The compiler's
request Source copies the same identifiers as the runtime Source; the marked
copies wrap the bundle initializer and the marked descriptor allocation, so the
principal and its marker capture the copies, while the continuation keeps the
original cells. The copies, the bundle and the allocation form one two-way
continuation boundary for any accepted candidate body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedLexicalWhile (initializedRequest)
open GeneralizedLocalDescriptorHeap GeneralizedLocalLocatedRows
open GeneralizedLocalInstanceCompilation (Inputs)
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)
open SourceSemantics.CaptureBinders (copiedBinder?)

theorem complete_with_at_source {allocationSource : TypedSource} {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog checked.catalog) projects prepared.layouts.definitions}
    {inputs : Inputs} {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : GeneralizedLocalDescriptorOrigin.Origin prepared function binding lexical)
    (attachment : Attachment (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {context : SourceSemantics.Context}
    (extended : BinderExtends function.source.owner function.definitionContext function.binder context)
    (ordinary : allocationSource.inputs.any (fun input => decide (input.id = function.binder.id)) = false)
    (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts inputs.current.owner lexical
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
      prepared.base.globals.length
      (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))
      (initializedRequest allocationSource inputs.scope function.binder lowered.type))
    (same : annotation.original = allocation.expression)
    {captured : Expr}
    (copied : SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt inputs.current.owner lexical (fun error => .sourceAllocation (reprStr error)))))
      allocationSource inputs.scope (fun index => index)
      (snapshotInner lowered.type lowered.expression annotation.expression) = .ok captured)
    (copiedIds : ∀ id, (copiedBinder? allocationSource id).isSome = (copiedBinder? function.source id).isSome)
    {Records : Type} {protocol : ProtectedStateTransition.Protocol Records}
    (producer : ProtectedStateTransition.CellAllocation.Producer
      (catalog := CompatibleEquality.storageCatalog checked.catalog) protocol prepared.layouts
      prepared.ancestry.layout.frame (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)))
    (transitions : ProtectedStateTransition.AdministrativeTransitions protocol)
    (bindings : ProtectedStateTransition.Bindings protocol)
    (registered : prepared.ancestry.layout.frame.Registered prepared.layouts.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {actual : Core.Environment}
    (current : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope environment actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ current.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {before snapshotHeap after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location}
    {frameLocation : Core.Location}
    (heaps : GenericHeap.CellHeapRepresents
      (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.definitionContext.locals environment)
    (reference : current.canonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation))
    (index : SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope =
      inputs.scope.length + 1 + prepared.base.globals.length)
    (read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    (snapshot : Dynamic.EnvironmentCopies function.source environment before function.captured snapshotHeap)
    (allocated : Dynamic.Heap.AllocatesGeneralized snapshotHeap function sourceLocation after)
    (initial : protocol.State ⟨inputs.scope, mapping, world, before, store, current.canonical⟩)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer frameLocation origin.native)
    (output : Ty) (body : Expr) :
    ∃ values marker, ∃ (copiedStore : Store) (copiedMap : LocationMap) (copiedWorld : StoreTyping),
      let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
      let nextStore := copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]
      let nextWorld := copiedWorld ++ [prepared.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType lowered.type]
      let nextMap := copiedMap ++ [copiedStore.length + 2]
      let nextRef := Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)
      ContinuationAgreement actual store ((snapshotSequence output captured body).rename current.embedding)
        (nextRef :: actual) nextStore (body.rename current.embedding.lift) ∧
      (∀ {size value finalStore},
        EvaluationSize size actual store ((snapshotSequence output captured body).rename current.embedding)
          value finalStore →
        ∃ tailSize, tailSize < size ∧ EvaluationSize tailSize (nextRef :: actual) nextStore
          (body.rename current.embedding.lift) value finalStore) ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) nextMap nextWorld current.administrative
        ((function.binder.id, lowered.type) :: inputs.scope)
        ((function.binder.id, sourceLocation) :: environment) (nextRef :: current.canonical) prepared.layouts.definitions ∧
      GenericHeap.CellHeapRepresents (cellModel model (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        nextMap nextWorld after nextStore ∧
      Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: environment) ∧
      EnvironmentsAgree current.embedding.lift (nextRef :: current.canonical) (nextRef :: actual) ∧
      RuntimeEnvironmentHasTypes nextWorld (nextRef :: actual)
        (OptionalCell.referenceType lowered.type :: current.actualContext) prepared.layouts.definitions ∧
      (nextRef :: current.canonical)[((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length]? =
        some (.cellRef prepared.ancestry.layout.frame.type frameLocation) ∧
      nextStore.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native) ∧
      AdministrativePreserved mapping store nextMap nextStore ∧
      LocationMap.Extends mapping nextMap ∧ WorldExtends world nextWorld ∧ (∃ suffix, nextStore = store ++ suffix) ∧
      (∃ located : Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical
        sourceLocation nextMap nextWorld after nextStore,
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located frameLocation) ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨(function.binder.id, lowered.type) :: inputs.scope, nextMap, nextWorld, after, nextStore,
          nextRef :: current.canonical⟩ := by
  have base : (fun index : Nat => index) = (· + ([] : Environment).length) := by
    funext index
    simp
  rw [base] at copied
  obtain ⟨copies, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap, copiedWorld,
      copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds, copiedFrame,
      ⟨copiedSuffix, copiedStoreEq⟩, copiedRead, copiedLookups, copiedTypes, copiedTyped, copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix_cells (pre := []) (preContext := []) copied rfl registered
      current.represented heaps current.agrees rfl current.respects current.typed reference read
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional (copy.of_copiedIds copiedIds) snapshot
  let captures : CallableIndexedLambdaValues.Captures prepared copiedMap copiedWorld inputs.scope function.captured
      copiedActual :=
    ⟨current.administrative, copiedCanonical, copiedContext, copiedEmbedding, copiedEnvironments, copiedLookups,
      copiedTypes, copiedTyped⟩
  have copiedReference : copiedCanonical[inputs.scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    rw [slots _ (by omega)]
    exact reference
  obtain ⟨values, initialized, rows, frames, stored⟩ := GeneralizedLocalAcceptedInitializer.formation_with
    receipt sourceAttachment attached owner initializer origin attachment captures declarations ownership issuer
    nativeTyped copiedHeaps.runtime_hasTypes (index ▸ copiedReference) copiedRead
  let bundle := SourceCoreLocalPolymorphism.ProductBundle.value values
  have canonicalBound : inputs.scope.length < current.canonical.length :=
    Nat.lt_of_le_of_lt (by omega) (List.getElem?_eq_some_iff.mp reference).1
  have copiedBound : inputs.scope.length < copiedCanonical.length :=
    Nat.lt_of_le_of_lt (by omega) (List.getElem?_eq_some_iff.mp copiedReference).1
  obtain ⟨extendedState, extendedRelated⟩ :=
    transitions initial copiedMaps copiedWorlds copiedFrame snapshot.metadata_extends
  obtain ⟨copiedState, copiedRelated⟩ := bindings.rebind extendedState copiedCanonical
    (Nat.le_of_lt canonicalBound) (Nat.le_of_lt copiedBound) slots
  have canonicalLayout : EnvironmentsAgree
      (initializedRequest allocationSource inputs.scope function.binder lowered.type).references copiedCanonical
      (bundle :: copiedCanonical) := fun found => found
  have referenceAt : (bundle :: copiedCanonical)[SourceCoreCallableIndexedAllocationFrames.referenceIndex
      prepared.base.globals.length (initializedRequest allocationSource inputs.scope function.binder lowered.type)]? =
      some (.cellRef prepared.ancestry.layout.frame.type frameLocation) := by
    have named : SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest allocationSource inputs.scope function.binder lowered.type) = false := ordinary
    change (bundle :: copiedCanonical)[Renaming.comp (Renaming.insertion 0) Renaming.id
      (inputs.scope.length + (if SourceCoreCallableIndexedAllocationFrames.isNamedInput
        (initializedRequest allocationSource inputs.scope function.binder lowered.type) then 0 else 1) +
          prepared.base.globals.length)]? = _
    rw [named]
    exact copiedReference
  obtain ⟨marker, _markerCaptures, markerTyped, evaluated, nextHeaps, nextReference, preservation, transition⟩ :=
    producer.complete allocation annotation same rfl registered copiedEnvironments canonicalLayout copiedHeaps
      referenceAt copiedRead (.initialized rfl rfl) (.generalized stored) (.generalized allocated) copiedState
      (ready copiedState copiedRead)
  have allocatedNative : Evaluates (bundle :: copiedActual) copiedStore
      (annotation.expression.rename copiedEmbedding.lift)
      (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2))
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]) :=
    CallableIndexedAllocationRenaming.transport allocation annotation same (Or.inr rfl) evaluated
      (copiedLookups.lift bundle)
  have located := GeneralizedLocalAcceptedPrefix.framed_after_allocation allocation
    (congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted)
    attachment copiedHeaps rows frames registered markerTyped (native := origin.native) allocated
  have innerShape : (snapshotInner lowered.type lowered.expression annotation.expression).rename copiedEmbedding =
      LanguageResult.bind (OptionalCell.referenceType lowered.type) (lowered.expression.rename copiedEmbedding)
        (LanguageResult.success (annotation.expression.rename copiedEmbedding.lift)) := rfl
  have innerEvaluated : Evaluates copiedActual copiedStore
      ((snapshotInner lowered.type lowered.expression annotation.expression).rename copiedEmbedding)
      (.inRight .word (.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2)))
      (copiedStore ++ [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout marker, .inRight .unit bundle]) := by
    rw [innerShape]
    exact LanguageResult.bind_success _ initialized (LanguageResult.success_evaluates allocatedNative)
  have capturedEvaluated := copyAgreement.wrap innerEvaluated
  have outerShape : (snapshotSequence output captured body).rename current.embedding =
      LanguageResult.bind (LocalLoop.controlType output) (captured.rename current.embedding)
        (body.rename current.embedding.lift) := rfl
  have nextLocals : Dynamic.EnvironmentAgrees after context.locals ((function.binder.id, sourceLocation) :: environment) := by
    cases extended
    exact .cons allocated.reads_new
      (congrArg (fun retained : TypedBinder => retained.scheme.body) attachment.captures.binder_eq)
      (.generalized rfl (congrArg TypedBinder.id attachment.captures.binder_eq)
        (congrArg TypedBinder.scheme attachment.captures.binder_eq))
      (locals.mono (snapshot.metadata_extends.trans (.of_generalized_allocation allocated)))
  have finalSlots : ∀ slot, ((function.binder.id, lowered.type) :: inputs.scope).length ≤ slot →
      (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: current.canonical)[slot]? =
        (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: copiedCanonical)[slot]? := by
    intro slot above
    cases slot with
    | zero => simp at above
    | succ slot =>
      simp only [List.getElem?_cons_succ]
      exact (slots slot (by simpa using above)).symm
  obtain ⟨allocatedState, allocatedRelated⟩ := transition
  have requestScope : (initializedRequest allocationSource inputs.scope function.binder lowered.type).scope =
      inputs.scope := rfl
  obtain ⟨finalState, finalRelated⟩ := bindings.rebind allocatedState
    (Value.cellRef (OptionalCell.cellType lowered.type) (copiedStore.length + 2) :: current.canonical)
    (by simp only [List.length_cons, requestScope]; omega) (by simp only [List.length_cons, requestScope]; omega)
    finalSlots
  refine ⟨values, marker, copiedStore, copiedMap, copiedWorld, ?_, ?_,
    CallableIndexedOrdinaryAllocation.bind_environment (current.represented.extend copiedMaps copiedWorlds)
      nextReference,
    nextHeaps, nextLocals, ReadOnly.EnvironmentsAgree.lift current.agrees _,
    .cons (.cellRef nextReference.typed) (current.typed.weaken (copiedWorlds.trans ⟨_, rfl⟩)), ?_, ?_,
    copiedFrame.trans preservation, copiedMaps.trans ⟨_, rfl⟩, copiedWorlds.trans ⟨_, rfl⟩,
    ⟨copiedSuffix ++ _, by rw [copiedStoreEq, List.append_assoc]⟩, located,
    ⟨finalState, protocol.trans extendedRelated (protocol.trans copiedRelated
      (protocol.trans allocatedRelated finalRelated))⟩⟩
  · rw [outerShape]
    exact ContinuationAgreement.bind capturedEvaluated
  · intro size value finalStore completed
    rw [outerShape] at completed
    exact completed.bind_success capturedEvaluated
  · have shifted : ((function.binder.id, lowered.type) :: inputs.scope).length + 1 + prepared.base.globals.length =
        (inputs.scope.length + 1 + prepared.base.globals.length) + 1 := by simp; omega
    rw [shifted]
    exact reference
  · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp copiedRead).1).trans copiedRead

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedSnapshotPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAllocation
/-! The real generalized initializer and marked cell allocation share the
same ordered row values. Each row keeps its creation frame after allocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAllocation
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalDescriptorOrigin (Origin)

theorem formation_allocates_with {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (sourceAttachment : Dynamic.GeneralizedClosure → Binding → Substitution → Prop)
    (attached : sourceAttachment function binding lexical)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.modelWith prepared sourceAttachment)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith sourceAttachment located location := by
  obtain ⟨values, evaluated, rows, frames, _stored⟩ :=
    GeneralizedLocalAcceptedInitializer.formation_with receipt sourceAttachment attached owner initializer origin attachment
      captured declarations ownership issuer typed heaps.runtime_hasTypes reference read
  obtain ⟨afterHeaps, located, sameValues⟩ := GeneralizedLocalLocatedRows.of_marked_allocation_values
    heaps attachment rows snapshotTyped markerTyped allocated
  refine ⟨values, evaluated, afterHeaps, located, sameValues, ?_⟩
  change ProductBundle.Pointwise _ _ _
  rw [sameValues]
  clear evaluated rows _stored afterHeaps located sameValues
  generalize binding.atContext lexical = candidates at frames ⊢
  induction frames with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend ⟨_, rfl⟩ ⟨_, rfl⟩) ih

theorem formation_allocates {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.model prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.model prepared))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.model prepared))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.model prepared)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.Frames located location := by
  exact formation_allocates_with receipt (fun function binding _ => function.source = binding.source)
    descriptorSource owner initializer origin attachment captured declarations ownership issuer typed reference read
    heaps snapshotTyped markerTyped allocated

/-- Storage retains the actual independently tracked Source and capture frame. -/
theorem formation_allocates_tracked {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalAcceptedInitializer.Receipt prepared inputs binding lexical lowered)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalAcceptedInstances.trackedModel prepared) function binding lexical)
    {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared mapping world inputs.scope function.captured actual)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source inputs.scope function.definitionContext)
    (ownership : LocalIdentityOwnership function.source)
    (issuer : GeneralizedLocalDiagnosticIssuer.Receipt prepared inputs)
    (typed : HasType (SourceCoreLocalCell.coreContext inputs.scope ++ captured.administrative)
      lowered.expression (LanguageResult.resultType lowered.type) prepared.layouts.definitions)
    {store : Store} {location : Core.Location}
    (reference : captured.canonical[SourceCoreCallableIndexedAncestry.creationReferenceIndex
      inputs.current inputs.scope]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame origin.native))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
    {before after : Dynamic.Heap} {sourceLocation : Dynamic.Location}
    {snapshot marker : Core.Value} {snapshotType markerType : Core.Ty}
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.trackedModel prepared))
      mapping world before store)
    (snapshotTyped : RuntimeValueHasType world snapshot snapshotType prepared.layouts.definitions)
    (markerTyped : RuntimeValueHasType world marker markerType prepared.layouts.definitions)
    (allocated : Dynamic.Heap.AllocatesGeneralized before function sourceLocation after) :
    ∃ values,
      Evaluates actual store (lowered.expression.rename captured.embedding)
        (.inRight .word (ProductBundle.value values)) store ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel ordinary (GeneralizedLocalAcceptedInstances.trackedModel prepared))
        (mapping ++ [store.length + 2])
        (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
        (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]) ∧
      ∃ located : GeneralizedLocalLocatedRows.Located (GeneralizedLocalAcceptedInstances.trackedModel prepared)
          function binding lexical sourceLocation (mapping ++ [store.length + 2])
          (world ++ [snapshotType, markerType, OptionalCell.cellType (binding.bundleType lexical)]) after
          (store ++ [snapshot, marker, .inRight .unit (ProductBundle.value values)]),
        located.values = values ∧
        GeneralizedLocalAcceptedLocatedRows.Located.FramesWith (fun _ _ _ => True) located location := by
  exact formation_allocates_with receipt (fun _ _ _ => True) True.intro owner initializer origin attachment
    captured declarations ownership issuer typed reference read heaps snapshotTyped markerTyped allocated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInvocation
/-! A materialized general body enters through its actual captured frame and
marked parameter fold. Source typing and the whole compiler receipt refer to
that same closure, including nested declarations and all later statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedParameterMeaning
open GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {mapping : LocationMap} {world : StoreTyping}
  (material : Materialization compiled mapping world function)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerState : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (view : View material)

local notation "payload" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "instances" => GeneralizedLocalAcceptedInstances.model compiled.indexed
local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel payload instances

/-- The current authority and actual Source frame construct the complete body
entry. No finite body profile, body execution, or future heap is supplied. -/
theorem enters
    (frame : Dynamic.ClosureFrame program function)
    (represented : Arguments payload mapping world material.code.receipt.loweredParameters arguments nativeArguments)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)))
    (sameLocation : view.location = owner.key.frameLocation)
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.readFrame view.id material.code.descriptor.id view.callerNative))) :
    ∃ inputs : CallableIndexedLambdaEntryPrefix.Context
        (values := .initial compiled.compatible.checked) material.code,
    ∃ entry : GeneralizedLocalBodyEntry.Entry (values := .initial compiled.compatible.checked)
        material.origin material.captured material.code inputs functions registry cells arguments nativeArguments
        before store owner.key.frameLocation view.callerNative view.callerGhost view.caller view.id view.recipe,
      Dynamic.SourceRuntimeValid program inputs.context function.source ∧
      function.evidence.Covers inputs.context ∧
      Dynamic.HeapWellTyped inputs.context entry.entry.heap ∧
      Dynamic.EnvironmentAgrees entry.entry.heap inputs.context.locals entry.entry.environment ∧
      (∃ finalContext facts,
        StatementsHaveType function.source { returnType := function.resultType } inputs.context
          function.body finalContext facts ∧ BodyCompletes function.resultType facts) ∧
      CellAwareScopeAuthority.Effect instances mapping world before store
        entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store ∧
      (∃ added copied : Environment, added.length = material.code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, material.inputs.scope.length ≤ slot → copied[slot]? = material.captured.canonical[slot]?) ∧
        ProtectedStateTransition.Transition (protocol headers keys) callerState
          ⟨material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩) := by
  obtain ⟨inputs⟩ := GeneralizedLocalAcceptedBodyCompiler.entry_context material frame material.ownership
  have reference : material.captured.canonical[material.code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    simpa only [sameLocation] using view.lexicalReference
  have ordinaryCells : GenericHeap.OrdinaryCells payload cells :=
    GeneralizedLocalDescriptorHeap.ordinary_cells
  obtain ⟨entry, added, copied, length, spine, slots, transition⟩ :=
    GeneralizedLocalOwnedBodyEntry.parameters_with_state material.origin material.captured material.code inputs
      functions ordinaryCells represented owner callerState view.carried view.recipe heaps locals reference read
  have argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types := by
    simpa only [← Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended] using argumentsTyped
  obtain ⟨runtime, covers, heapTyped, environmentTyped, bodyTyped⟩ :=
    GeneralizedLocalOwnedBodyEntry.source_admission material.origin material.captured material.code inputs
      functions owner view.recipe entry frame beforeTyped argumentsTyped
  exact ⟨inputs, entry, runtime, covers, heapTyped, environmentTyped, bodyTyped,
    GeneralizedLocalBodyEntry.Entry.scope_effect (values := .initial compiled.compatible.checked) material.origin material.captured material.code inputs functions registry cells
      arguments nativeArguments before store owner.key.frameLocation view.callerNative view.callerGhost
      view.caller view.id view.recipe entry instances, added, copied, length, spine, slots, transition⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedRead
/-! Actual first-match lookup and the descriptor allocation's retained row
supply materialization at a named read. The native read keeps both the store
and the exact previously created closure value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedRead
open Core Frontend SourceInference GeneralHeap ReadOnly CompatibleEquality
open GeneralizedLocalLocatedRows GeneralizedLocalAcceptedMaterialization

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {descriptor : Dynamic.GeneralizedClosure} {binding : SourceCoreLocalPolymorphism.Binding}
  {lexical : TypeSystem.Substitution} {location : Dynamic.Location}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : SourceCoreLocalPolymorphism.Key} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem preserves
    (located : Located (GeneralizedLocalAcceptedInstances.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    located.preserves_rename receipt sameCaller sameBinder contextExtension environments lookup agrees
  have represented : GeneralizedLocalAcceptedInstances.Represents compiled.indexed mapping world descriptor
      receipt.binding lexical receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, nativeEq⟩ :=
    GeneralizedLocalAcceptedAssociationFormation.materialize receipt represented located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, ?_⟩
  simpa only [nativeEq] using evaluated


theorem preserves_framed
    (located : Located (GeneralizedLocalAcceptedInstances.model compiled.indexed) descriptor binding lexical
      location mapping world heap store)
    {frameLocation : Core.Location} (frames : GeneralizedLocalAcceptedLocatedRows.Located.Frames located frameLocation)
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals caller [] source scope id reason lowered)
    (sameCaller : caller = binding.caller) (sameBinder : receipt.binder = binding.binder.id)
    (contextExtension : GeneralizedLocalBundleContexts.ContextExtension lexical [])
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {embedding : Renaming}
    (environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual)
    (unique : NodeOccurrencesUnique descriptor.source)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme)
    (sameType : actualType = receipt.node.rawType)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization compiled mapping world function,
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧ material.candidate = receipt.candidate ∧
      material.actualType = actualType ∧ material.semantic = semantic ∧ material.context = context ∧
      material.callerEvidence = callerEvidence ∧ material.produced = produced ∧ material.requirements = requirements ∧
      material.frameLocation = frameLocation ∧
      Evaluates actual store (lowered.expression.rename embedding)
        (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
          material.origin.native material.actual)) store := by
  have sameBinding : receipt.binding = binding := by
    have selected := receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    simp only [sameCaller, sameBinder, registered] at selected
    exact (Except.ok.inj selected).symm
  obtain ⟨native, represented, evaluated⟩ :=
    GeneralizedLocalAcceptedLocatedRows.Located.preserves_framed located frames receipt sameCaller sameBinder contextExtension environments lookup agrees
  have framed : GeneralizedLocalAcceptedInstances.Framed compiled.indexed mapping world descriptor
      receipt.binding lexical frameLocation receipt.candidate native := by
    rw [sameBinding]
    exact represented
  have initializer : descriptor.initializer = receipt.binding.initializer := by
    rw [sameBinding]
    exact located.attachment.initializer
  obtain ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
      callerEq, producedEq, requirementsEq, frameEq, nativeEq⟩ :=
    GeneralizedLocalAcceptedAssociationFormation.materialize_framed receipt framed located.attachment.captures unique
      initializer instantiation sameScheme sameType profile
  refine ⟨material, descriptorEq, bindingEq, lexicalEq, candidateEq, typeEq, semanticEq, contextEq,
    callerEq, producedEq, requirementsEq, frameEq, ?_⟩
  simpa only [nativeEq] using evaluated

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedRead
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedViewedFormation
/-! Native typing for the materialized wrapper follows from its accepted
emission and actual read execution in the unchanged store. The resulting
positive association is the one used by mixed public function values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {viewRelation : SourceInference.TypedSource → SourceInference.TypedSource → Prop}
  {material : Materialization compiled mapping world function viewRelation}

theorem View.formation (view : View material) {store : Store}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative)) :
    Evaluates view.environment store (view.lowered.expression.rename view.embedding)
      (.inRight .word view.native) store := by
  rw [view.emitted]
  exact GeneralizedLocalReadView.formation read view.reference snapshot

theorem View.runtime_hasType (view : View material) {context : Core.Context}
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions) :
    RuntimeValueHasType world view.native
      (CallableContract.functionType material.code.receipt.parameterCore material.code.receipt.resultCore)
      compiled.indexed.layouts.definitions := by
  have raw := material.rawTyped
  rw [material.native_type] at raw
  exact GeneralizedLocalReadView.runtime_hasType (CallableIndexedAmbient.frame_registered compiled.indexed)
    raw environments view.reference

theorem View.represents (view : View material) {store : Store} {context : Core.Context}
    (read : Evaluates view.environment store (view.original.expression.rename view.embedding)
      (.inRight .word (CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual)) store)
    (snapshot : store.read? view.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame view.callerNative))
    (typed : HasType context (view.lowered.expression.rename view.embedding)
      (LanguageResult.resultType (CallableContract.functionType material.code.receipt.parameterCore
        material.code.receipt.resultCore)) compiled.indexed.layouts.definitions)
    (environments : RuntimeEnvironmentHasTypes world view.environment context compiled.indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Nonempty (Association (viewRelation := viewRelation) compiled mapping world function view.native material.code.receipt.loweredParameters
      material.code.receipt.parameterCore material.code.receipt.resultCore) := by
  have evaluated := view.formation read snapshot
  obtain ⟨future, _, finalStored, outputTyped⟩ := evaluation_preserves_type evaluated typed environments stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases outputTyped with
  | inRight typed => exact ⟨.viewed material view typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
end
