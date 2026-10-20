import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInstances
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

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
