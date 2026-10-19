import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerPackets
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceFrames
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLocatedRows

/-! The actual finite initializer creates its ordered native closures in the
current lexical frame. It retains the complete Source descriptor without
executing the initializer or assuming any future instance body evaluation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
open Core Frontend SourceInference TypeSystem GeneralHeap
open SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalDescriptorOrigin (Origin)
open GeneralizedLocalInitializerPackets (IndexedRows Receipt)

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
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
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
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Represents prepared mapping world
        function binding lexical) candidates values ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Framed prepared mapping world
        function binding lexical location) candidates values := by
  induction rows with
  | nil => exact ⟨[], .nil, .nil, .nil⟩
  | @cons candidate raw rest remaining head tail ih =>
    cases typed with
    | cons rawTyped restTyped =>
      obtain ⟨packet, ⟨⟨indexed, sameLexical⟩, bodyProfile⟩⟩ := head
      have sameIndex : GeneralizedLocalInstanceValues.referenceIndex indexed =
          SourceCoreCallableIndexedAncestry.creationReferenceIndex inputs.current inputs.scope := rfl
      obtain ⟨evaluated, framed⟩ := GeneralizedLocalInstanceValues.formation_at_frame indexed bodyProfile sameLexical
        owner initializer (sources candidate (by simp)) (binders candidate (by simp))
        descriptorSource origin namedLexical namedMetadata captured declarations ownership issuer rawTyped stored (sameIndex ▸ reference) read
      obtain ⟨values, evaluations, representedRows, framedRows⟩ := ih (fun child member => sources child (List.mem_cons_of_mem _ member))
        (fun child member => binders child (List.mem_cons_of_mem _ member)) restTyped
      exact ⟨_, .cons evaluated evaluations, .cons framed.forget representedRows, .cons framed framedRows⟩

/-- The production initializer produces the complete bundle in the original
store. Its Source attachment retains the real binding and captured metadata. -/
theorem formation {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {inputs : Inputs}
    {function : Dynamic.GeneralizedClosure} {binding : Binding} {lexical : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt prepared inputs binding lexical lowered)
    (descriptorSource : function.source = binding.source)
    (owner : inputs.current.owner = binding.caller)
    (initializer : inputs.initializer = binding.initializer)
    (origin : Origin prepared function binding lexical)
    (namedLexical : lexical = [])
    (namedMetadata : origin.metadata = ⟨⟨binding.caller, [], binding.source⟩, []⟩)
    (attachment : GeneralizedLocalLocatedRows.Attachment
      (GeneralizedLocalInstanceValues.model prepared) function binding lexical)
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
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Represents prepared mapping world
        function binding lexical) (binding.atContext lexical) values ∧
      ProductBundle.Pointwise (GeneralizedLocalInstanceValues.Framed prepared mapping world
        function binding lexical location) (binding.atContext lexical) values ∧
      GeneralizedLocalDescriptorHeap.Stored (GeneralizedLocalInstanceValues.model prepared)
        mapping world function (ProductBundle.value values) lowered.type := by
  obtain ⟨values, evaluations, rows, frames⟩ := rows_form receipt.rows receipt.sources receipt.binders descriptorSource owner initializer origin namedLexical namedMetadata captured declarations ownership issuer
    (receipt.raw_typed typed).2 stored reference read
  refine ⟨values, ?_, rows, frames, ?_⟩
  · rw [receipt.original.emitted]
    exact .inRight (bundle_evaluates evaluations)
  · have payload : lowered.type = binding.bundleType lexical :=
      congrArg SourceCoreBasic.LoweredExpr.type receipt.original.emitted
    rw [payload]
    exact attachment.stored rows

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerMeaning
