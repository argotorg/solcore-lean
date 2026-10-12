import Solcore.Test.SourceCoreCapturedCopyFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata

/-! The actual six-node source supplies original policy metadata for both the
initializer's seed read and the closure body's distinct captured-local read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedReadLambdaMetadata (NodeMetadata)

theorem ObservedFactory.node_metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    NodeMetadata node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.nodes] at present
  have alternatives : node = observed.shape.initialRead ∨ node = observed.shape.read ∨
      node = observed.shape.expression := by simpa using present
  rcases alternatives with rfl | rfl | rfl
  · exact .inl ⟨_, _, observed.shape.initialReadForm,
      observed.shape.initialReadRequirements, observed.shape.initialReadCoercions⟩
  · exact .inl ⟨_, _, observed.shape.readForm,
      observed.shape.readRequirements, observed.shape.readCoercions⟩
  · exact .inr ⟨_, _, _, observed.shape.lambda⟩

/-- Metadata follows from compiler observations, independently of a Source
trace, native execution result, caller state or a chosen body meaning. -/
theorem ObservedFactory.metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) (named : CallableIndexedNamedGeneration.Named) :
    MetadataFor fixture.recipe.compiled.indexed named observed.row.function.typedBody :=
  CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named
    (fun _ _ found => observed.node_metadata found) observed.noLocals

/-- Every authentic cached owner has the same observed original source. -/
theorem ObservedStages.metadata {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : CallableIndexedNamedGeneration.Named}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    MetadataFor fixture.recipe.compiled.indexed named (CallableIndexedNamedGeneration.source named) := by
  rw [stages.source_of_cached actual selected]
  exact observed.metadata named

end Tests.SourceCoreCapturedCopy
