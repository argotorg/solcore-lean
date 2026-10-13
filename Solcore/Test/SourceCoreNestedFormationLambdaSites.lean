import Solcore.Test.SourceCoreNestedFormationMakeSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedProgram.inner_owned {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner :=
  graph.nodesOwned _ (lookupExpression?_sound observed.makeShape.expressionFound).1

theorem ObservedProgram.inner_read {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id =
      .ok (observed.makeShape.expression, Core.CallableContract.functionType .unit .word) := by
  simp [SourceCoreCompatibleDataExpressions.readExpression, observed.inner_owned graph,
    observed.makeShape.expressionFound, observed.makeShape.requirements, observed.makeShape.coercions,
    SourceCoreCompatibleDataExpressions.projectType, SourceCoreCompatibleCatalog.Checked.project,
    observed.makeShape.expressionType, closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile,
    Core.CallableContract.functionType, Core.TaggedFunction.functionType, Core.TaggedFunction.identityType,
    Core.LanguageResult.resultType, Core.Ty.isWellFormed,
    TypeSystem.Ty.unit, TypeSystem.Ty.word]
  rfl

def ObservedProgram.inner_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (caller : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (same : caller.function.source = observed.makeRow.row.function.typedBody)
    (graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody) :
    CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors.ReturnLambda caller
      observed.makeShape.expression.id where
  node := observed.makeShape.expression
  reported := Core.CallableContract.functionType .unit .word
  parameters := []
  result := .word
  statement := observed.makeShape.innerReturn.id
  returnNode := observed.makeShape.innerReturn
  expression := observed.makeShape.call.value.node.id
  found := by rw [same]; exact observed.makeShape.expressionFound
  form := observed.makeShape.lambda
  owner := by rw [same]; exact observed.inner_owned graph
  requirements := observed.makeShape.requirements
  coercions := observed.makeShape.coercions
  ordinary := by rw [observed.noLocals]; rfl
  read := by rw [same]; exact observed.inner_read graph
  returnFound := by rw [same]; exact observed.makeShape.innerReturnFound
  returnForm := observed.makeShape.innerReturnForm
  returnType := observed.makeShape.innerReturnType

end Tests.SourceCoreNestedFormation
