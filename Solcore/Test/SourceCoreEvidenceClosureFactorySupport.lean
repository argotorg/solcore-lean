import Solcore.Test.SourceCoreEvidenceClosureSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedFactory (fixture : CompiledFixture)
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) where
  owned : shape.expression.id.occurrence.owner = function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    function.typedBody shape.expression.id = .ok (shape.expression, reported)

private def confirm (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFactorySupport (fixture : CompiledFixture)
    {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : FactoryShape function signature generic firstParameter secondParameter firstType secondType trait) :
    IO (ObservedFactory fixture shape) := do
  let ⟨owned⟩ ← confirm (shape.expression.id.occurrence.owner = function.typedBody.owner) "factory lambda owner"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      function.typedBody shape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = shape.expression) "factory lambda node"
    return ⟨owned, reported, by simpa only [same] using read⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  word : ObservedFactory fixture observed.factoryWordShape
  bool : ObservedFactory fixture observed.factoryBoolShape

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.factoryWordShape,
    ← observeFactorySupport fixture observed.factoryBoolShape⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
  {generic : ProgramFunctionSignature} {firstParameter secondParameter : TypeSystem.TypeParameterId}
  {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}

include observed in
theorem ActualHeader.factory_formation (actual : ActualHeader fixture row.row)
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (extra : ObservedFactory fixture shape) (stages : ObservedStages fixture row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = shape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.wordRow.entryMember (node := shape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact shape.expressionFound
  · exact shape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact shape.requirements
  · exact shape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact shape.body_shape
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact shape.body_syntax (actual.source ▸ actual.header.unique) True.intro typed

include observed in
theorem ActualHeader.factory_support (actual : ActualHeader fixture row.row)
    (shape : FactoryShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (extra : ObservedFactory fixture shape) (stages : ObservedStages fixture row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.expression.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry actual.header
        stages.registry terminal faults) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ :=
    actual.terminal shape.expression.id shape.outerReturn shape.roots shape.outerFound shape.outerForm
  obtain ⟨formation⟩ := actual.factory_formation (observed := observed) shape extra stages terminal diagnostic expression
  exact ⟨terminal, expression, ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    headers (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩⟩

end Tests.SourceCoreEvidenceClosure
