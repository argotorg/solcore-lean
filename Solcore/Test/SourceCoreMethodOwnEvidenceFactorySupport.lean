import Solcore.Test.SourceCoreMethodOwnEvidenceFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOwnEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

structure ObservedFactory (fixture : CompiledFixture) {function : CheckedFunction} {generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape function generic parameter type trait) where
  owned : shape.expression.node.id.occurrence.owner = function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    function.typedBody shape.expression.node.id = .ok (shape.expression.node, reported)

private def confirm (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFactorySupport (fixture : CompiledFixture) {function : CheckedFunction} {generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape function generic parameter type trait) : IO (ObservedFactory fixture shape) := do
  let ⟨owned⟩ ← confirm (shape.expression.node.id.occurrence.owner = function.typedBody.owner) "factory lambda owner"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      function.typedBody shape.expression.node.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = shape.expression.node) "factory lambda node"
    return ⟨owned, reported, by simpa only [same] using read⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  word : ObservedFactory fixture observed.makeWordShape
  bool : ObservedFactory fixture observed.makeBoolShape

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.makeWordShape,
    ← observeFactorySupport fixture observed.makeBoolShape⟩

theorem ActualHeader.factory_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty} {trait : ProgramTraitId} (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (extra : ObservedFactory fixture shape) (actual : ActualHeader fixture row.row)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {stages : Staging.Recursive.Registry} :
    ∃ terminal : Terminal actual.header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ :=
    actual.terminal shape.expression.node.id shape.outerReturn shape.roots shape.outerReturnFound shape.outerReturnForm
  refine ⟨terminal, ?_⟩
  apply CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_actual terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile
    observed.wordRow.entryMember (node := shape.expression.node) (reported := extra.reported)
  · rw [actual.source, expression]; exact shape.expression.found
  · exact shape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact shape.expression.requirements
  · exact shape.expression.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact shape.statementFound
  · exact shape.statementForm
  · exact shape.statementType
  · exact point

end Tests.SourceCoreMethodOwnEvidence
