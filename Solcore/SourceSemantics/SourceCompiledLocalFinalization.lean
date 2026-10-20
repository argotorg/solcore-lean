import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins
import Solcore.SourceSemantics.SourceInferenceSoundness

/-! One successful body check retains its actual inference, return unification
and finalization. The reusable solver resources come from that finalizer;
neither declarative body typing nor monomorphic locals are assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness

def context (environment : ProgramEnvironment) (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (declaration : ProgramDeclaration) : SourceInference.Context :=
  { environment, signatures, scope := .ofDeclaration declaration,
    typeParameters := signature.scheme.parameters, assumptions := signature.scheme.predicates }

def initial (signature : ProgramFunctionSignature) (declaration : ProgramDeclaration) : State :=
  State.initial declaration.id
    ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
      (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime

structure BodyReceipt (environment : ProgramEnvironment) (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) (fuel : Nat) (checked : CheckedFunction) where
  accepted : checkFunctionBody environment signatures signature fuel = .ok checked
  declaration : ProgramDeclaration
  body : Detail.BlockResult
  returned : State
  finalized : SourceInference.Result
  declared : environment.declaration? signature.id = some declaration
  inferred : Detail.inferStatementsFuel fuel (context environment signatures signature declaration)
    signature.source.value.body.value (Ty.productMany signature.returnTypes)
    (initial signature declaration) = .ok body
  unified : Detail.unify body.state body.type (Ty.productMany signature.returnTypes) = .ok returned
  finalization : Detail.finalize (context environment signatures signature declaration)
    (Ty.productMany signature.returnTypes) returned (body.statements.map NodeId.statement) = .ok finalized
  checkedResult : checked = {
    declaration := signature.id
    type := signature.scheme.body
    inferredBodyType := finalized.type
    returnComptime := signature.returnComptime
    substitution := finalized.substitution
    solvedRequirements := finalized.solvedRequirements
    typedBody := finalized.typedSource }

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem of_check (accepted : checkFunctionBody environment signatures signature fuel = .ok checked) :
    Nonempty (BodyReceipt environment signatures signature fuel checked) := by
  obtain ⟨declaration, body, returned, finalized, declared, inferred, unified, finalization, result⟩ :=
    checkFunctionBody_success_witness accepted
  exact ⟨⟨accepted, declaration, body, returned, finalized, declared, inferred, unified, finalization, result⟩⟩

def resources (receipt : BodyReceipt environment signatures signature fuel checked) :
    FinalInferenceResources (context environment signatures signature receipt.declaration)
      (Ty.productMany signature.returnTypes) receipt.returned
      (receipt.body.statements.map NodeId.statement) receipt.finalized :=
  FinalInferenceResources.ofFinalize receipt.finalization

theorem returned_nodes (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.returned.nodes = receipt.body.state.nodes :=
  (Detail.unify_occurrenceState_eq receipt.unified).1

theorem returned_requirements (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.returned.requirements = receipt.body.state.requirements :=
  Detail.unify_requirements_eq receipt.unified

theorem solver_requirements (receipt : BodyReceipt environment signatures signature fuel checked) :
    receipt.resources.finalState.requirements = receipt.body.state.requirements :=
  receipt.resources.requirements_eq.trans receipt.returned_requirements

theorem substitution (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.substitution = receipt.finalized.substitution :=
  congrArg CheckedFunction.substitution receipt.checkedResult

theorem solved (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.solvedRequirements = receipt.finalized.solvedRequirements :=
  congrArg CheckedFunction.solvedRequirements receipt.checkedResult

theorem source (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.typedBody = receipt.finalized.typedSource :=
  congrArg CheckedFunction.typedBody receipt.checkedResult

theorem source_nodes (receipt : BodyReceipt environment signatures signature fuel checked) :
    checked.typedBody.nodes = receipt.body.state.nodes.map (Node.applySubstitution receipt.finalized.substitution) := by
  rw [receipt.source, receipt.resources.source_eq]
  change receipt.returned.nodes.map (Node.applySubstitution receipt.finalized.substitution) = _
  rw [receipt.returned_nodes]

end BodyReceipt
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
