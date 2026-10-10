import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaSourceDiagnostics

/-! A named profile retains the literal prepared row and the coupled native
collector output at its actual parameter entry. The authentic diagnostic
issuance is aligned pointwise with that same collected plan. These are static
compiler fields; no expression, flow or body execution law is stored here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

/-- The positive compiler packet keeps its actual Prepared/HeaderAt and
collection. Token equalities concern the genuine receiving issuance. -/
structure Profile (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (administrative : Core.Context) where
  row : SourceSpecialization.SpecializedFunction
  prepared : Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  first : Nat
  operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source
  assignmentsPrepared : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok prepared.compilation.own.assignments
  extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
    (certificates := certificates) (expressionSyntax := expressionSyntax) (administrative := administrative)
    prepared operandsTyped assignmentsPrepared
  issued : IssuedSource compiled header.owner header.function.source
  assignments : issued.assignments = prepared.compilation.own.assignments
  operand : issued.invalidOperand = Prepared.invalidOperand prepared
  unary : issued.invalidUnary = Prepared.invalidUnary prepared
  projection : issued.invalidProjection = Prepared.invalidProjection prepared
  missing : issued.missingDefault = Prepared.missingDefault prepared

namespace Profile
variable {administrative : Core.Context}
  (profile : Profile (certificates := certificates) (expressionSyntax := expressionSyntax) header administrative)

/-- Forward projection keeps the exact generated flow and compiler Tree. -/
def nested : CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile
    (certificates := certificates) (expressionSyntax := expressionSyntax) true header administrative :=
  CallableIndexedOwnedPreparedNestedNamedProfileView.of_direct
    (CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt.profile
      profile.prepared profile.aligned profile.operandsTyped profile.assignmentsPrepared profile.extraction)

/-- Replacing the assignment field by its proved-equal literal compiler table
makes the factory index definitionally exact. All issuer provenance is kept. -/
def receiving : IssuedSource compiled header.owner header.function.source :=
  { profile.issued with
    assignments := profile.prepared.compilation.own.assignments
    assignmentsPrepared := profile.assignments ▸ profile.issued.assignmentsPrepared }

/-- The same genuine extraction factory is used at the aligned table. -/
def factory : AssignmentDiagnosticOrigins.Factory true .reachable header.function.source profile.receiving.invalidOperand :=
  CallableIndexedOwnedPreparedDirectNamedProfileExtraction.assignment_factory
    profile.prepared profile.operandsTyped profile.assignmentsPrepared

/-- Pointwise diagnostic alignment keeps the same collected eliminator. -/
theorem prepared_eliminator : GenericImperativeMatch.Structural.Eliminates
    (layouts := header.layouts) (owner := header.owner) (active := header.active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := header.globals) (onError := header.onError)
    (values := .initial compiled.compatible.checked) (source := header.function.source)
    (expressionSyntax := expressionSyntax header) (certificates := certificates header)
    (definitions := compiled.indexed.layouts.definitions)
    (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
    (fun head => GenericForHeader.Structural.PreparedAssignment profile.factory profile.receiving.invalidProjection profile.receiving.missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true header.function.source profile.receiving.invalidUnary head)
    (fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := profile.factory)
      (invalidProjection := profile.receiving.invalidProjection) (missingDefault := profile.receiving.missingDefault)
      (invalidUnary := profile.receiving.invalidUnary) tree)
    (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)
    header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (.statements true header.function.body) header.function.resultType header.output profile.nested.flow := by
  have projection : profile.receiving.invalidProjection = Prepared.invalidProjection profile.prepared :=
    profile.projection
  have missing : profile.receiving.missingDefault = Prepared.missingDefault profile.prepared :=
    profile.missing
  have unary : profile.receiving.invalidUnary = Prepared.invalidUnary profile.prepared := rfl
  rw [projection, missing, unary]
  exact profile.extraction.collected.eliminate
    (header.valid.ledger.trans (by simpa only [Prepared.ambientMatch, Prepared.baseMatch] using profile.aligned.solved))

end Profile
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles
