import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceSpecializationWorklist

/-!
Shared declarations for specialization-plan validation and execution.

These declarations contain no runtime values, heap, or evaluator. The historical
`SourceTypedRuntime` names are retained while both execution backends migrate to
an evaluator-independent compilation boundary. `RuntimeError` is the existing
shared diagnostic carrier; preserving it keeps all rejection cases stable.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Location where
  index : Nat
  deriving Repr, BEq, DecidableEq

/-- Closed trait evidence available while one specialized function body is
executing.  The carrier deliberately excludes `PredicateEvidence.assumption`:
every entry has already been discharged by an enclosing call.  Call assembly
and `Matches`, rather than the list carrier itself, enforce the specialized
signature's predicate order. -/
abbrev RuntimeEvidenceEnvironment := List TypedTraitResolution.Evidence

namespace RuntimeEvidenceEnvironment

def goals (environment : RuntimeEvidenceEnvironment) : List ProgramPredicate :=
  environment.map fun
    | .byImpl goal _ _ => goal

/-- The executable dictionary has exactly the goals, order, and multiplicity
declared by the specialization about to execute. -/
def Matches (environment : RuntimeEvidenceEnvironment)
    (predicates : List ProgramPredicate) : Prop :=
  environment.goals = predicates

theorem Matches.length_eq
    {environment : RuntimeEvidenceEnvironment}
    {predicates : List ProgramPredicate}
    (agreement : environment.Matches predicates) :
    environment.length = predicates.length := by
  unfold Matches goals at agreement
  rw [← agreement, List.length_map]

end RuntimeEvidenceEnvironment

/-- Runtime evidence attached to one concrete use of a qualified local
scheme.  Requirement identities, rather than predicate equality, connect the
assumption in the stored lambda body to the independently solved obligation at
the local-reference occurrence. -/
structure LocalRequirementWitness where
  templateRequirement : RequirementId
  actualRequirement : RequirementId
  predicate : ProgramPredicate
  evidence : TypedTraitResolution.Evidence
  deriving Repr

inductive RuntimeError where
  | missingSpecialization (key : Key)
  | duplicateSpecialization (key : Key) (count : Nat)
  | inputPlanWorklist (error : SourceSpecializationWorklist.Error)
  | inputPlanBudgetExhausted (next : Key)
  | nonCanonicalInputPlan
  | specializationOwnershipMismatch
      (key : Key) (declaration functionDeclaration typedBodyOwner :
        Resolved.DeclarationId)
  | missingInstantiationTarget
      (declaration : Resolved.DeclarationId) (type : Ty)
  | duplicateInstantiationTargets
      (declaration : Resolved.DeclarationId) (type : Ty) (count : Nat)
  | invalidFunctionType (key : Key) (type : Ty)
  | inferredResultTypeMismatch (key : Key) (declared inferred : Ty)
  | unresolvedAssumptions (key : Key) (predicates : List ProgramPredicate)
  | runtimeEvidenceCountMismatch (key : Key) (expected actual : Nat)
  | runtimeEvidenceGoalMismatch
      (key : Key) (index : Nat)
      (expected actual : ProgramPredicate)
  | runtimeEvidenceResolutionNoSolution (key : Key)
      (predicate : ProgramPredicate)
  | runtimeEvidenceResolutionInconclusive (key : Key)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId Ty ProgramImplId)
  | runtimeEvidenceNotSelected
      (key : Key) (index : Nat) (goal : ProgramPredicate)
      (implementation : ProgramImplId)
  | missingRuntimeAssumptionEvidence
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | stagedExpressionType (id : ExpressionId) (type : Ty)
  | missingExpressionStage
      (caller : Key) (use : ExpressionId) (expression : ExpressionId)
  | comptimeArgumentStageMismatch
      (caller : Key) (use : ExpressionId) (index : Nat)
      (argument : ExpressionId) (actual : SourceStageAnalysis.Stage)
  | comptimeResultStageMismatch
      (caller : Key) (use : ExpressionId) (callee : Key)
      (actual : SourceStageAnalysis.Stage)
  | unsupportedStagedInput (expected : Ty)
  | inputValidationFuelExhausted (expected : Ty) (fuel : Nat)
  | missingExpression (id : ExpressionId)
  | missingStatement (id : StatementId)
  | expectedStatementRoot (id : ExpressionId)
  | unboundLocal (id : Resolved.LocalId)
  | danglingLocation (location : Location)
  | uninitializedLocal (id : Resolved.LocalId)
  | duplicateCallEdge (caller : Key) (id : ExpressionId) (count : Nat)
  | missingCallEdge (caller : Key) (id : ExpressionId)
  | callRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Nat)
  | invalidDirectCallRequirementLayout
      (caller : Key) (id : ExpressionId)
      (requirements : List RequirementId)
  | invalidDeclarationReferenceRequirementLayout
      (caller : Key) (id : ExpressionId)
      (requirements : List RequirementId)
  | duplicateCallRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | missingSolvedRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | duplicateSolvedRequirements
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (count : Nat)
  | callRequirementPredicateMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | callRequirementEvidenceGoalMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unsupportedCallAssumptionEvidence
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | callEvidenceResolutionNoSolution
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (goal : ProgramPredicate)
  | callEvidenceResolutionInconclusive
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId Ty ProgramImplId)
  | callEvidenceNotSelected
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (goal : ProgramPredicate) (implementation : ProgramImplId)
  | localSchemeInstanceMismatch
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (expected actual : Ty)
  | localSchemeRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (expected actual : Nat)
  | duplicateLocalSchemeTemplateRequirement
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | duplicateLocalSchemeActualRequirement
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | localSchemeTemplateExpectedAssumption
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | localSchemeActualExpectedImplementation
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | nonGroundLocalSchemePredicate
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | unsupportedQualifiedLocalReference
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
  | unsupportedQualifiedLocalInitializer
      (caller : Key) (binder : Resolved.LocalId) (initializer : ExpressionId)
  | unsupportedLocalSchemeTemplateUse
      (caller : Key) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | unsupportedConstrainedDeclarationReference
      (caller : Key) (call callee : ExpressionId)
  | duplicateReferenceEdge (caller : Key) (id : ExpressionId) (count : Nat)
  | missingReferenceEdge (caller : Key) (id : ExpressionId)
  | declarationMetadataMismatch (call callee : ExpressionId)
  | malformedLiteral (id : ExpressionId)
  | literalMetadataMismatch (id : ExpressionId)
  | expectedBool (actual : Option Ty)
  | expectedWord (actual : Option Ty)
  | expectedInteger (actual : Option Ty)
  | expectedFunction (actual : Option Ty)
  | expectedMapping (actual : Option Ty)
  | expectedConstructor (actual : Option Ty)
  | expectedProduct (actual : Option Ty)
  | typeMismatch (expected : Ty) (actual : Option Ty)
  | resultTypeMismatch (expected : Ty) (actual : Option Ty)
  | argumentArityMismatch (expected actual : Nat)
  | invalidUnaryOperand (operator : Syntax.UnaryOp) (actual : Option Ty)
  | invalidBinaryOperands
      (operator : Syntax.BinaryOp) (left right : Option Ty)
  | unsupportedRuntimeUnary
      (caller : Key) (id : ExpressionId) (operator : Syntax.UnaryOp)
  | unsupportedRuntimeBinary
      (caller : Key) (id : ExpressionId) (operator : Syntax.BinaryOp)
  | unaryRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Nat)
  | binaryRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Nat)
  | duplicateUnaryRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | duplicateBinaryRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | runtimeUnaryTraitNameMismatch
      (caller : Key) (id : ExpressionId) (expected actual : String)
  | runtimeBinaryTraitNameMismatch
      (caller : Key) (id : ExpressionId) (expected actual : String)
  | executableUnaryMethod
      (caller : Key) (id : ExpressionId)
      (error : ExecutableImplMethods.Error)
  | executableBinaryMethod
      (caller : Key) (id : ExpressionId)
      (error : ExecutableImplMethods.Error)
  | runtimeUnaryInputTypesMismatch
      (caller : Key) (id : ExpressionId) (expected actual : List Ty)
  | runtimeBinaryInputTypesMismatch
      (caller : Key) (id : ExpressionId) (expected actual : List Ty)
  | runtimeUnaryResultTypeMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Ty)
  | runtimeBinaryResultTypeMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Ty)
  | operatorMethodWorklist
      (caller : Key) (id : ExpressionId)
      (error : SourceSpecializationWorklist.Error)
  | operatorMethodSpecializationBudgetExhausted
      (caller : Key) (id : ExpressionId) (next : Key) (pending : Nat)
  | invalidAssignmentOperands
      (operator : Syntax.ValueAssignOp) (left right : Option Ty)
  | invalidMember (name : String) (index : Nat) (actual : Option Ty)
  | invalidPlaceProjection
  | invalidExpressionCoercionPath
      (expression : ExpressionId) (source target : Ty)
  | invalidIndirectArgumentCoercionPath (expression : ExpressionId)
  | indirectCalleeNotFunction (call : ExpressionId) (type : Ty)
  | indirectArgumentBundleMismatch
      (call : ExpressionId) (expected actual : Ty)
  | indirectParameterTypeMismatch
      (call : ExpressionId) (expected actual : Ty)
  | indirectResultTypeMismatch
      (call : ExpressionId) (expected actual : Ty)
  | duplicateCoercionRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | coercionPredicateMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (source target : Ty) (actual : ProgramPredicate)
  | coercionTraitMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (trait : ProgramTraitId)
  | coercionMethodRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : Nat)
  | executableCoercionMethod
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (error : ExecutableImplMethods.Error)
  | coercionMethodWorklist
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (error : SourceSpecializationWorklist.Error)
  | coercionMethodSpecializationBudgetExhausted
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (next : Key) (pending : Nat)
  | executablePlanClosureFuelExhausted (nextSpecialization : Nat)
  | unsupportedCoercion (source target : Ty)
  | unsupportedRequirements (requirements : List RequirementId)
  | unsupportedExpressionCoercions (expression : ExpressionId)
  | unsupportedIndirectCoercions (expression : ExpressionId)
  | invalidLiteralEvidence (requirement : RequirementId)
  | invalidPatternMetadata
  | malformedPattern
  | controlEscapedFunction
  | functionFellThrough (expected : Ty)
  | invalidBuiltin (function : BuiltinFunctionId)
  | deepSafetyInitialStateRejected
  | deepSafetyInputsRejected
  | deepSafetyFinalStateRejected
  | deepSafetyResultRejected (expected : Ty) (actual : Option Ty)
  deriving Repr, DecidableEq

end Solcore.Frontend.SourceTypedRuntime
