import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates

/-! Full reflection of the existing carrier comparison. Runtime comparisons
remain unchanged: every source node, ordered evidence tree and stage entry is
part of the equality returned here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
open Frontend SourceInference

deriving instance ReflBEq, LawfulBEq for BuiltinFunctionId
deriving instance ReflBEq, LawfulBEq for BuiltinTraitId
deriving instance ReflBEq, LawfulBEq for ProgramTraitId
deriving instance ReflBEq, LawfulBEq for BuiltinImplId
deriving instance ReflBEq, LawfulBEq for ProgramImplId
deriving instance ReflBEq, LawfulBEq for ProgramPredicate
deriving instance ReflBEq, LawfulBEq for RequirementId
deriving instance ReflBEq, LawfulBEq for OccurrenceId
deriving instance ReflBEq, LawfulBEq for Syntax.SourceOrigin
deriving instance ReflBEq, LawfulBEq for Syntax.SourceId
deriving instance ReflBEq, LawfulBEq for Syntax.SourceSpan
deriving instance ReflBEq, LawfulBEq for Syntax.Located
deriving instance ReflBEq, LawfulBEq for Syntax.CoreLiteralValue
deriving instance ReflBEq, LawfulBEq for Syntax.UnaryOp
deriving instance ReflBEq, LawfulBEq for Syntax.BinaryOp
deriving instance ReflBEq, LawfulBEq for Syntax.ValueAssignOp
deriving instance ReflBEq, LawfulBEq for ProgramDataConstructorId
deriving instance ReflBEq, LawfulBEq for LocalSchemeRequirement
deriving instance ReflBEq, LawfulBEq for TypedBinder
deriving instance ReflBEq, LawfulBEq for DeclarationInstantiation
deriving instance ReflBEq, LawfulBEq for DataConstructorInstantiation
deriving instance ReflBEq, LawfulBEq for CoercionStep
deriving instance ReflBEq, LawfulBEq for IntegerLiteralResolution
deriving instance ReflBEq, LawfulBEq for MatchPatternSource
deriving instance ReflBEq, LawfulBEq for MatchPatternInstruction
deriving instance ReflBEq, LawfulBEq for MatchPatternResolution
deriving instance ReflBEq, LawfulBEq for TypedMatchPattern
deriving instance ReflBEq, LawfulBEq for IndirectCallResolution
deriving instance ReflBEq, LawfulBEq for ReferenceResolution
deriving instance ReflBEq, LawfulBEq for CallResolution
deriving instance ReflBEq, LawfulBEq for ExpressionId
deriving instance ReflBEq, LawfulBEq for StatementId
deriving instance ReflBEq, LawfulBEq for TypedMatchCase
deriving instance ReflBEq, LawfulBEq for MatchResolution
deriving instance ReflBEq, LawfulBEq for PlaceProjection
deriving instance ReflBEq, LawfulBEq for PlaceResolution
deriving instance ReflBEq, LawfulBEq for AssignmentResolution
deriving instance ReflBEq, LawfulBEq for ForItemForm
deriving instance ReflBEq, LawfulBEq for NodeId
deriving instance ReflBEq, LawfulBEq for ExpressionForm
deriving instance ReflBEq, LawfulBEq for ExpressionNode
deriving instance ReflBEq, LawfulBEq for StatementForm
deriving instance ReflBEq, LawfulBEq for StatementNode
deriving instance ReflBEq, LawfulBEq for Node
deriving instance ReflBEq, LawfulBEq for TypedSource
deriving instance ReflBEq, LawfulBEq for PredicateEvidence
deriving instance ReflBEq, LawfulBEq for SolvedRequirement
deriving instance ReflBEq, LawfulBEq for CheckedFunction
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.Stage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.ExpressionStage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.BinderStage
deriving instance ReflBEq, LawfulBEq for SourceStageAnalysis.Analysis
deriving instance ReflBEq, LawfulBEq for SourceSpecialization.SpecializationKey
deriving instance ReflBEq, LawfulBEq for SourceSpecialization.SpecializedFunction

theorem eq_of_beq {left right : SourceSpecialization.SpecializedFunction}
    (same : (left == right) = true) : left = right := by
  exact LawfulBEq.eq_of_beq same

end Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
