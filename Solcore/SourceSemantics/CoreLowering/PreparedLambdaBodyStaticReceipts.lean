import Solcore.SourceSemantics.CoreLowering.EmittedMatchCatalogCoupledExtraction
import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites

/-! Exact compiler trees keep their original occurrence evidence. The prepared
alternative interprets only authentic operand and unary tokens; projection
failures remain indexed by the actual reached state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
open Core Frontend SourceInference
open GenericImperativeMatch

/-- Only original value-assignment occurrences request an operand token law. -/
def OperandLaw (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {site assignment operator rhs},
    AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
    (operator = .equal ∨ assignment.target.type = .word) →
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (invalidOperand site assignment.target.root operator)

/-- Original unary occurrences retain their actual diagnostic token. -/
def UnaryLaw (source : TypedSource)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
    assignment.target.type = .word →
    faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- The tree is fixed before a receiving registry or fault interpretation is
chosen. Place diagnostics retain preparation instead of a uniform fault law. -/
structure PreparedExtraction
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope position expected type code
  sites : ∀ registry faults, OperandLaw source invalidOperand faults → UnaryLaw source invalidUnary faults →
    PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault registry faults tree


end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
