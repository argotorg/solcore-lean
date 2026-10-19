import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionCollectors
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer

/-! The bounded named profile fills every terminal compiler receipt from its
actual accepted expression action. Its public construction has no expression
certificate callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  CellAwareNamedBodySupport.Profile prepared named statements
    (CellAwareMaterializedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  CellAwareNamedBodySupport.profile? prepared named statements
    (CellAwareMaterializedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

def Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ rootFuel,
    CellAwareMaterializedExpressionCertificates.Tree compiled rootFuel (source named) sourceContext
      (diagnostics.reasonAt named.signature.key) scope id lowered

theorem Certificate.ordinary {compiled : Compilation prepared named diagnostics code}
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate compiled sourceContext scope id lowered) :
    CellAwareNamedBodyProducer.Certificate compiled sourceContext scope id lowered := by
  obtain ⟨fuel, tree⟩ := receipt
  exact ⟨fuel, tree.ordinary⟩

theorem expression (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (syntaxTree : CellAwareMaterializedExpressionSyntax.Syntax prepared named (source named) id)
    (unique : NodeOccurrencesUnique (source named))
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext)
    (found : (source named).lookupExpression? id = some node)
    (typed : ExpressionHasType (source named) sourceContext id node.type)
    (accepted : (CellAwareNamedBodySupport.policy compiled).lowerExpression fuel (source named)
      scope id (diagnostics.reasonAt named.signature.key) = .ok lowered) :
    Certificate compiled sourceContext scope id lowered := by
  change SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
    diagnostics (context prepared named) prepared.base.callableContext none none fuel
    (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered at accepted
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual compiled record] at accepted
    exact ⟨fuel, CellAwareMaterializedExpressionCollectors.of_policy compiled fuel syntaxTree unique
      declarations found typed accepted⟩

theorem of_compilation (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named)
      (CellAwareNamedBodySupport.scope named) sourceContext)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (CellAwareNamedBodySupport.scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (CellAwareNamedBodySupport.Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply CellAwareNamedBodySupport.of_compilation compiled record profile ?_ unique result typed declarations nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedBodyProducer
