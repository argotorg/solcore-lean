import Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors

/-! The bounded named profile fills every terminal compiler receipt from its
actual accepted expression action. Its public construction has no expression
certificate callback. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  CellAwareLexicalNamedBodySupport.Profile prepared named statements
    (CellAwareNamedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  CellAwareLexicalNamedBodySupport.profile? prepared named statements
    (CellAwareNamedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

abbrev Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  CellAwareNamedBodyProducer.Certificate compiled sourceContext

theorem of_compilation (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named)
      (CellAwareLexicalNamedBodySupport.scope named) sourceContext)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (CellAwareLexicalNamedBodySupport.scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (CellAwareLexicalNamedBodySupport.Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply CellAwareLexicalNamedBodySupport.of_compilation compiled record profile ?_ unique result typed declarations nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact CellAwareNamedBodyProducer.expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalNamedBodyProducer
