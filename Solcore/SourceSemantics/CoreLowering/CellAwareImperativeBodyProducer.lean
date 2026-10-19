import Solcore.SourceSemantics.CoreLowering.CellAwareNamedInitializerProfiles
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeCollectors
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyProducer

/-! The selected named body obtains its bounded mixed-cell tree from its
original accepted compiler action. All row checks inspect the unchanged local
catalog; native child typing comes from the enclosing actual body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source context)
open CompatibleEncoding (bind_ok)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

def policy : SourceCoreLoops.Policy :=
  AcceptedNamedBodyFlow.namedPolicy prepared named diagnostics compiled.parents compiled.own

def scope (named : SourceCoreGeneralFunctions.Function) : SourceCoreLocalCell.Scope :=
  named.inputs.reverse.map fun binding => (binding.1.id, binding.2)

structure StaticProfile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (approved : ExpressionId → Prop) (expected : TypeSystem.Ty) : Type where
  initializers : CellAwareNamedInitializerProfiles.Rows prepared named prepared.base.locals.bindings
  scan : CellAwareImperativeSourceBodyAdmission.Scan prepared.base.locals named.signature.key [] (source named)
    approved expected true statements

def staticProfile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    Option (StaticProfile prepared named statements approved expected) := do
  let ⟨initializers⟩ ← CellAwareNamedInitializerProfiles.rows? prepared named prepared.base.locals.bindings
  let ⟨scan⟩ ← CellAwareImperativeSourceBodyAdmission.scan? prepared.base.locals named.signature.key []
    (source named) expression expected prepared.fuel true statements
  pure ⟨initializers, scan⟩

structure Body (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (sourceContext : SourceSemantics.Context) (expected : TypeSystem.Ty) where
  flow : Expr
  tree : CellAwareImperativeTree.Tree prepared named compiled certificates administrative
    (diagnostics.reasonAt named.signature.key) sourceContext (scope named) true compiled.statements
    expected named.signature.resultType flow
  emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
    compiled.own.fellThroughReason compiled.own.table.escapedReason

/-- The public-facing static producer consumes checker facts and actual native
body typing; terminal certificates remain static compiler receipts. -/
theorem of_static_compilation
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {approved : ExpressionId → Prop} {expected : TypeSystem.Ty}
    (profile : StaticProfile prepared named compiled.statements approved expected)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {administrative : Core.Context}
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      (policy compiled).lowerExpression fuel (source named) scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) (scope named) sourceContext)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (Body compiled certificates administrative sourceContext expected) := by
  have accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy compiled) prepared.fuel (source named)
      (scope named) compiled.statements named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compiled.own.fellThroughReason compiled.own.table.escapedReason = .ok compiled.body := compiled.bodyCompiled
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := bind_ok accepted
  have emitted : compiled.body = CompatibleStatements.finish named.signature.resultType flow
      compiled.own.fellThroughReason compiled.own.table.escapedReason := (Except.ok.inj emitted).symm
  rw [emitted] at nativeTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  have tree := CellAwareImperativeCollectors.collected compiled record rfl rfl (by
    intro scope binder mono
    simp only [policy, AcceptedNamedBodyFlow.namedPolicy, SourceCoreGeneralFunctions.contextualBinder,
      mono, List.isEmpty_nil, ↓reduceIte]
    rfl) rfl
    (CellAwareNamedInitializerProfiles.Rows.at_site compiled _ profile.initializers)
    (CellAwareNamedInitializerProfiles.Rows.bodies_at_site compiled _ profile.initializers)
    children (profile.scan.syntax unique result typed) declarations generated flowTyped
  exact ⟨⟨flow, tree, emitted⟩⟩

abbrev Profile (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :=
  StaticProfile prepared named statements (CellAwareNamedExpressionSyntax.Syntax prepared named (source named)) expected

def profile? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) (expected : TypeSystem.Ty) :
    Option (Profile prepared named statements expected) :=
  staticProfile? prepared named statements
    (CellAwareNamedExpressionSyntax.syntax? prepared named (source named) prepared.fuel) expected

abbrev Certificate (compiled : Compilation prepared named diagnostics code)
    (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  CellAwareNamedBodyProducer.Certificate compiled sourceContext

/-- Actual expression compiler receipts close every child certificate of the
common mixed body. Only the original static typing and accepted body remain. -/
theorem of_compilation
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {expected : TypeSystem.Ty} (profile : Profile prepared named compiled.statements expected)
    (unique : NodeOccurrencesUnique (source named))
    {control : ControlContext} (result : control.returnType = expected)
    {sourceContext final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType (source named) control sourceContext compiled.statements final facts)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) (scope named) sourceContext)
    {administrative : Core.Context} {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext (scope named) ++ administrative)
      compiled.body nativeType prepared.layouts.definitions) :
    Nonempty (Body compiled (Certificate compiled) administrative sourceContext expected) := by
  apply of_static_compilation compiled record profile ?_ unique result typed declarations nativeTyped
  intro childContext childScope fuel id node lowered childDeclarations syntaxTree found childTyped accepted _ _
  exact CellAwareNamedBodyProducer.expression compiled record syntaxTree unique childDeclarations found childTyped accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer
