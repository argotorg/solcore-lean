import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates

/-! The real contextual lambda producer retains its body recipe before the
ordinary Site forgets it. The compatible representation's loop policy then
supplies the expression callback and statement reader by construction. Its
actual lambda body receipt supplies terminal acceptance. There is no callback
equality, original body acceptance, or execution law in the public producer's
inputs. Raw Source typing, original policy coverage and reached-call authority
remain separate at the original selected parameter context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration

/-- The concrete marked representation preserves the supplied expression
callback through its allocator and ancestry updates. -/
def loop_policy {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) : SourceCoreLoops.Policy :=
  let actual := (representation prepared).atContext named.signature.key []
  { actual.loopsWithSourceCells actual.expressions.sourceCells
      (context prepared named).solvedRequirements assignments diagnostics
      (context prepared named).owner expression with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder
      actual prepared.base.locals named.signature.key [] }

theorem expression_callback {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    (loop_policy prepared named assignments diagnostics expression).lowerExpression = expression := by
  rfl

theorem statement_reader {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    (loop_policy prepared named assignments diagnostics expression).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement checked := by
  rfl

/-- The actual production body lowerer uses that same concrete loop policy. -/
theorem body_lowerer {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked) (named : Named)
    (assignments : SourceCoreAssignmentFaultSites.Table)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program)
    (expression : SourceCoreFunctions.ExpressionLowerer) :
    SourceCoreGeneralFunctions.bodyLowererWithRepresentation
      ((representation prepared).atContext named.signature.key [])
      (context prepared named).solvedRequirements assignments diagnostics
      (context prepared named).owner
      (SourceCoreGeneralFunctions.contextualBinder
        ((representation prepared).atContext named.signature.key [])
        prepared.base.locals named.signature.key []) expression =
      SourceCoreLoops.lowerStatementsWithPolicy
        (loop_policy prepared named assignments diagnostics expression) := by
  rfl

/-- The retained body recipe belongs to the same chosen compiler Site. This
is a static compiler packet, not a called-body meaning certificate. -/
structure Produced (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : Named) (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment) (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : CallableIndexedLambdaGeneration.Site compiled.indexed named parameters result statements
    sourceContext evidence captured scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binder : site.code.policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((representation compiled.indexed).atContext named.signature.key [])
    compiled.indexed.base.locals named.signature.key []
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation site.code
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  callback : site.code.lowerBody
      (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy
      (loop_policy compiled.indexed named compilation.own.assignments diagnostics
        (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))

/-- Run the checked original contextual producer once and keep its exact body
recipe. In particular, the callback field is constructed from compiler success. -/
theorem of_contextual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {statements : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (captured : Dynamic.Environment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (Produced compiled named diagnostics namedCode compilation parameters result statements
      sourceContext evidence captured scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binder, recipe, compilerPolicy⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_policy_recipe compiled.indexed
      compilation record sourceContext evidence captured profile viewOfSource sourceFound sourceForm
      found form owner requirements coercions ordinary read accepted typed
  refine ⟨{
    site := site
    identifier := identifier
    emitted := emitted
    binder := binder
    recipe := recipe
    compilerPolicy := compilerPolicy
    callback := ?_ }⟩
  have applied := congrArg
    (fun body : SourceCoreFunctions.BodyLowerer =>
      body (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))
    recipe
  exact applied.trans (body_lowerer compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation))

section Terminal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {captured : Dynamic.Environment} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced compiled named diagnostics namedCode compilation parameters result statements
    sourceContext evidence captured scope administrative id lowered)

/-- The production callback and real body receipt construct the terminal
packet directly. No arbitrary BodyWith policy is replaced or inferred. -/
theorem terminal {stages : Staging.Recursive.Registry} (expression : ExpressionId)
    (shape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      produced.site.code.view expression statements)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (CallableIndexedLambdaGeneration.closure named parameters result statements
        sourceContext evidence captured) child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
        produced.site.code stages,
      packet.policy.lowerExpression = FunctionCode.children produced.site.code.policy
        produced.site.code.lowerBody produced.site.code.fuel produced.site.code.compilation ∧
      packet.reasonAt = produced.site.code.reasonAt ∧ packet.child = child ∧
      packet.expression = expression ∧
      packet.certificate = CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
        (produced.site.code.receipt.loweredParameters.reverse.map
          (fun binding => (binding.1.id, binding.2)) ++ scope) expression packet.receipt.child := by
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
      produced.site.code.fuel produced.site.code.compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    produced.site.code policy produced.callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (statement_reader compiled.indexed named compilation.own.assignments diagnostics
      (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
        produced.site.code.fuel produced.site.code.compilation)) shape accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal
      produced.site.code stages := {
    policy := policy
    fuel := produced.site.code.fuel
    expression := expression
    reasonAt := produced.site.code.reasonAt
    fellThrough := produced.site.code.compilation.internalReason
    escaped := produced.site.code.compilation.internalReason
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.Point
      (produced.site.code.receipt.loweredParameters.reverse.map
        (fun binding => (binding.1.id, binding.2)) ++ scope) expression receipt.child
    certifies := by
      intro actual generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  exact ⟨packet, expression_callback compiled.indexed named compilation.own.assignments diagnostics
    (FunctionCode.children produced.site.code.policy produced.site.code.lowerBody
      produced.site.code.fuel produced.site.code.compilation), rfl, rfl, rfl, rfl⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
