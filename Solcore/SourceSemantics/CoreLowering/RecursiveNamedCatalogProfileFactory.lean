import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForCertificates

/-! Native body typing is supplied from the cached lambda at the actual entry.
The existing single compiler traversal supplies the same Tree and its precise
residual diagnostic predicate. Source syntax, child certificates, assignment
child native typing and residual diagnostic interpretation remain explicit.
No body execution or recursive meaning is stored in a receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy}

structure Receipt (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  extracted : GenericImperativeFor.DiagnosticExtraction diagnosticPolicy header.layouts header.owner header.active
    prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax
    (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.context (bodyScope header)
    (.statements true header.function.body) header.function.resultType header.output flow

/-- Interpret only the predicate of the returned extraction, rather than all
arbitrary receipts with the same code. -/
def Receipt.profile
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults :=
  receipt.extracted.catalog_profile receipt.accepted receipt.projection receipt.generated interpreted

variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Actual cached output typing and a checked support bound remove the whole
body/native-loop typing premise at this entry. All static child/source and
remaining diagnostic obligations are visible in this interface. -/
theorem extract_with_residual (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = residualMode)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  have typed := canonical_cached complete globals cachedTyped support entry
  obtain ⟨flow, generated, extracted, _⟩ := GenericImperativeFor.extraction_of_typed_body_with_residual residualMode diagnosticPolicy factory
    readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy header.unique assignmentExpressions
    syntaxTree closed residual sourceSignatures declarations projection accepted typed
  exact ⟨⟨accepted, projection, flow, generated, extracted⟩⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem extract (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (closed : header.context.typeVariables = []) (residual : header.context.residualTypeVariables = false)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual false (diagnosticPolicy := diagnosticPolicy) (tracked := tracked) (factory := factory)
    (readPolicy := readPolicy) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (expressions := expressions) (assignments := assignments) (unaryPolicy := unaryPolicy)
    (assignmentExpressions := assignmentExpressions) (syntaxTree := syntaxTree) (closed := closed)
    (residual := residual) (sourceSignatures := sourceSignatures) (declarations := declarations)
    (projection := projection) (accepted := accepted) (suffix := suffix) (cachedTyped := cachedTyped)
    (support := support) (complete := complete) (globals := globals) (entry := entry)

/-- Use the real source declaration context; its residual flag is derived
from structural instantiation and the actual monomorphic parameters. -/
theorem extract_source (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) lowered.expression
          (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    {suffix : Core.Context}
    (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType ambient.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
    (complete : Complete headers) (globals : header.globals = base.globals.length)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_with_residual true (diagnosticPolicy := diagnosticPolicy) (tracked := tracked) (factory := factory)
    (readPolicy := readPolicy) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (expressions := expressions) (assignments := assignments) (unaryPolicy := unaryPolicy)
    (assignmentExpressions := assignmentExpressions) (syntaxTree := syntaxTree)
    (closed := RecursiveNamedSourceContextFacts.header_typeVariables header)
    (residual := RecursiveNamedSourceContextFacts.header_residual header) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (projection := projection) (accepted := accepted) (suffix := suffix)
    (cachedTyped := cachedTyped) (support := support) (complete := complete) (globals := globals) (entry := entry)

/-- A state-indexed returned receipt plus its own residual interpretation is
exactly the static provider consumed by mutual body induction. There is no
request for profiles at an unreachable arbitrary administrative context. -/
def Receipt.provider
    (receipts : ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost},
      BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    {faults : FunctionCalls.FaultRep}
    (interpreted : ∀ {arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost}
      (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost),
      (receipts entry).extracted.diagnostics registry faults)
    (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) :
    ProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults :=
  (receipts entry).profile (interpreted entry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfileFactory
