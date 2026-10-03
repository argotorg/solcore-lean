import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeMatchProfiles
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates

/-! Runtime profiles are extracted from the actual cached body at its actual
entry. One existing compiler traversal produces the same Tree and residual
diagnostic predicate. Full signature/ledger fields are transported through
actual source binders without using ordinary all-row validity. Expression,
assignment and match static receipts remain explicit; no execution law or
profile callback is a compiler premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport
open GenericImperativeMatch GenericImperativeMatch.Tree

section Sites
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

private theorem pattern_fields {compilation : SourceCoreCompatibleDataMatches.Context}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    (ledger : context.solvedRequirements = solved)
    (signatures : context.signatures = values.checked.signatures)
    (sameValues : compilation.values = values) (sameLedger : compilation.solvedRequirements = solved) :
    MatchContextFields compilation context := by
  refine ⟨?_, ledger.trans sameLedger.symm⟩
  simpa only [SourceCoreCompatibleDataMatches.Context.signatures,
    SourceCoreCompatibleDataMatches.Context.checked, sameValues] using signatures

private theorem scoped_ledger {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)}
    {request : GenericMatchChildren.Request} {solved : List SolvedRequirement}
    (related : GenericMatchChildren.ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child)
    (ledger : parent.solvedRequirements = solved) : child.solvedRequirements = solved := by
  cases related with
  | arm _ _ _ extended _ =>
    exact (Dynamic.BindersExtend.runtimeContextFields extended).solvedRequirements.trans ledger
  | default => exact ledger

/-- This fold is indexed by the returned diagnostic tree. It transports only
complete field equality and retains each original ordered child occurrence. -/
theorem catalog_sites (catalog : SignatureCatalogWellFormed values.checked.signatures) {diagnosticPolicy : AssignmentDiagnosticPolicy} {solved : List SolvedRequirement}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    {errors : ErrorsFor diagnosticPolicy registry faults tree}
    (ledgers : SiteLedgersFor diagnosticPolicy solved registry faults errors) :
    context.solvedRequirements = solved →
    context.signatures = values.checked.signatures → CatalogSites diagnosticPolicy registry faults tree := by
  induction ledgers with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro valid signatures
    exact @CatalogSites.body layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode statements expected type code syntaxTree body
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.uninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining (remainingErrorsIH ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans valid) (extended.context_fields.1.trans signatures))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining (remainingErrorsIH ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans valid) (extended.context_fields.1.trans signatures))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.discard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining (remainingErrorsIH valid signatures)
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsLedger remainingErrorsLedger innerErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.block layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node statements rest expected type innerCode body found form inner remaining (innerErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsLedger elseTreeErrorsLedger remainingErrorsLedger thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.ifThen layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining (thenTreeErrorsIH valid signatures) (elseTreeErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @breaking context scope mode id node rest expected type found form =>
    intro valid signatures
    exact @CatalogSites.breaking layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @continuing context scope mode id node rest expected type found form =>
    intro valid signatures
    exact @CatalogSites.continuing layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node rest expected type found form
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsLedger remainingErrorsLedger loopBodyErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.whileLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining (loopBodyErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.assign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment operator rhs rest expected type body found form head remaining (remainingErrorsIH valid signatures) headErrors
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.bitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node assignment rest expected type body found form head remaining (remainingErrorsIH valid signatures) headErrors
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsLedger remainingErrorsLedger initialErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.forLoop layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining (initialErrorsIH valid signatures) (remainingErrorsIH valid signatures)
  | @initializersDone context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsLedger loopErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializersDone layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped (loopErrorsIH valid signatures) postErrors
  | @initializerUninitialized context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializerUninitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining (remainingErrorsIH ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans valid) (extended.context_fields.1.trans signatures))
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializerInitialized layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining (remainingErrorsIH ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans valid) (extended.context_fields.1.trans signatures))
  | @initializerDiscard context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializerDiscard layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope expression expressionNode rest lowered body condition post statements expected type found value remaining (remainingErrorsIH valid signatures)
  | @initializerAssign context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializerAssign layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment operator rhs rest body condition post statements expected type head remaining (remainingErrorsIH valid signatures) headErrors
  | @initializerBitNot context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsLedger remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.initializerBitNot layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope assignment rest body condition post statements expected type head remaining (remainingErrorsIH valid signatures) headErrors
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining childErrors remainingErrors sameLedger childLedgers remainingErrorsLedger childErrorsIH remainingErrorsIH =>
    intro valid signatures
    exact @CatalogSites.matchWith layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog (pattern_fields valid signatures sameValues sameLedger) (fun request member childContext related => childErrorsIH request member childContext related (scoped_ledger related valid) (related.closed_fields.1.trans signatures)) (remainingErrorsIH valid signatures)

  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerLedger innerIH =>
    intro valid signatures
    exact .terminalBlock (unique := unique) (found := found) (form := form) (stops := stops) (issued := issued) (innerIH valid signatures)
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenLedger elseLedger thenIH elseIH =>
    intro valid signatures
    exact .terminalIf (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (thenIH valid signatures) (elseIH valid signatures)

  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued childErrors sameLedger childLedgers childrenIH =>
    intro valid signatures
    exact @CatalogSites.terminalMatch layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative diagnosticPolicy registry faults context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued
      catalog (pattern_fields valid signatures sameValues sameLedger)
      (fun request member childContext related => childrenIH request member childContext related
        (scoped_ledger related valid) (related.closed_fields.1.trans signatures))


end Sites

section Factory
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- The fields describe this compiler invocation and its reached static children.
None is a body/expression execution law or an arbitrary profile. -/
structure Inputs (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand
  matchPolicy : header.policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation)
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = ambient.definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError))
  matchLedger : matchCompilation.solvedRequirements = header.solved
  matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation header.function.source
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative
  readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder
  allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
    header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions
  syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
    (.statements true header.function.body) header.function.resultType
  sourceSignatures : header.context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body

structure Receipt (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  signatures : header.context.signatures = values.checked.signatures
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  extracted : GenericImperativeMatch.ExtractionFor diagnosticPolicy header.layouts header.owner header.active
    prepared.layout.frame header.globals header.onError values header.function.source expressionSyntax
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.solved header.context (bodyScope header)
    (.statements true header.function.body) header.function.resultType header.output flow

/-- The complete Header validity is used only in its forward runtime form.
Interpretation refers to the exact returned diagnostic predicate. -/
def Receipt.profile
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults := by
  have sites : CatalogSites diagnosticPolicy registry faults receipt.extracted.tree := by
    obtain ⟨errors, ledgers⟩ := receipt.extracted.materialize registry faults interpreted
    exact catalog_sites catalog ledgers header.valid.ledger receipt.signatures
  exact RuntimeMatchProfileFor.of_extracted header.valid receipt.accepted receipt.projection receipt.generated
    receipt.extracted.tree sites

variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include inputs cachedTyped support complete globals entry in
/-- Real cached typing is transported to the actual pack-plus-administrative
entry. The existing single compiler traversal supplies every body node. -/
theorem extract_source :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  have typed := canonical_cached complete globals cachedTyped support entry
  obtain ⟨flow, generated, extracted, _⟩ := GenericImperativeMatch.extraction_of_typed_body_with_residual true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    header.unique inputs.assignmentExpressions inputs.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    inputs.sourceSignatures inputs.declarations inputs.projection inputs.accepted typed
  rw [inputs.matchLedger] at extracted
  exact ⟨⟨inputs.accepted, inputs.projection, inputs.sourceSignatures, flow, generated, extracted⟩⟩

include inputs cachedTyped support complete globals entry in
/-- Pointwise provider for mutual body induction. The chosen static receipt
stays inside this proposition. Interpretation concerns only its own returned
diagnostics, and materialization preserves that receipt's exact flow and Tree. -/
theorem provider (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree := by
  obtain ⟨result⟩ := extract_source inputs cachedTyped support complete globals entry
  exact ⟨result, fun faults interpreted => ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩⟩
end Factory

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
