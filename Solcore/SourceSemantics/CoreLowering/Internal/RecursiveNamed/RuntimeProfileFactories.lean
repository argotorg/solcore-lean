import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.EmittedDiagnosticTokenPlan
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.CoreContinuationSize

/-!
# Recursive named rows: runtime profile factories

Factories of catalog runtime profiles, with the emitted and token variants, the certificates of emitted imperative matches, and the prepared initialization and header policies they read.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedImperativeMatchTokenCertificates
/-! The same emitted flow and native finish receipts retain actual token
provenance beside the original diagnostic plan and static traversal. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

variable {matchCompilation : SourceCoreCompatibleDataMatches.Context}
variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem extraction_of_typed_body_with_tokens (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : TokenExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  obtain ⟨extracted⟩ := extraction_of_typed_position_with_tokens residualMode diagnosticPolicy factory matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions
    assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection generated flowTyped
  exact ⟨flow, generated, extracted, rfl⟩


end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
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
  {administrative : Core.Context} {authenticated : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- The fields describe this compiler invocation and its reached static children.
None is a body/expression execution law or an arbitrary profile. -/
structure InputsFor (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate) (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (header : Header prepared values ambient.definitions program)
    (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess header.policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = ambient.definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError))
  matchLedger : matchCompilation.solvedRequirements = header.solved
  matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation header.function.source
    certificates
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
    certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions
  syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
    (.statements true header.function.body) header.function.resultType
  sourceSignatures : header.context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body


structure InputsWith (authenticated : Bool) (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
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
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess header.policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = ambient.definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError))
  matchLedger : matchCompilation.solvedRequirements = header.solved
  matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation header.function.source
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
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
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions
  syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
    (.statements true header.function.body) header.function.resultType
  sourceSignatures : header.context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context
  projection : values.checked.catalog.project header.function.resultType = .ok header.output
  accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body

/-- Every legacy field belongs to the exact same static expression family. -/
def InputsWith.to_for {tracked : Bool}
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative) :
    InputsFor (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
      (if authenticated then some header.function.evidence else none) headers compilation header.readFuel
      header.function.source context header.solved header.reasonAt) tracked diagnosticPolicy header expressionSyntax administrative := by
  rcases inputs with ⟨matchCompilation, invalidProjection, invalidOperand, invalidUnary, missingDefault,
    factory, matchPolicy, matchValues, matchDefinitions, matchAllocator, matchLedger, matchChildStatic,
    readPolicy, binderPolicy, allocationPolicy, expressions, assignments, unaryPolicy, assignmentExpressions,
    syntaxTree, sourceSignatures, declarations, projection, accepted⟩
  exact ⟨matchCompilation, invalidProjection, invalidOperand, invalidUnary, missingDefault,
    factory, matchPolicy, matchValues, matchDefinitions, matchAllocator, matchLedger, matchChildStatic,
    readPolicy, binderPolicy, allocationPolicy, expressions, assignments, unaryPolicy, assignmentExpressions,
    syntaxTree, sourceSignatures, declarations, projection, accepted⟩


abbrev Inputs (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) :=
  InputsWith false tracked diagnosticPolicy headers header compilation expressionSyntax administrative

/-- Exact-policy compatibility constructor. The same fields are retained;
only its policy equality is used as an identity success transport. -/
def InputsWith.of_exact (authenticated : Bool) (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context)
    (matchCompilation : SourceCoreCompatibleDataMatches.Context)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (matchPolicy : header.policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = ambient.definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError)))
    (matchLedger : matchCompilation.solvedRequirements = header.solved)
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation header.function.source
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative)
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
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
    (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body) :
    InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative where
  matchCompilation := matchCompilation
  invalidProjection := invalidProjection
  invalidOperand := invalidOperand
  invalidUnary := invalidUnary
  missingDefault := missingDefault
  factory := factory
  matchPolicy := CompatibleMatchAmbientLowering.PolicySuccess.of_eq matchPolicy
  matchValues := matchValues
  matchDefinitions := matchDefinitions
  matchAllocator := matchAllocator
  matchLedger := matchLedger
  matchChildStatic := matchChildStatic
  readPolicy := readPolicy
  binderPolicy := binderPolicy
  allocationPolicy := allocationPolicy
  expressions := expressions
  assignments := assignments
  unaryPolicy := unaryPolicy
  assignmentExpressions := assignmentExpressions
  syntaxTree := syntaxTree
  sourceSignatures := sourceSignatures
  declarations := declarations
  projection := projection
  accepted := accepted

def Inputs.of_exact (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context)
    (matchCompilation : SourceCoreCompatibleDataMatches.Context)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (matchPolicy : header.policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = ambient.definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame header.globals
    (header.layouts.allocatorAt header.owner header.active header.onError)))
    (matchLedger : matchCompilation.solvedRequirements = header.solved)
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation header.function.source
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative)
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
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
    (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
    (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body) :
    Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative :=
  InputsWith.of_exact false tracked diagnosticPolicy headers header compilation expressionSyntax administrative matchCompilation invalidProjection invalidOperand invalidUnary missingDefault factory matchPolicy matchValues matchDefinitions matchAllocator matchLedger matchChildStatic readPolicy binderPolicy allocationPolicy expressions assignments unaryPolicy assignmentExpressions syntaxTree sourceSignatures declarations projection accepted

structure ReceiptFor (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (header : Header prepared values ambient.definitions program)
    (expressionSyntax : ExpressionId → Prop)
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
    certificates
    ambient.definitions administrative header.solved header.context (bodyScope header)
    (.statements true header.function.body) header.function.resultType header.output flow


structure ReceiptWith (authenticated : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
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
    (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source context header.solved header.reasonAt)
    ambient.definitions administrative header.solved header.context (bodyScope header)
    (.statements true header.function.body) header.function.resultType header.output flow

def ReceiptWith.to_for
    (receipt : ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative) :
    ReceiptFor (fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
      (if authenticated then some header.function.evidence else none) headers compilation header.readFuel
      header.function.source context header.solved header.reasonAt) diagnosticPolicy header expressionSyntax administrative :=
  ⟨receipt.accepted, receipt.projection, receipt.signatures, receipt.flow, receipt.generated, receipt.extracted⟩


abbrev Receipt (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) :=
  ReceiptWith false diagnosticPolicy headers header compilation expressionSyntax administrative

/-- The complete Header validity is used only in its forward runtime form.
Interpretation refers to the exact returned diagnostic predicate. -/
def ReceiptFor.profile
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (receipt : ReceiptFor certificates diagnosticPolicy header expressionSyntax administrative)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    MatchProfileWith (fun context => CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence) certificates
      diagnosticPolicy header expressionSyntax administrative registry faults := by
  have sites : CatalogSites diagnosticPolicy registry faults receipt.extracted.tree := by
    obtain ⟨errors, ledgers⟩ := receipt.extracted.materialize registry faults interpreted
    exact catalog_sites catalog ledgers header.valid.ledger receipt.signatures
  exact MatchProfileWith.of_extracted header.valid receipt.accepted receipt.projection receipt.generated
    receipt.extracted.tree sites

def ReceiptWith.profile
    (receipt : ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults :=
  receipt.to_for.profile catalog interpreted

def Receipt.profile
    (receipt : Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults :=
  ReceiptWith.profile receipt catalog interpreted

section GenericFactory
variable {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include cachedTyped support complete globals entry in
/-- One actual body traversal serves every static expression certificate family. -/
theorem extract_source_for
    (inputs : InputsFor certificates tracked diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (ReceiptFor certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  have typed := canonical_cached complete globals cachedTyped support entry
  obtain ⟨flow, generated, extracted, _⟩ := GenericImperativeMatch.extraction_of_typed_body_with_lowering true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    header.unique inputs.assignmentExpressions inputs.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    inputs.sourceSignatures inputs.declarations inputs.projection inputs.accepted typed
  rw [inputs.matchLedger] at extracted
  exact ⟨⟨inputs.accepted, inputs.projection, inputs.sourceSignatures, flow, generated, extracted⟩⟩

end GenericFactory

variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
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
theorem extract_source_with :
    Nonempty (ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  obtain ⟨result⟩ := extract_source_for cachedTyped support complete globals entry inputs.to_for
  exact ⟨⟨result.accepted, result.projection, result.signatures, result.flow, result.generated, result.extracted⟩⟩

include inputs cachedTyped support complete globals entry in
/-- Pointwise provider for mutual body induction. The chosen static receipt
stays inside this proposition. Interpretation concerns only its own returned
diagnostics, and materialization preserves that receipt's exact flow and Tree. -/
theorem provider_with (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        ∃ profile : RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation header.readFuel expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree := by
  obtain ⟨result⟩ := extract_source_with inputs cachedTyped support complete globals entry
  exact ⟨result, fun faults interpreted => ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩⟩
omit inputs cachedTyped support complete globals entry in
theorem extract_source (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
 :
    Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :=
  extract_source_with inputs cachedTyped support complete globals entry

omit inputs cachedTyped support complete globals entry in
theorem provider (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)
 (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  provider_with inputs cachedTyped support complete globals entry catalog

end Factory

section Formation
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {header : Header indexed.ancestry values indexed.layouts.definitions program}
  {expressionSyntax : ExpressionId → Prop} {administrative suffix : Core.Context}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked authenticated : Bool} {locations : Locations}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}

abbrev FormationCertificates (authenticated : Bool)
    (header : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) :=
  RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := header) (headers := headers)
    (context := context) (evidence := header.function.evidence) (registry := registry) (faults := faults)
    (fuel := header.readFuel) (solved := header.solved) (reasonAt := header.reasonAt) authenticated

abbrev FormationInputs (authenticated tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (header : Header indexed.ancestry values indexed.layouts.definitions program)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context) :=
  InputsFor (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
    (FormationCertificates (headers := headers) (registry := registry) (faults := faults) authenticated header)
    tracked diagnosticPolicy header expressionSyntax administrative

abbrev FormationReceipt (authenticated : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (header : Header indexed.ancestry values indexed.layouts.definitions program)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context) :=
  ReceiptFor (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
    (FormationCertificates (headers := headers) (registry := registry) (faults := faults) authenticated header)
    diagnosticPolicy header expressionSyntax administrative

/-- Static children are constructed at this actual aligned parameter result.
The complete cached code and its finite support still provide whole-body typing. -/
theorem formation_provider
    (profile : values.checked.catalog.callableContracts = true)
    (entry : BodyState (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers locations 0
      (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header
      arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost)
    (aligned : RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed)
      (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry)
    (inputs : RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed)
      (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry →
      FormationInputs (headers := headers) (registry := registry) (faults := faults) authenticated tracked diagnosticPolicy header expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    (cachedTyped : HasType (indexed.base.globals.map (·.referenceType) ++ .cell indexed.ancestry.layout.frame.type :: suffix)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType indexed.layouts.definitions)
    (support : supported (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) (indexed.base.globals.length + 1) = true)
    (complete : Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : header.globals = indexed.base.globals.length)
    (catalog : SignatureCatalogWellFormed values.checked.signatures) :
    ∃ result : FormationReceipt (headers := headers) (registry := registry) (faults := faults) authenticated diagnosticPolicy header expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      result.accepted = (inputs aligned).accepted ∧ result.projection = (inputs aligned).projection ∧
      ∀ observedFaults : FunctionCalls.FaultRep, result.extracted.diagnostics registry observedFaults →
        ∃ profile : MatchProfileWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
            (fun context => CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence)
            (FormationCertificates (headers := headers) (registry := registry) (faults := faults) authenticated header)
            diagnosticPolicy header expressionSyntax
            (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry observedFaults,
          profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree := by
  obtain ⟨result⟩ := extract_source_for cachedTyped support complete globals entry (inputs aligned)
  exact ⟨result, Subsingleton.elim _ _, Subsingleton.elim _ _,
    fun observedFaults interpreted => ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩⟩
end Formation

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedEmittedTokenRuntimeProfileFactory
/-! Actual cached Header extraction retains unary token provenance beside
the diagnostic plan generated by its original compiler traversal. The complete
receipt and own diagnostic equation belong to this actual parameter entry. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {authenticated : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include cachedTyped support complete globals entry in
/-- The actual cached entry selects the original static traversal, retaining
its genuine emitted diagnostics rather than an arbitrary receipt predicate. -/
theorem extract_source_for_with_tokens
    (inputs : InputsFor certificates tracked diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (EmittedDiagnosticTokenPlan.Produced inputs.factory inputs.invalidUnary
      (ReceiptFor certificates diagnosticPolicy header expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (fun receipt => receipt.extracted.diagnostics)) := by
  have typed := canonical_cached complete globals cachedTyped support entry
  obtain ⟨flow, generated, produced, _⟩ := GenericImperativeMatch.extraction_of_typed_body_with_tokens true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    header.unique inputs.assignmentExpressions inputs.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    inputs.sourceSignatures inputs.declarations inputs.projection inputs.accepted typed
  rw [inputs.matchLedger] at produced
  exact ⟨⟨⟨⟨inputs.accepted, inputs.projection, inputs.sourceSignatures, flow, generated, produced.original⟩,
    produced.plan, produced.equation⟩, produced.tokens⟩⟩

include cachedTyped support complete globals entry in
/-- The existing runtime certificate specialization preserves the whole
actual emitted receipt and its exact diagnostic plan. -/
theorem extract_source_with_tokens
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (EmittedDiagnosticTokenPlan.Produced inputs.factory inputs.invalidUnary
      (ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (fun receipt => receipt.extracted.diagnostics)) := by
  obtain ⟨produced⟩ := extract_source_for_with_tokens cachedTyped support complete globals entry inputs.to_for
  exact ⟨⟨⟨⟨produced.original.accepted, produced.original.projection, produced.original.signatures,
    produced.original.flow, produced.original.generated, produced.original.extracted⟩,
    produced.plan, produced.equation⟩, produced.tokens⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
/-! Real declaration scopes keep their residual flag. Closed constructor ranges and selected headers
supply source instantiation validity; actual compiler receipts supply the
existing recursive expression Tree. Static source admission, reached selection
coverage, source typing and diagnostic interpretation remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogProfileFactory
open RecursiveNamedExpressionCompilerCertificates RecursiveNamedCallSelectionCertificates
open CompatibleExpressionInstantiationLaws RecursiveNamedResidualExpressionFactory
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

section Expressions
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

/-- The reached full header carries independent source declaration validity.
Only original binder well-formedness and program signature identity are moved
into the caller context; compiler acceptance never supplies source validity. -/
theorem selected_validity {source : TypedSource} {context : SourceSemantics.Context}
    {admitted : ExpressionId → Prop} (sameSignatures : context.signatures = program.signatures) :
    SelectedDeclarationLaw headers compilation source context admitted := by
  intro _id _node _callee _arguments instantiation header _policy _index _signature
    _allowed _found _form _selected _member same _slot _signatureEq binders _admissible
  subst instantiation
  exact CallableCoercionRawNamedCallAdmission.header_valid header sameSignatures binders

/-- The real source frame and its installed parameters retain the program's
entire signature catalog. No equality with a native catalog is inferred. -/
theorem header_program_signatures (header : Header prepared values ambient.definitions program) :
    header.context.signatures = program.signatures := by
  have declaration : header.function.context.signatures = program.signatures := by
    rw [header.frame.context]
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  exact (StructuralSubstitution.MonoBindersExtend.signatures_eq header.extended).trans declaration

/-- Actual selected-site validity removes the named raw-range condition.
Constructor ranges remain independent static source receipts. -/
theorem tree_of_contextual_at
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (lexical : sourceContext.typeVariables = [])
    (constructorRanges : ConstructorRanges source
      (fun id => admitted id ∨ CompatibleExpressionBuiltins.Syntax source id))
    (programSignatures : sourceContext.signatures = program.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact RecursiveNamedExpressionCompilerCertificates.tree_of_contextual_at
    (checkedProgram := checkedProgram)
    (representation := representation)
    (signatures := signatures)
    (locals := locals)
    (parents := parents)
    (assignments := assignments)
    (diagnostics := diagnostics)
    (native := native)
    (skipInitializer := skipInitializer)
    (fuel := fuel)
    (readFuel := readFuel)
    (source := source)
    (scope := scope)
    (id := id)
    (node := node)
    (reasonAt := reasonAt)
    (lowered := lowered)
    (sourceContext := sourceContext)
    (admitted := admitted)
    (caller := caller)
    (admission := admission)
    (coverage := coverage)
    (sourceTypes := sourceTypes)
    (order := order)
    (ordinary := ordinary)
    (callerSelected := callerSelected)
    (callerClosed := callerClosed)
    (unique := unique)
    (declarations := declarations)
    (sourceSignatures := sourceSignatures)
    (allowed := allowed)
    (found := found)
    (typed := typed)
    (readPolicy := readPolicy)
    (lowerPolicy := lowerPolicy)
    (leafPolicy := leafPolicy)
    (accepted := accepted)
    (constructorValid := ConstructorLaw.of_ranges lexical (constructorRanges.restrict (fun _ allowed => Or.inl allowed)))
    (fragmentValid := ConstructorLaw.of_ranges lexical (constructorRanges.restrict (fun _ allowed => Or.inr allowed)))
    (selectedValid := selected_validity programSignatures)

/-- Preserve the former whole-inventory interface as a restriction. -/
theorem tree_of_contextual
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (lexical : sourceContext.typeVariables = [])
    (constructorRanges : ConstructorRanges source
      (fun id => admitted id ∨ CompatibleExpressionBuiltins.Syntax source id))
    (programSignatures : sourceContext.signatures = program.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_at admission coverage.restrict sourceTypes order ordinary callerSelected callerClosed
    unique lexical constructorRanges programSignatures declarations sourceSignatures allowed found typed readPolicy lowerPolicy leafPolicy accepted

end Expressions

variable (cached : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
  (rows : List LambdaRow)
  (cachedRows : cached.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    cached.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
  (member : nativeEntry ∈ cached.indexed.entries)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (definitions : ambient.definitions = cached.indexed.layouts.definitions)
  {headers : Inventory cached.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {header : Header cached.indexed.ancestry values ambient.definitions program}
  (sameCache : header.compiled.closures = cached.indexed.secondPass.closures)
  (complete : Complete headers) (globals : header.globals = cached.indexed.base.globals.length)
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)


variable {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}


/-- The same actual contextual compiler is used at every lexical child scope.
Only signature-dependent source rows move between scopes. The original ledger,
raw instantiations, admission domains and stored node identities remain fixed. -/
theorem expressions_at
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : ReachedCoverage headers compilation header.function.source expressionSyntax) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (sourceSignatures : header.context.signatures = values.checked.signatures) :
∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered := by
  intro sourceContext lexical _residual childSignatures scope fuel id node lowered declarations allowed found typed generated
  rw [policyExpression] at generated
  have tree := tree_of_contextual_at admission coverage
    (sourceTypes_at (childSignatures.trans sourceSignatures.symm) sourceTypes) order ordinary
    callerSelected callerClosed header.unique lexical constructorRanges
    ((childSignatures.trans sourceSignatures.symm).trans (header_program_signatures header)) declarations
    childSignatures allowed found typed expressionRead expressionLower expressionLeaf generated
  simpa only [sameLedger] using tree

/-- Preserve the former whole-inventory interface as a restriction. -/
theorem expressions
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (sourceSignatures : header.context.signatures = values.checked.signatures) :
∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      (fun context => Expressions headers compilation header.readFuel header.function.source context header.solved header.reasonAt) sourceContext scope id lowered := by
  exact expressions_at (cached := cached) policyExpression sameLedger admission coverage.restrict sourceTypes order ordinary
    callerSelected callerClosed constructorRanges expressionRead expressionLower expressionLeaf sourceSignatures

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- Actual cached typing and support still feed the unique statement traversal.
There is no external expression/body meaning or arbitrary child native typing
premise. Constructor raw closed ranges and independent source admission remain explicit. -/
theorem extract_at (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : ReachedCoverage headers compilation header.function.source expressionSyntax) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  apply RecursiveNamedCachedSupport.extract_source cached recipeAccepted rows cachedRows ordered
    member definitions sameCache complete globals entry diagnosticPolicy registered prefixEq factory
    readPolicy binderPolicy allocationPolicy
    (expressions_at (cached := cached) policyExpression sameLedger admission coverage sourceTypes order ordinary callerSelected callerClosed
      constructorRanges expressionRead expressionLower expressionLeaf sourceSignatures)
    assignments unaryPolicy syntaxTree sourceSignatures declarations projection accepted

include member definitions sameCache complete globals recipeAccepted cachedRows ordered entry in
/-- Preserve the former whole-inventory interface as a restriction. -/
theorem extract (diagnosticPolicy : AssignmentDiagnosticPolicy)
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    (prefixEq : compilation.administrativePrefix = 1) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source invalidOperand)
    (readPolicy : header.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      header.policy.lowerBinder header.function.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked header.function.source scope binder)
    (allocationPolicy : header.policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator cached.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)))
    {checkedProgram : CheckedProgram} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignmentTable : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {caller : SourceSpecialization.SpecializedFunction}
    (policyExpression : header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      checkedProgram header.representation signatures locals parents assignmentTable diagnostics compilation
      (some native) none skipInitializer)
    (sameLedger : compilation.solvedRequirements = header.solved)
    (admission : Admission header.function.source expressionSyntax)
    (coverage : Coverage headers compilation) (sourceTypes : SourceTypes headers header.context)
    (order : ∀ id callee arguments instantiation node, expressionSyntax id →
      header.function.source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary header.function.source locals compilation.owner expressionSyntax)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (constructorRanges : ConstructorRanges header.function.source
      (fun id => expressionSyntax id ∨ CompatibleExpressionBuiltins.Syntax header.function.source id))
    (expressionRead : header.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (expressionLower : header.representation.expressions.lowerRead =
      SourceCoreCompatibleDataExpressions.lowerRead header.readFuel values)
    (expressionLeaf : header.representation.expressions.leafLowerer =
      SourceCoreCompatibleDataExpressions.leafLowerer values)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy header.policy values invalidProjection invalidUnary missingDefault)
    (syntaxTree : GenericImperativeFor.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType)
    (sourceSignatures : header.context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source (bodyScope header) header.context)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (bodyScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    : Nonempty (Receipt diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) := by
  exact extract_at (cached := cached) (recipeAccepted := recipeAccepted) (rows := rows) (cachedRows := cachedRows)
    (ordered := ordered) (member := member) (definitions := definitions) (sameCache := sameCache) (complete := complete)
    (globals := globals) (entry := entry) diagnosticPolicy registered prefixEq factory readPolicy binderPolicy allocationPolicy
    policyExpression sameLedger admission coverage.restrict sourceTypes order ordinary callerSelected callerClosed constructorRanges
    expressionRead expressionLower expressionLeaf assignments unaryPolicy syntaxTree sourceSignatures declarations projection accepted

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
/-! Static policies for the actual second-pass named body. The compiler keeps
its base-table matcher; successful matcher checking is transported to the final
native definitions before the single Tree extraction. Actual child typing is
never demanded under the base table. Source admission, diagnostic interpretation,
inventory completeness and runtime entry remain independent obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
open Core Frontend SourceInference RecursiveNamedCatalog
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaders
open CompatibleMatchAmbientLowering

private theorem automatic_signatures {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    automatic.checked.signatures = program.signatures := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i checked registered
    obtain ⟨prepared, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
    cases accepted
    exact SourceCoreCompatibleCatalog.prepare_signatures registered

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

/-- The exact base context used by the existing public named compiler. -/
def baseMatch : SourceCoreCompatibleDataMatches.Context :=
  ⟨.initial compiled.compatible.checked, prepared.named.specialized.function.solvedRequirements,
    some (CallableIndexedNamedGeneration.allocator compiled.indexed prepared.named), none⟩

/-- The same context with its actual final table. No code callback is changed. -/
abbrev ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  withDefinitions (baseMatch prepared) compiled.indexed.layouts.definitions

theorem base_match_policy : (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerMatch =
    some (SourceCoreCompatibleDataMatches.lowerWithReasons (baseMatch prepared)) := rfl

theorem match_success : PolicySuccess (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (ambientMatch prepared) := by
  apply PolicySuccess.extend (base_match_policy prepared)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  prepared.diagnostics.placeReason prepared.named.signature.key site root none

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else prepared.compilation.own.assignments.reasonAt site root (.value operator)

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  prepared.compilation.own.assignments.reasonAt site root .bitNot

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  prepared.diagnostics.placeReason prepared.named.signature.key site root (some type)

theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (.initial compiled.compatible.checked)
    (invalidProjection prepared) (invalidOperand prepared) (missingDefault prepared) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

theorem unary : CompatibleBitNotStatements.Policy
    (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (.initial compiled.compatible.checked)
    (invalidProjection prepared) (invalidUnary prepared) (missingDefault prepared) := rfl

variable {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (atHeader : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include atHeader

theorem header_match : PolicySuccess header.policy (ambientMatch prepared) := by
  rw [atHeader.policy]
  exact match_success prepared

theorem header_read : header.policy.readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  rw [atHeader.policy]
  rfl

theorem header_binder (scope : SourceCoreBasic.Scope) (binder : TypedBinder)
    (monomorphic : binder.scheme.quantified = []) :
    header.policy.lowerBinder header.function.source scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked header.function.source scope binder := by
  rw [atHeader.policy]
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
  rfl

theorem header_allocator : header.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)) := by
  rw [atHeader.policy, atHeader.globals, atHeader.layouts, atHeader.owner, atHeader.active, atHeader.onError]
  rfl

theorem match_allocator : (ambientMatch prepared).sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)) := by
  rw [atHeader.globals, atHeader.layouts, atHeader.owner, atHeader.active, atHeader.onError]
  rfl

omit atHeader in
theorem header_signatures : header.context.signatures = compiled.compatible.checked.signatures :=
  (RecursiveNamedSelectedExpressionFactory.header_program_signatures
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header).trans
    (automatic_signatures compiled.compatiblePrepared).symm

variable {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    compiled.indexed.layouts.definitions (Program.ofChecked compiled.sourceProgram)}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Materialize the actual compiler's static policy fields. Expression admission,
source Syntax and hidden-source freshness stay explicit. The returned match
certificate uses final definitions; actual native child contexts are unchanged. -/
def inputs_with (authenticated : Bool)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source (invalidOperand prepared))
    (hidden : GenericImperativeMatch.MatchHiddenFresh header.function.source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    RecursiveNamedCatalogRuntimeProfileFactory.InputsWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative where
  matchCompilation := ambientMatch prepared
  invalidProjection := invalidProjection prepared
  invalidOperand := invalidOperand prepared
  invalidUnary := invalidUnary prepared
  missingDefault := missingDefault prepared
  factory := factory
  matchPolicy := header_match prepared atHeader
  matchValues := rfl
  matchDefinitions := rfl
  matchAllocator := match_allocator prepared atHeader
  matchLedger := atHeader.solved.symm
  matchChildStatic := GenericImperativeMatch.MatchChildStatic.of_hidden
    (matchCompilation := ambientMatch prepared) (definitions := compiled.indexed.layouts.definitions)
    (administrative := administrative)
    (certificates := fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
      (program := Program.ofChecked compiled.sourceProgram)
      (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source context header.solved header.reasonAt) hidden
  readPolicy := header_read prepared atHeader
  binderPolicy := header_binder prepared atHeader
  allocationPolicy := header_allocator prepared atHeader
  expressions := expressions
  assignments := by rw [atHeader.policy]; exact assignments prepared
  unaryPolicy := by rw [atHeader.policy]; exact unary prepared
  assignmentExpressions := assignmentExpressions
  syntaxTree := syntaxTree
  sourceSignatures := header_signatures (header := header)
  declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header
  projection := atHeader.projection
  accepted := atHeader.accepted

def inputs
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source (invalidOperand prepared))
    (hidden : GenericImperativeMatch.MatchHiddenFresh header.function.source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    RecursiveNamedCatalogRuntimeProfileFactory.Inputs
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      tracked diagnosticPolicy headers header compilation expressionSyntax administrative :=
  inputs_with prepared atHeader false factory hidden expressions assignmentExpressions syntaxTree

end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
/-! Positive receipts for the actual prepared catalog initializer. The returned
entry is built with the existing stored authority. Each retained capture comes
from its prescribed initialized closure read, with the real installer prefix.
Source headers and their static cache alignment remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)

/-- The same initialized capture retains its actual canonical environment,
installer prefix and code renaming. Its full store read and typing are fields
of the indexed Capture itself. -/
structure StoredCaptureReceipt {world : StoreTyping}
    {header : Header compiled.indexed.ancestry values ambient.definitions program}
    (capture : Capture headers
      (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
      0 0 header [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) : Prop where
  canonical : capture.canonical =
    initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  captured : capture.captured = List.replicate header.slot Value.unit ++
    initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame
  embedding : capture.embedding = shift header.slot

variable
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include cached ordered ledger globals sizes locals in
/-- Construct a prescribed capture from the actual initialized store. Native
closure typing is used only for this full known closure read. -/
theorem stored_capture {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ambient.definitions)
    (header : Header compiled.indexed.ancestry values ambient.definitions program) (member : header ∈ headers) :
    ∃ capture : Capture headers
        (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
        0 0 header [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame),
      StoredCaptureReceipt compiled headers rows capture := by
  have rowFound := RecursiveNamedCatalogInitialization.row_of_cached
    (by rw [← cached]; exact ledger.cached header member)
  have read := RecursiveNamedCatalogInitialization.closure_read compiled.indexed.base.globals rows
    compiled.indexed.ancestry.layout.frame ordered rowFound
  obtain ⟨capturedContext, capturedTyped, _⟩ := stored_closure typed read
  obtain ⟨canonicalContext, canonicalTyped⟩ := drop_installer_units header.slot capturedTyped
  have embedding : EnvironmentsAgree (shift header.slot)
      (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)
      (List.replicate header.slot .unit ++ initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame) := by
    intro index value found
    rw [List.getElem?_append_right (by simp [shift])]
    simpa [shift] using found
  have reference := RecursiveNamedCatalogInitialization.frame_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame
  refine ⟨{
    administrative := canonicalContext,
    canonical := initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    captured := List.replicate header.slot Value.unit ++
      initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame,
    capturedContext := capturedContext, embedding := shift header.slot,
    environments := .nil canonicalTyped, locals := ?_, layout := embedding, typed := capturedTyped,
    reference := by simpa only [sizes header member] using reference,
    capturedReference := embedding reference, coherent := ?_, unmapped := by simp,
    distinct := by simp [RecursiveNamedCatalogInitialization.location], read := read },
    ⟨rfl, rfl, rfl⟩⟩
  · rw [locals header member]
    exact .nil
  · intro target targetMember
    simpa only [Nat.zero_add] using RecursiveNamedCatalogInitialization.global_reference
      compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame (globals target targetMember)

/-- These facts concern the concrete initial Entry returned by the producer,
with the same initial store and genuine positive captures. -/
structure ConstructorReceipt (world : StoreTyping)
    (entry : Entry headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled)) : Prop where
  frameLocation : entry.authority.frameLocation = 0
  current : entry.authority.current = .empty
  ghost : entry.authority.ghost = .empty
  records : entry.authority.records = []
  captures : ∀ header, header ∈ headers →
    ∃ capture : Capture headers
        (fun target => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals target.slot)
        0 0 header [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled),
      StoredCaptureReceipt compiled headers (RecursiveNamedCachedRows.rows compiled) capture

include ledger sizes locals in
/-- Actual preparation supplies native store typing once. The existing stored
authority and empty heap representation are retained at that same world/store;
no body execution or classification of an arbitrary returned Entry is needed. -/
theorem entry_with_constructor {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, ∃ entry : Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (RecursiveNamedCatalogPreparedInitialization.environment compiled),
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      ConstructorReceipt compiled headers world entry := by
  obtain ⟨world, typed⟩ := RecursiveNamedCatalogPreparedInitialization.typed accepted
  rw [definitions] at typed
  have actualGlobals : ∀ header, header ∈ headers →
      compiled.indexed.base.globals[header.slot]? = some header.named.signature :=
    fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected
  let authority := RecursiveNamedCatalogInitialization.of_stored compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger actualGlobals sizes locals typed
  let entry : Entry headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (RecursiveNamedCatalogPreparedInitialization.environment compiled) :=
    ⟨authority, by
      intro header member
      simpa only [RecursiveNamedCatalogPreparedInitialization.environment, List.length_nil, Nat.zero_add] using
        RecursiveNamedCatalogInitialization.global_reference
        compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame (actualGlobals header member)⟩
  refine ⟨world, entry, ⟨rfl, ?_, typed, ?_⟩, ⟨rfl, rfl, rfl, rfl, ?_⟩⟩
  · intro left right target impossible
    simp at impossible
  · intro source target impossible
    simp at impossible
  · intro header member
    exact stored_capture compiled headers (RecursiveNamedCachedRows.rows compiled)
      (RecursiveNamedCachedRows.exact_cache compiled) (RecursiveNamedCachedRows.ordered compiled)
      ledger actualGlobals sizes locals typed header member

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.EmittedImperativeMatchCertificates
/-! The same emitted flow and native finish receipts retain the diagnostic
plan returned by the original static position traversal. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

variable {matchCompilation : SourceCoreCompatibleDataMatches.Context}
variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem extraction_of_typed_body_with_emitted (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ProducedExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  obtain ⟨extracted⟩ := extraction_of_typed_position_with_emitted residualMode diagnosticPolicy factory matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy expressions
    assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations projection generated flowTyped
  exact ⟨flow, generated, extracted, rfl⟩


end Solcore.SourceSemantics.CoreLowering.GenericImperativeMatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedEmittedRuntimeProfileFactory
/-! Actual cached Header extraction retains the diagnostic plan generated by
its one original compiler traversal. Interpretation uses concrete local static
receipts and materializes that exact output at the actual parameter entry. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedCatalogNativeContexts NativeExpressionContextSupport
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {authenticated : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {tracked : Bool} {suffix : Core.Context}
  (cachedTyped : HasType (base.globals.map (·.referenceType) ++ .cell prepared.layout.frame.type :: suffix)
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
    header.named.signature.functionType ambient.definitions)
  (support : supported (.lambda header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType) header.code) (base.globals.length + 1) = true)
  (complete : Complete headers) (globals : header.globals = base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include cachedTyped support complete globals entry in
/-- The actual cached entry selects the original static traversal, retaining
its genuine emitted diagnostics rather than an arbitrary receipt predicate. -/
theorem extract_source_for_with_emitted
    (inputs : InputsFor certificates tracked diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (EmittedDiagnosticPlan.Produced inputs.factory
      (ReceiptFor certificates diagnosticPolicy header expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (fun receipt => receipt.extracted.diagnostics)) := by
  have typed := canonical_cached complete globals cachedTyped support entry
  obtain ⟨flow, generated, produced, _⟩ := GenericImperativeMatch.extraction_of_typed_body_with_emitted true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    header.unique inputs.assignmentExpressions inputs.syntaxTree
    (RecursiveNamedSourceContextFacts.header_typeVariables header) (RecursiveNamedSourceContextFacts.header_residual header)
    inputs.sourceSignatures inputs.declarations inputs.projection inputs.accepted typed
  rw [inputs.matchLedger] at produced
  exact ⟨⟨⟨inputs.accepted, inputs.projection, inputs.sourceSignatures, flow, generated, produced.original⟩,
    produced.plan, produced.equation⟩⟩

include cachedTyped support complete globals entry in
/-- The existing runtime certificate specialization preserves the whole
actual emitted receipt and its exact diagnostic plan. -/
theorem extract_source_with_emitted
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)) :
    Nonempty (EmittedDiagnosticPlan.Produced inputs.factory
      (ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
      (fun receipt => receipt.extracted.diagnostics)) := by
  obtain ⟨produced⟩ := extract_source_for_with_emitted cachedTyped support complete globals entry inputs.to_for
  exact ⟨⟨⟨produced.original.accepted, produced.original.projection, produced.original.signatures,
    produced.original.flow, produced.original.generated, produced.original.extracted⟩,
    produced.plan, produced.equation⟩⟩

include cachedTyped support complete globals entry in
/-- Real local diagnostic receipts interpret the returned plan internally and
produce the authentic receipt's own predicate at this actual body entry. -/
theorem interpreted_source_with
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
    {faults : FunctionCalls.FaultRep}
    (localReceipts : EmittedDiagnosticPlan.Plan.LocalReceipts (factory := inputs.factory) registry faults) :
    ∃ receipt : ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults := by
  obtain ⟨produced⟩ := extract_source_with_emitted cachedTyped support complete globals entry inputs
  exact ⟨produced.original, produced.interpreted localReceipts⟩
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
/-! Emitted optional-cell calls select the real catalog capture after their
native argument bundle succeeds. This connects the admitted source program
observation to the call wrapper used at public roots. Input encoding, the
actual root factory equation and argument-bundle evaluation remain separate
receipts; no capture is inferred from a native type or decoded value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup
section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel_with_evidence
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have traced := RecursiveNamedProgramOutcomeMeaning.body_from_program header executed
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.preserves_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      executed.program_well_formed.function_ids uninitialized missing escaped prefixMatches profiles caller member represented heaps traced
  have selected := OptionalCell.read_success reason
    (show Evaluates (DataPatternValues.packValues payloads :: actual) store
      (.var (ξ (scope.length + callerPrefix + header.slot) + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) store
      from .var (agrees (caller.globals header member))) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated selected evaluated
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel called
  exact ⟨value, finalStore, finalMap, finalWorld, required, run, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program_with_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨capture⟩ := caller.authority.captures header member
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated (agrees (caller.globals header member)) capture.read measured
  obtain ⟨outcome, after, finalMap, finalWorld, traced, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.reflects_sized_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller member represented heaps
      size bodySize (Nat.le_of_lt smaller) capture bodyEvaluation
  exact ⟨outcome, after, finalMap, finalWorld,
    RecursiveNamedProgramOutcomeMeaning.program_from_body header admitted heapTyped argumentsTyped traced,
    result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

end Evidence

section Common
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel_with
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact emitted_call_has_sufficient_fuel_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program_with
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_call_reflects_program_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

end Common

section Match
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel_match
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact emitted_call_has_sufficient_fuel_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program_match
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_call_reflects_program_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

end Match

section Native
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact emitted_call_has_sufficient_fuel_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_call_reflects_program_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

end Native
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
end
