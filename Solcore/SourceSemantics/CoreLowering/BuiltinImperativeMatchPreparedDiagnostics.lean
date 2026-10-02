import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatchExtraction

/-! Prepared diagnostics for the real contextual builtin body. The compiler's
fixed match policy supplies ledger, allocator and token provenance. Independent
source syntax/typing, native typing and residual fault interpretation remain
explicit; no runtime child meaning is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
open Core Frontend SourceInference
section Certificates
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
  {parents : List SourceCoreLocalEvidence.Prepared} {assignmentsTable : SourceCoreAssignmentFaultSites.Table}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
  {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
  {skipInitializer : Option ExpressionId}

theorem extraction_of_contextual_body_with_diagnostics (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values) (matchDefinitions : matchCompilation.definitions = definitions)
    (matchLedger : matchCompilation.solvedRequirements = compilation.solvedRequirements)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation source
      (fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  obtain ⟨flow, generated, extracted, same⟩ := GenericImperativeMatch.extraction_of_typed_body_with_diagnostics diagnosticPolicy factory
    (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
    matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy
    (fun sourceContext closed residual signatures scope fuel id node lowered declarations syntaxTree found typed generated =>
      CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated))
    assignments unaryPolicy unique
    (fun sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated =>
      ⟨CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures
        syntaxTree found typed expressionRead lowerRead leafPolicy (expressionPolicy ▸ generated),
        nativeTyping sourceContext scope fuel id lowered closed residual signatures declarations syntaxTree node found typed generated⟩)
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped
  exact ⟨flow, generated, matchLedger ▸ extracted, same⟩

/-- Actual prepare supplies every reachable operand law. The returned
predicate consists of remaining place/uninitialized/unary diagnostics and
explicit inclusion of operand table diagnostics in the whole fault relation. -/
theorem extraction_of_prepared_contextual_body {first : Nat}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok assignmentsTable)
    (operandTyping : AssignmentDiagnosticOrigins.OperandsTyped source)
    (fixedPolicy : policy = SourceCoreCompatibleDataMatches.loopPolicy values compilation.solvedRequirements
      assignmentsTable diagnostics compilation.owner policy.lowerExpression
      (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)))
      (some definitions))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (unique : NodeOccurrencesUnique source)
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (expressionPolicy : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      program representation signatures locals parents assignmentsTable diagnostics compilation (some native) parent skipInitializer)
    (expressionRead : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (nativeTyping : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionBuiltins.Syntax source id → ∀ node,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context (.statements true statements) expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor .reachable layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt definitions administrative
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) := by
  have assignments := CompatibleAssignmentStatements.AssignmentPolicy.actual values compilation.solvedRequirements assignmentsTable diagnostics compilation.owner policy.lowerExpression
    (some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError))) (some definitions)
  have assignmentPolicy := fixedPolicy.symm ▸ assignments
  exact extraction_of_contextual_body_with_diagnostics .reachable (AssignmentDiagnosticOrigins.Factory.prepared operandTyping prepared)
    (matchCompilation := ⟨values, compilation.solvedRequirements,
      some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
      some definitions⟩)
    (by rw [fixedPolicy]; rfl) rfl rfl rfl rfl
    (GenericImperativeMatch.MatchChildStatic.of_hidden
      (matchCompilation := ⟨values, compilation.solvedRequirements,
        some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt owner active onError)),
        some definitions⟩)
      (certificates := fun context => CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      (definitions := definitions) (administrative := administrative) hidden)
    (by rw [fixedPolicy]; rfl)
    (by intro scope binder _; rw [fixedPolicy]; rfl)
    (by rw [fixedPolicy]; rfl)
    assignmentPolicy
    (show CompatibleBitNotStatements.Policy policy values
      (fun site root => diagnostics.placeReason compilation.owner site root none)
      (fun site root => assignmentsTable.reasonAt site root .bitNot)
      (fun site root type => diagnostics.placeReason compilation.owner site root (some type)) from by rw [fixedPolicy]; rfl)
    unique ordinary expressionPolicy expressionRead lowerRead leafPolicy nativeTyping
    syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped

end Certificates
end Solcore.SourceSemantics.CoreLowering.BuiltinImperativeMatch
