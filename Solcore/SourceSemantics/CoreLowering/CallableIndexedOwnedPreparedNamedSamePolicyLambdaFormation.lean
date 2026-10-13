import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation

/-! An actual lambda child below a recursive expression uses its retained root
policy and reached lexical context. Original Source typing and native child
typing construct the same formation receipt; captures come from execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics prepared.code
    prepared.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {childFuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

include aligned in
/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_expression
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (fields : Dynamic.RuntimeContextFields header.context sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext)
    (sourceTyped : ExpressionHasType header.function.source sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      childFuel (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header sourceContext child.evidence
      scope
      id lowered) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer.of_expression
    (sourceContext := sourceContext) (evidence := child.evidence) prepared aligned root profile
    found form owner requirements coercions ordinary read accepted nativeTyped
  have actualFound : header.function.source.lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  have sourceTyped : ExpressionHasType header.function.source sourceContext id produced.site.code.sourceNode.type :=
    sameNode.symm ▸ sourceTyped
  let function := closure header.named parameters result [statement] sourceContext child.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport ((RecursiveNamedInitialContextValidity.mono_fields header.extended).trans fields)
  have covers : function.evidence.Covers function.context := by
    change child.evidence.Covers sourceContext
    rw [stages.evidence selected]
    exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      scope.length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact fields.solvedRequirements.trans (header.valid.ledger.trans (aligned.solved.trans (by rw [aligned.named]; rfl)))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have invocationSource : child.source = function.source :=
    (stages.source selected).trans original.symm
  have returnFound : function.source.lookupStatement? statement = some returnNode := by
    simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression function.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound returnFound) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  obtain ⟨lowered, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return
    produced.site.code produced.recipe inputs frame ledger profile actualView rfl
    returnFound returnForm returnType childFound childType childTyped
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared prepared diagnostic aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header prepared aligned fields
      ((stages.evidence selected).trans (congrArg (fun function => function.evidence) aligned.function)))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation
