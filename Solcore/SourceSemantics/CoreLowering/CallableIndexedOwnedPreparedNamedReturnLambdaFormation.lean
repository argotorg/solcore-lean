import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness

/-! Actual named compilation retains the same lambda and its single
return child. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal_parameters
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result [statement] header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
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
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
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
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩

/-- The nullary entry point keeps its original API. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda [] result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :=
  of_terminal_parameters terminal prepared diagnostic wellFormed profile selected member
    found form owner requirements coercions ordinary read returnFound returnForm returnType

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
