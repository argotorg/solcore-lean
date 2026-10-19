import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedBranchingLambdaFormation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedReturnLambdaFormation
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedPreparedLambdaBodyFormation

/-! Original named compilation and observed lambda nodes produce physical
formation support. No execution law or full ordinary-header inventory is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem of_actual
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
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
    (returnType : returnNode.type = result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedReturnLambdaFormation.of_terminal_parameters (registry := registry) (faults := faults) terminal
    prepared diagnostic certified profile selected member found form owner requirements coercions ordinary read
    returnFound returnForm returnType
  obtain ⟨formed⟩ := formed
  exact ⟨.inl (by simpa only [stages.evidence selected] using formed)⟩

/-- Original scoped body syntax and the accepted lambda compiler supply full
formation support before any closure body runs. -/
theorem of_branching
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (_receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (_included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (_catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (_shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedPreparedBranchingLambdaFormation.of_terminal terminal
    prepared diagnostic certified profile selected member found form owner requirements coercions ordinary read
    syntaxFor
  obtain ⟨formed⟩ := formed
  exact ⟨.inr (.inl (by simpa only [stages.evidence selected] using formed))⟩


/-- Original scoped body syntax and the accepted lambda compiler supply full
formation support before any closure body runs. -/
theorem of_prepared_branching
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (_receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (_included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.PreparedSyntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (SelectedCompilationPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := SelectedCompilationNamedPreparedLambdaBodyFormation.of_terminal terminal
    prepared diagnostic certified profile (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact catalog) selected member found form owner requirements coercions ordinary read
    shape syntaxFor
  obtain ⟨formed⟩ := formed
  exact ⟨.inr (.inr (by simpa only [stages.evidence selected] using formed))⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedFormationCollectors
