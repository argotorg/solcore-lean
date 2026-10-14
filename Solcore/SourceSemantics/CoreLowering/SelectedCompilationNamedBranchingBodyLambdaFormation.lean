import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnLambdaStaticFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness

/-! Actual named compilation retains the same lambda and its complete
scoped imperative body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingBodyLambdaFormation
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
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
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
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
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
    SelectedCompilationNamedTerminalChildReceipts.source_child terminal.receipt selected certified
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := certified
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
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.Syntax function.source
      (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  obtain ⟨body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedBranchingLambdaBodySupport.of_branching
    produced.site.code produced.issuedRecipe
    (by rw [terminal.aligned.named]; exact terminal.prepared.selected) rfl receiver included
    produced.site.compilation inputs frame ledger profile actualView
    (by rw [produced.site.compilation]; rfl) produced.site.active produced.site.allocationError
    signatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (by rw [CallableIndexedOwnedPublicSignatureCatalog.signatures compiled]; exact catalog) entryDeclarations (by simpa only [function, closure, source, ← header.agreement.source] using shape) syntaxTree
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Child body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedBranchingBodyLambdaFormation
