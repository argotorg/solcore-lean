import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts

/-! Actual named terminal lowering constructs an empty ordinary lambda's
formation receipt. Source typing comes from the accepted Header, native typing
from the same checked cached body, and both trees from the literal empty body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

private theorem native_child
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) (emptyInputs : entry.native.inputTypes = []) :
    HasType (SourceCoreLocalCell.coreContext
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.receipt.child.expression (LanguageResult.resultType terminal.receipt.child.type)
      compiled.indexed.layouts.definitions := by
  have cached := terminal.prepared.cached.trans (congrArg some terminal.prepared.compilation.emitted)
  have cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code) := by
    simpa only [terminal.aligned.slot, terminal.aligned.named, terminal.aligned.code] using cached
  have typed := RecursiveNamedCatalogNativeContexts.prepared_body compiled.indexedPrepared member
    (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) rfl header cached
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
  have child := terminal.receipt.native_child_exact typed
  change HasType _ _ _ compiled.indexed.layouts.definitions at child
  simpa only [RecursiveNamedCatalogNativeContexts.bodyPrefix, RecursiveNamedCatalogNativeContexts.bodyScope,
    RecursiveNamedLambdaFormationHeads.nativePrefix, emptyInputs, SourceCoreGeneralEntry.nativeInputContext,
    List.map_nil, List.reverse_nil, List.append_nil, List.append_assoc,
    CallableIndexedAmbient.ambient_definitions, ← header.parameterType] using child

/-- All shape checks refer to the original, actually lowered occurrence. -/
theorem of_terminal
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) (emptyInputs : entry.native.inputTypes = [])
    {node : ExpressionNode} {reported : Ty}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda [] .unit [])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported)) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  have accepted := terminal.receipt.generated
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy terminal.prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression terminal.aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext terminal.prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    terminal.prepared.compilation.parents terminal.prepared.compilation.own.assignments terminal.prepared.diagnostics
    (context compiled.indexed terminal.prepared.named) compiled.indexed.base.callableContext none none
    terminal.receipt.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) terminal.expression header.reasonAt =
      .ok terminal.receipt.child at accepted
  have nonzero : terminal.receipt.childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source terminal.prepared.named :=
    header.agreement.source.trans (congrArg source terminal.aligned.named)
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      terminal.prepared.named.signature.key = .ok terminal.prepared.named.specialized := by
    simpa only [terminal.aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  obtain ⟨rawProduced⟩ := CallableIndexedOwnedContextualLambdaProducerReceipts.of_contextual
    terminal.prepared.compilation record header.context header.function.evidence profile
    (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
    (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
    (by simpa only [fuelEq] using accepted) (native_child terminal member emptyInputs)
  have produced : Produced (compiled := compiled) header.named [] .unit [] header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child := by
    simpa only [terminal.aligned.named] using rawProduced
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named [] .unit [] header.context header.function.evidence []
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
  have parametersEmpty : produced.site.code.receipt.loweredParameters = [] := by
    have same := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) produced.site.code
    exact List.map_eq_nil_iff.mp same.symm
  let inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code := {
    context := header.context
    types := []
    extended := .nil _
    kinds := by simp only [parametersEmpty, List.not_mem_nil, false_implies, implies_true]
    referenceIndex := by
      change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
      rw [produced.site.compilation]
      rfl }
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  obtain ⟨body, _sameInputs⟩ := CallableIndexedOwnedPreparedEmptyLambdaBodySupport.of_empty produced.site.code
    (expressionSyntax := fun _ _ => False) (certificates := fun _ _ _ _ _ _ => False)
    produced.recipe inputs frame ledger profile rfl rfl
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (fun _ _ => False) (fun _ _ _ _ _ _ => False) body
    (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_empty rfl)
    (CallableIndexedOwnedContextualLambdaProvenance.BodyReasons.of_empty rfl)
    declarations
    (.body (.nil (.inr rfl))) facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
