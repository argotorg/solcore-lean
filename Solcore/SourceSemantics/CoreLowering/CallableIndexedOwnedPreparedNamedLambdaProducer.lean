import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProducerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch

/-! The actual named terminal callback retains one literal lambda Site, its
original compiler view and complete policy. Bootstrap acceptance removes only
unused native input slots before the genuine child typing inversion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

private theorem native_child
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.receipt.child.expression (LanguageResult.resultType terminal.receipt.child.type)
      compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed
    terminal.prepared terminal.aligned member
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using
      CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported prepared terminal.prepared terminal.aligned)
  have body := RecursiveNamedCatalogNativeContexts.body_of_cached (suffix := [])
    (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (header := header) (by simpa only [List.append_nil, List.append_assoc, List.singleton_append,
      CallableIndexedAmbient.ambientDefinitions, SourceCoreCompatibleValues.Context.initial] using minimal)
  have child := terminal.receipt.native_child_exact body
  change HasType _ _ _ compiled.indexed.layouts.definitions at child
  simpa only [RecursiveNamedCatalogNativeContexts.bodyPrefix, RecursiveNamedCatalogNativeContexts.bodyScope,
    RecursiveNamedLambdaFormationHeads.nativePrefix, List.append_nil, List.append_assoc, ← header.parameterType] using child

/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported)) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
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
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, issuedRecipe, view, reasonAt⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact compiled.indexed
      terminal.prepared.compilation (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared terminal.prepared diagnostic) record header.context header.function.evidence [] profile
      (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
      (by simpa only [fuelEq] using accepted) (native_child terminal prepared member)
  let rawProduced : Produced (compiled := compiled) terminal.prepared.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  have actual : ∃ produced : Produced (compiled := compiled) terminal.prepared.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt :=
    ⟨rawProduced, view, reasonAt⟩
  let Property (named : Named) : Prop :=
    ∃ produced : Produced (compiled := compiled) named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt
  exact Eq.mp (congrArg Property terminal.aligned.named.symm) actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
