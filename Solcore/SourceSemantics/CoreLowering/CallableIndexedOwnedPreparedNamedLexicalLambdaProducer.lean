import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping

/-! The real named expression callback retains an ordinary lambda at any
actual lexical scope. Native child typing comes from the enclosing accepted
body, and its literal callable constructors determine the result type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include aligned in
/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (accepted : header.policy.lowerExpression childFuel header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
    (context compiled.indexed prepared.named) compiled.indexed.base.callableContext none none
    childFuel header.function.source
    scope id header.reasonAt =
      .ok lowered at accepted
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source prepared.named :=
    header.agreement.source.trans (congrArg source aligned.named)
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have actualAccepted := fuelEq ▸ accepted
  obtain ⟨policy, lowerBody, _accepted, ⟨certificate⟩, _allocationProfile, _manifest,
      expressionProfile, callables, _projector, _binderPolicy, _bodyRecipe, _policyRecipe⟩ :=
    CallableIndexedLambdaGeneration.contextual_certificate_with_policy_recipe compiled.indexed
      prepared.compilation record found form owner requirements coercions ordinary read actualAccepted
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found expressionProfile callables nativeTyped
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, policyRecipe, view, reasonAt⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_policy_recipe_exact compiled.indexed
      prepared.compilation record sourceContext evidence [] profile
      (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
      (by simpa only [fuelEq] using accepted) native
  let rawProduced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := policyRecipe.body_recipe
    compilerPolicy := policyRecipe }
  have actual : ∃ produced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt :=
    ⟨rawProduced, view, reasonAt⟩
  let Property (named : Named) : Prop :=
    ∃ produced : Produced (compiled := compiled) named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt
  exact Eq.mp (congrArg Property aligned.named.symm) actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaProducer
