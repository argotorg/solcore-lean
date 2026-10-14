import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles

/-! An ordinary lambda below a recursive expression retains the original root
policy at its actual child fuel. Native child typing determines the emitted
callable type, and the retained producer keeps that exact Site and policy. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
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
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include aligned in
/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
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
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      childFuel (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source prepared.named :=
    header.agreement.source.trans (congrArg source aligned.named)
  have actualAccepted := fuelEq ▸ accepted
  have pointwise := lambda_policy root (scope := scope) (reasonAt := header.reasonAt)
    found form requirements coercions ordinary
  have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt :=
    pointwise.special _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special owner found
    (pointwise.read.trans read) form actualAccepted
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found root.rawLambdaExpression root.callables nativeTyped
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, _sameFuel, view, reasonAt,
      _sourceNode, _node, _sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate actualAccepted
      profile (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl
      root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType native
  have issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained prepared.named site.code := by
    apply CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes (rootFuel := rootFuel)
      prepared.compilation (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic) (sameBody.trans root.selected.recipe) _ site.compilation
    rw [samePolicy]
    exact root.compilerPolicy
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy prepared.named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans root.selected.binder
  let rawProduced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
