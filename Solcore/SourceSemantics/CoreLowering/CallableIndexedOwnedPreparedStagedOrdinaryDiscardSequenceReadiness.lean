import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryPreparedScopeAnnotationCallsReady

/-! Ordinary public preparation constructs call readiness for the exact child
certificates issued by one retained discard-sequence packet. Original static
authority, both policy profiles, view transport and the genuine source receipt
remain inputs. The registry is the actual Selected relation; this theorem does
not extend ordinary owner recovery to implementation-method histories. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories (Choice Conditions)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- Every genuine selected ordinary scope receives call ports for this same
issuer's finite certificate. Child typing comes from its original frame and
parameter receipt; the supplied static conditions contain no CallsReady law. -/
theorem ready_of_preparation
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
    (choice : Choice code (stages := RecursiveStageRegistry.registry compiled.sourceProgram
      compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table))
    (conditions : Conditions code body choice)
    (readFuel_eq : conditions.readFuel = compiled.indexed.fuel)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.Ready
      code body choice conditions := by
  intro invocation selected
  let packet := CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.static
    code body choice conditions invocation selected
  refine ⟨?_⟩
  intro expression child used
  have typed := (packet.authority expression child used).typed
  have root : Certificate code.policy code.lowerBody code.compilation conditions.readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source body.toContext.context choice.packet.reasonAt
      (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code)
      expression child := packet.certificate expression child used
  have atIndices (readFuel : Nat) (reasonAt : ExpressionId → Word)
      (sameFuel : readFuel = compiled.indexed.fuel)
      (sameReason : reasonAt = code.reasonAt)
      (certificate : Certificate code.policy code.lowerBody code.compilation readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source body.toContext.context reasonAt
        (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code)
        expression child) :
      CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
        (compiled := compiled) (invocation := invocation) certificate := by
    subst readFuel
    subst reasonAt
    exact CallableOrdinaryPreparedScopeAnnotationCallsReady.calls_ready
      code retained metadata sourceReceipt unique accepted wellFormed signatureMember sourceOwner
      selected typed certificate
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  exact atIndices conditions.readFuel choice.packet.reasonAt readFuel_eq choice.reason root compiler path

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryDiscardSequenceReadiness
