import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSelectedCall
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipalCaptures

/-! Actual method lambda sites produce finite formation and call certificates.
The static site retains its original empty capture environment and full body
receipt. At each genuine input the principal packet determines the used native
prefix, and the original Code and body are recaptured at that actual Source
environment. No semantic callee factory is stored in a certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedMethodLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context)

/-- The complete accepted static site and body belong to this actual method
Source occurrence. Only the capture environment is filled at execution input. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary [] scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
    expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure principal.named parameters result statements context principal.dictionary [])
  ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions []
  coercions : site.code.sourceNode.coercions = []
  syntaxTree : GenericImperativeMatch.Syntax
    (CallableIndexedNamedGeneration.source principal.named)
    (expressionSyntax (CallableIndexedNamedGeneration.source principal.named)) body.context
    (.statements true statements) result

variable {principal context}

/-- Actual capture locations change no accepted compiler or Source field. -/
def Formation.function {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure principal.named head.parameters head.result head.statements
    context principal.dictionary environment

def Formation.code {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
    (indexed := compiled.indexed) head.site.code environment

/-- Original static body recapture retains its complete Source frame,
dictionary, Tree, certificates and accepted emitted body. -/
def Formation.support {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) principal context scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) registry faults where
  method := method
  principal := principal
  expressionSyntax := head.expressionSyntax
  certificates := head.certificates
  source := rfl
  compilation := head.site.compilation
  active := head.site.active
  body := RecursiveNamedLambdaFormationHeads.recaptureBodyWith (values := .initial compiled.compatible.checked)
    (indexed := compiled.indexed) head.site.code head.body environment

variable (principal context)

/-- The ordered original compiler argument receipt and genuine Source row
remain independent. Both guards select this same accepted literal Code. -/
structure Call (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  callee : ExpressionId
  calleeCode : SourceCoreBasic.LoweredExpr
  formation : Formation (registry := registry) (faults := faults) principal context scope callee calleeCode
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
    (CallableIndexedNamedGeneration.source principal.named) scope id formation.site.code.id ids metadata reasonAt lowered
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared formation.site.code
  sameCallee : compiler.calleeCode = formation.site.code.lowered
  sourceArguments : ExpressionsHaveTypes (CallableIndexedNamedGeneration.source principal.named)
    context ids formation.body.types
  sourceCount : formation.body.types.length = metadata.argumentCount

/-- This finite sum is a genuine expression Certificate transformer. Neither
branch classifies arbitrary values or contains an evaluation law. -/
inductive Head (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | formation {scope id lowered}
      (head : Formation (registry := registry) (faults := faults) principal context scope id lowered) :
      Head principal context certificate scope id lowered
  | call {scope id lowered}
      (head : Call (registry := registry) (faults := faults) principal context certificate scope id lowered) :
      Head principal context certificate scope id lowered


def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner principal.named

def model (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include complete slots wellFormed runtime covers in
/-- Each authentic finite branch constructs captures, Code and Support at
its actual input. Strict arguments and the joint body's own strict IH remain. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, CallableIndexedLambdaGeneration.closure, head.identifier] using
        head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have nativeTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
        (head.function environment).context (head.function environment).evidence (head.function environment).source
        (head.function environment).captured before code.id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    obtain ⟨result, finalStore, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormation.preserves_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile
        wellFormed runtime covers locals actualTyped head.sourceType head.ordinary head.coercions heaps
        capturedAdmission nativeTrace
    have evaluated : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using evaluated
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
        mapping world code.sourceNode.type lowered.type faults outcome result := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, mapping, world, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCall.preserves_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below trace within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

include complete slots wellFormed runtime covers in
/-- Native child bounds are measured independently. The same static branch
producer reconstructs the authentic Source trace and restores its exact pool. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile) wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (registry := registry) (faults := faults) principal context certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  let captured := CallableIndexedOwnedMethodPrincipalCaptures.captures principal owner initial.val initial.property
    complete environments agrees nativeTyped
  have packet := CallableIndexedOwnedMethodPrincipalCaptures.captured_packet principal owner initial.val initial.property
    complete environments agrees nativeTyped slots
  let capturedInitial : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
      ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
  have capturedAdmission : Admission (bridge (headers := headers) principal owner) context capturedInitial :=
    ⟨admitted.heap, admitted.rows⟩
  cases head with
  | formation head =>
    let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
    let support : Support code registry faults := head.support environment
    have sourceFound : (CallableIndexedNamedGeneration.source principal.named).lookupExpression? id = some code.sourceNode := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
    have same := Option.some.inj (found.symm.trans sourceFound)
    subst node
    have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context code.id code.sourceNode.type := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using typed
    have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
      simpa only [code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode,
        head.emitted, captured, CallableIndexedOwnedMethodPrincipalCaptures.captures] using completed
    obtain ⟨sourceSize, outcome, after, trace, _native, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedMethodLambdaFormation.reflects_at
        (function := head.function environment) (scope := scope) (actual := actual) captured code support owner initial.val packet profile
        wellFormed runtime covers locals actualTyped head.sourceType head.ordinary head.coercions heaps capturedAdmission actualCompleted
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) environment before id outcome after := by
      simpa only [code, Formation.code, Formation.function, CallableIndexedLambdaGeneration.closure,
        RecursiveNamedLambdaFormationHeads.recaptureCode, head.identifier] using trace
    have represented : GenericExpressionMeaning.ResultRepresents
        (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile)
        mapping world code.sourceNode.type lowered.type faults outcome value := by
      simpa only [model, code, Formation.code, RecursiveNamedLambdaFormationHeads.recaptureCode, head.emitted] using represented
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, mapping, world, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed sourceTrace frame⟩
  | call head =>
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans head.compiler.found)
    subst node
    let issued : CallableIndexedOwnedMethodLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.formation.syntaxTree, parentTyped := typed }
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedMethodLambdaSelectedCall.reflects_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (compiler := head.compiler) (wellFormed := wellFormed) (runtime := runtime)
        (covers := covers) (locals := locals) (heaps := heaps)
        (admitted := capturedAdmission) issued budget children below completed within
    obtain ⟨actualReached, _pool, actualRelated⟩ :=
      (bridge (headers := headers) principal owner).restore initial reached.val maps worlds frame metadata related
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaExpressionHeads
