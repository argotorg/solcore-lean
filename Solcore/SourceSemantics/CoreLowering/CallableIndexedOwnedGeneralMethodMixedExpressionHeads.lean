import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPrincipalLambdaExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodMixedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedNestedReadyFamilyReceipts

/-! The original finite named/method-lambda certificates share one actual
principal caller packet. Authentic lambda formation preserves its prefix and
leading bundle in the shared model, including through named/method expressions.
Original named entries and strict joint body children keep the same caller pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedMethodLambdaExpressionHeads (bridge)
open CallableIndexedOwnedMethodMixedExpressionHeads (named_caller)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (context : SourceSemantics.Context) (compilation : SourceCoreFunctions.Context)

/-- The exact original mixed certificate retains its authentic static heads. -/
abbrev Head (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  CallableIndexedOwnedMethodMixedExpressionHeads.Head
    (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate

variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

variable
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (prefixOne : compilation.administrativePrefix = 1)
  (prefixZero : owner.key.capturePrefix = 0)
  (globalCounts : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source principal.named))
  (covers : principal.dictionary.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source principal.named))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (idsUnique : RequirementIdsUnique context)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers → CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor
    (headers := headers) (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) header)
  (syntaxTrees : ∀ header, header ∈ headers → GenericImperativeMatch.Syntax header.function.source
    (expressionSyntax header) header.context (.statements true header.function.body) header.function.resultType)

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique owners idsUnique
  sameLayouts escaped profiles syntaxTrees in
/-- Each selected finite branch runs at the same input and returned caller.
Its body obligation is the actual strict child of the extended shared family. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.preserves_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique idsUnique
    sameLayouts escaped profiles owners budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.source_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedPrincipalLambdaExpressionHeads.preserves_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted trace
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted trace

include inclusion prefixOne prefixZero globalCounts complete slots wellFormed runtime covers unique
  sameLayouts escaped profiles syntaxTrees in
/-- Native finite selection keeps the original measured children and restores
the same full caller while independently reconstructing the Source parent. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named) certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (Head (headers := headers) (registry := registry) (faults := faults) principal context compilation certificate) faults size := by
  have named : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers compilation (CallableIndexedNamedGeneration.source principal.named) context principal.dictionary certificate) faults size :=
    CallableIndexedOwnedAdmittedNamedExpressionHeads.reflects_at
    (functions := functions) (owner := owner) (runtime := true) principal.dictionary
    (named_caller principal compilation owner prefixOne) wellFormed runtime covers unique
    sameLayouts escaped profiles budget size within children
    (fun header member => CallableIndexedOwnedNamedNestedReadyFamilyReceipts.native_bodies
      (functions := functions) (owner := owner) (runtime := true) wellFormed prefixZero (globalCounts header member)
      member (syntaxTrees header member) (fun index => below (.namedNested index)))
  have methodLambda : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) principal owner)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context principal.dictionary (CallableIndexedNamedGeneration.source principal.named)
      (CallableIndexedOwnedMethodLambdaExpressionHeads.Head (registry := registry) (faults := faults) principal context certificate) faults size :=
    CallableIndexedOwnedPrincipalLambdaExpressionHeads.reflects_at
    principal context owner profile functions inclusion complete slots wellFormed runtime covers budget size within children below
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  cases head with
  | named head => exact named head found sourceTyped environments heaps locals agrees typed initial admitted completed
  | method_lambda head => exact methodLambda head found sourceTyped environments heaps locals agrees typed initial admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralMethodMixedExpressionHeads
