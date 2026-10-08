import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads

/-! A finite ordinary formation/call certificate keeps the actual accepted Site,
unrestricted same-Code body and original compiler selection. Genuine nested
input packets construct captures internally. Ordered admitted arguments and the
strict shared-family child consume the same real parameter/body post; caller
restoration keeps the actual reached pool. All heaps use the supplied model. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation bridge model)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- The call retains the exact parent receipt and independent Source argument
row. Its body Syntax belongs to the same accepted unrestricted formation Site. -/
structure Call (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  callee : ExpressionId
  calleeCode : SourceCoreBasic.LoweredExpr
  formation : Formation (registry := registry) (faults := faults) caller context evidence scope callee calleeCode
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  fuel : Nat
  compilation : SourceCoreFunctions.Context
  ids : List ExpressionId
  metadata : IndirectCallResolution
  reasonAt : ExpressionId → Word
  compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation
    (CallableIndexedNamedGeneration.source caller.named) scope id formation.site.code.id ids metadata reasonAt lowered
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared formation.site.code
  sameCallee : compiler.calleeCode = formation.site.code.lowered
  sourceArguments : ExpressionsHaveTypes (CallableIndexedNamedGeneration.source caller.named)
    context ids formation.body.types
  sourceCount : formation.body.types.length = metadata.argumentCount
  syntaxTree : GenericImperativeMatch.Syntax (CallableIndexedNamedGeneration.source caller.named)
    (formation.expressionSyntax (CallableIndexedNamedGeneration.source caller.named)) formation.body.context
    (.statements true formation.statements) formation.result

/-- Neither finite branch classifies arbitrary values or stores a meaning law. -/
inductive Head (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | formation {scope id lowered}
      (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered) :
      Head caller context evidence certificate scope id lowered
  | call {scope id lowered}
      (head : Call (registry := registry) (faults := faults) caller context evidence certificate scope id lowered) :
      Head caller context evidence certificate scope id lowered

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  {certificate : GenericExpressionMeaning.Certificate}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual recapture and static selection construct the finite parent endpoint;
only strictly smaller admitted arguments and shared-family bodies remain. -/
theorem preserves_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner) (model (registry := registry) functions)
      context evidence source certificate faults child)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner) (model (registry := registry) functions)
      context evidence source (Head (registry := registry) (faults := faults) caller context evidence certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  cases head with
  | formation head =>
    exact CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.preserves_at caller context evidence owner profile
      functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource size
      (scope := scope) (id := id) (lowered := lowered) ⟨head⟩ found typed
      environments heaps locals agrees nativeTyped initial admitted trace
  | call head =>
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let captured := captures_for complete globals entry environments agrees nativeTyped
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical
        (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    have packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
        ⟨scope, mapping, world, before, store, captured.canonical⟩ initial.val := {
      globals := observed.globals, reference := observed.reference,
      bundle := CallableIndexedLambdaNestedFormationEntries.bundle_of_environment captured.represented rfl,
      carried := initial.property.carried }
    let capturedInitial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
        ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
    have capturedAdmission : Admission (bridge (headers := headers) caller owner) context capturedInitial :=
      ⟨admitted.heap, admitted.rows⟩
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans (by simpa only [sameSource] using head.compiler.found))
    subst node
    let issued : CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.syntaxTree, parentTyped := by
        change ExpressionHasType (CallableIndexedNamedGeneration.source caller.named) context id head.compiler.original.type
        simpa only [sameSource] using typed }
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall.preserves_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (prefixContext := rfl) (observed := observed) (functions := functions) (inclusion := inclusion)
        (compiler := head.compiler) (wellFormed := wellFormed)
        (runtime := by simpa only [sameSource, CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation.function, CallableIndexedLambdaGeneration.closure] using runtime)
        (covers := covers) (locals := locals) (heaps := heaps) (admitted := capturedAdmission) issued budget
        (by
          change ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
            (bridge (headers := headers) caller owner) (model (registry := registry) functions)
            context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults child
          simpa only [sameSource] using children)
        below (by simpa only [sameSource, CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation.function, CallableIndexedLambdaGeneration.closure, captured, captures_for] using trace) within
    obtain ⟨actualReached, _samePool, actualRelated⟩ :=
      (bridge (headers := headers) caller owner).restore initial reached.val maps worlds frame metadata related
    have evaluated : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
      simpa only [captured, captures_for] using evaluated
    exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed trace frame⟩

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual recapture and static selection construct the finite parent endpoint;
only strictly smaller admitted arguments and shared-family bodies remain. -/
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner) (model (registry := registry) functions)
      context evidence source certificate faults child)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner) (model (registry := registry) functions)
      context evidence source (Head (registry := registry) (faults := faults) caller context evidence certificate) faults size := by
  intro scope id lowered head node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  cases head with
  | formation head =>
    exact CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.reflects_at caller context evidence owner profile
      functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource size
      (scope := scope) (id := id) (lowered := lowered) ⟨head⟩ found typed
      environments heaps locals agrees nativeTyped initial admitted completed
  | call head =>
    let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
      initial.property.observed initial.property.carried initial.property.bundle globals
    let captured := captures_for complete globals entry environments agrees nativeTyped
    have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
    have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
      change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical
        (initial.val.rows owner.position).authority.frameLocation at observed
      rw [(initial.val.rows owner.position).frame_eq] at observed
      exact observed
    have packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
        ⟨scope, mapping, world, before, store, captured.canonical⟩ initial.val := {
      globals := observed.globals, reference := observed.reference,
      bundle := CallableIndexedLambdaNestedFormationEntries.bundle_of_environment captured.represented rfl,
      carried := initial.property.carried }
    let capturedInitial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
        ⟨scope, mapping, world, before, store, captured.canonical⟩ := ⟨initial.val, packet⟩
    have capturedAdmission : Admission (bridge (headers := headers) caller owner) context capturedInitial :=
      ⟨admitted.heap, admitted.rows⟩
    let code : Code compiled.indexed (head.formation.function environment) scope captured.administrative := head.formation.code environment
    let support : Support code registry faults := head.formation.support environment
    have same := Option.some.inj (found.symm.trans (by simpa only [sameSource] using head.compiler.found))
    subst node
    let issued : CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall.Receipt
        (function := head.formation.function environment) captured code support head.compiler certificate := {
      native := head.native, prepared := head.prepared, parent := head.parent,
      selection := ⟨head.selection.children, head.selection.nativeTypes, head.selection.escaped,
        head.selection.rawResult, head.selection.nativeResult, head.selection.stageAccepted, head.selection.arityAccepted⟩,
      sameCallee := head.sameCallee, ordinary := head.formation.ordinary, coercions := head.formation.coercions,
      sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
      syntaxTree := head.syntaxTree, parentTyped := by
        change ExpressionHasType (CallableIndexedNamedGeneration.source caller.named) context id head.compiler.original.type
        simpa only [sameSource] using typed }
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
        reached, related, _post⟩ :=
      CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall.reflects_at_receipt
        (function := head.formation.function environment) (scope := scope) (actual := actual)
        (captured := captured) (code := code) (support := support) (owner := owner) (initial := initial.val) (packet := packet)
        (profile := profile) (prefixContext := rfl) (observed := observed) (functions := functions) (inclusion := inclusion)
        (compiler := head.compiler) (wellFormed := wellFormed)
        (runtime := by simpa only [sameSource, CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation.function, CallableIndexedLambdaGeneration.closure] using runtime)
        (covers := covers) (locals := locals) (heaps := heaps) (admitted := capturedAdmission) issued budget
        (by
          change ∀ child, child < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
            (bridge (headers := headers) caller owner) (model (registry := registry) functions)
            context evidence (CallableIndexedNamedGeneration.source caller.named) certificate faults child
          simpa only [sameSource] using children)
        below (by simpa only [sameSource, CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation.function, CallableIndexedLambdaGeneration.closure, captured, captures_for] using completed) within
    obtain ⟨actualReached, _samePool, actualRelated⟩ :=
      (bridge (headers := headers) caller owner).restore initial reached.val maps worlds frame metadata related
    have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after := by
      simpa only [sameSource, CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads.Formation.function, CallableIndexedLambdaGeneration.closure] using sourceTrace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
      actualReached, actualRelated, after_expression_sized initial actualReached admitted wellFormed runtime covers locals
        typed sourceTrace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads
