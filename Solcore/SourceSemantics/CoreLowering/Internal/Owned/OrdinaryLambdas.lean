import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.ExpressionTrees

/-!
# Owned callables: ordinary lambdas

Source facts, formation heads, selected calls and expression bounds of general ordinary lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
/-! The actual Source lambda judgment supplies the raw function type and body
receipt at the same occurrence. Authentic Source runtime fields and evidence
then construct its closure frame, independently of native callable typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
open Core Frontend SourceInference

/-- All fields refer to the original Source row and the literal closure. -/
structure Facts (function : Dynamic.Closure) (id : ExpressionId) (node : ExpressionNode) : Prop where
  contains : ContainsExpression function.source id node
  form : node.form = .lambda function.parameters function.resultType function.body
  rawType : node.rawType = FunctionValues.sourceType function
  sourceType : node.type = FunctionValues.sourceType function
  ordinary : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions []
  coercions : node.coercions = []
  typing : ExpressionFormHasRawType function.source function.context node.form
    (FunctionValues.sourceType function) (.ordinary [])

variable {function : Dynamic.Closure} {id : ExpressionId} {node : ExpressionNode}

/-- One lookup and typing inversion retains the complete original body
judgment. Parameter packing comes from the actual monomorphic binder row. -/
theorem of_typed (unique : NodeOccurrencesUnique function.source)
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body)
    (typed : ExpressionHasType function.source function.context id node.type)
    (coercions : node.coercions = []) : Facts function id node := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actual raw plan contains formTyped rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at formTyped
    cases formTyped with
    | @lambda _ lambdaContext finalContext _ parameterTypes _ _ bodyFacts namesUnique parametersExtend bodyTyped completes =>
      have bodies := MonoBindersExtend.bodyTypes_eq parametersExtend
      have shape : TypeSystem.Ty.function (TypeSystem.Ty.productMany parameterTypes) function.resultType =
          FunctionValues.sourceType function := by
        simp only [FunctionValues.sourceType, bodies]
      have finalType : node.type = FunctionValues.sourceType function := by
        simpa only [ExpressionNode.rawType, coercions] using rawType.trans shape
      cases requirements with
      | ordinary owned path layout =>
        refine ⟨contains, form, rawType.trans shape, finalType, layout, coercions, ?_⟩
        rw [form, ← shape]
        exact .lambda namesUnique parametersExtend bodyTyped completes

/-- The same actual static Source validity supplies every closure-code field.
No body execution or native-code equality is used to construct the frame. -/
theorem Facts.frame (facts : Facts function id node) {program : Program}
    (runtime : Dynamic.SourceRuntimeValid program function.context function.source)
    (covers : function.evidence.Covers function.context) : Dynamic.ClosureFrame program function := by
  refine ⟨runtime.signatures, runtime.owner, ?_, runtime.requirements.idsUnique, covers⟩
  exact {
    owner := runtime.owner
    closed := runtime.closed
    variables_closed := runtime.variables_closed
    residual_variables_open := runtime.residual_variables_open
    graph := runtime.graph
    requirement_ledger := runtime.requirements
    occurrence := ⟨id, node, facts.contains, facts.form, facts.rawType, facts.typing⟩ }

section ActualProduced
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- The chosen compiler Site already keeps the original lookup and form.
Genuine Source typing supplies its raw fields at that same occurrence. -/
theorem Produced.source_facts
    (unique : NodeOccurrencesUnique (source caller.named))
    (typed : ExpressionHasType (source caller.named) sourceContext id produced.site.code.sourceNode.type)
    (coercions : produced.site.code.sourceNode.coercions = []) :
    Facts (closure caller.named parameters result statements sourceContext evidence []) id produced.site.code.sourceNode := by
  have found : (source caller.named).lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier] using produced.site.code.sourceFound
  exact of_typed unique found produced.site.code.sourceForm typed coercions

/-- This derives the genuine frame needed by the static joint-body collector.
Its whole Source runtime receipt and covering evidence remain explicit. -/
theorem Produced.frame_of_typed
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) sourceContext (source caller.named))
    (covers : evidence.Covers sourceContext)
    (typed : ExpressionHasType (source caller.named) sourceContext id produced.site.code.sourceNode.type)
    (coercions : produced.site.code.sourceNode.coercions = []) :
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure caller.named parameters result statements sourceContext evidence []) :=
  (Produced.source_facts caller produced runtime.graph.nodeOccurrencesUnique typed coercions).frame runtime covers

end ActualProduced
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSourceFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
/-! An accepted ordinary Site retains unrestricted same-Code static body
support. At each actual input its genuine nested Header packet and represented
environment construct captures and full carried history. All heaps use the
supplied function model; forward inclusion transfers only the formed closure. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- This original compiler receipt contains no dynamic capture or meaning
factory. Only the actual input fills its stored capture environment. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence [] scope (nativePrefix (values := .initial compiled.compatible.checked) caller)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
    expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions []
  coercions : site.code.sourceNode.coercions = []

variable {caller context evidence}

/-- Recapture retains the complete original Source occurrence and dictionary. -/
def Formation.function {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements
    context evidence environment

/-- The accepted Code is reused with only its actual capture environment. -/
def Formation.code {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (nativePrefix (values := .initial compiled.compatible.checked) caller) :=
  recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) head.site.code environment

/-- The genuine Header and full unrestricted static body remain the same. -/
def Formation.support {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) registry faults :=
  (Support.of_site caller head.site head.expressionSyntax head.certificates head.body).recapture environment

variable (caller context evidence)

def Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

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

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual catalog/capture receipts construct the whole finite formation leaf.
Static body certificates remain unrestricted and never supply an execution law. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate (registry := registry) (faults := faults) caller context evidence) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨head⟩ := certified
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : Support code registry faults := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      (head.function environment).context (head.function environment).evidence (head.function environment).source
      (head.function environment).captured before code.id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using trace
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using typed
  obtain ⟨result, finalStore, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.preserves_at
      (function := head.function environment) (actual := actual)
      captured code support owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.site.snapshots head.ordinary head.coercions heaps admitted original
  have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.emitted, captured, captures_for] using native
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
    simpa only [model, code, Formation.code, recaptureCode, head.emitted] using represented
  exact ⟨result, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual native formation reflects the original Source leaf with its own
independent grade, preserving the same caller packet and generic heap model. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate (registry := registry) (faults := faults) caller context evidence) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨head⟩ := certified
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : Support code registry faults := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using typed
  have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.emitted, captured, captures_for] using completed
  obtain ⟨sourceSize, outcome, after, trace, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reflects_at
      (function := head.function environment) (actual := actual)
      captured code support owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.site.snapshots head.ordinary head.coercions heaps admitted actualCompleted
  have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using trace
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
    simpa only [model, code, Formation.code, recaptureCode, head.emitted] using represented
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall
/-! A genuine literal ordinary lambda with unrestricted same-Code body support
closes its original callee formation internally. Ordered arguments retain their
actual successful or fault post, then the exact nested parameter receipt selects
the strict shared-family body child. One supplied function model covers every
heap; only the authentic formed closure is included forward. Native and Source
grades remain independent, and the original caller packet restores the same pool. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)
open CallableIndexedOwnedMethodLambdaSelectedCall (Completion completed lambda lambda_function)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- This static row conversion retains every represented value in order. -/
private theorem arguments_of_values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding tail ih => cases represented with
    | cons head rest => exact .cons head (ih rest)

section Parent
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {id : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation function.source scope
    id code.id ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {certificate : GenericExpressionMeaning.Certificate}
  (selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared code)
  (sameCallee : compiler.calleeCode = code.lowered)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (copied : code.policy.snapshotLambda code.id = true)
  (sourceArguments : ExpressionsHaveTypes function.source function.context ids support.body.types)
  (sourceCount : support.body.types.length = metadata.argumentCount)
  (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include wellFormed runtime covers sourceArguments in
/-- Original Source argument preservation supplies both raw parameter types
and deep typing of the actual argument heap. Native vectors are independent. -/
private theorem arguments_admitted {start : Dynamic.Heap}
    (startLocals : Dynamic.EnvironmentAgrees start function.context.locals function.captured)
    (startTyped : Dynamic.HeapWellTyped function.context start)
    {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured start ids arguments middle) :
    Dynamic.ValuesHaveTypes function.context middle arguments support.body.types ∧
      Dynamic.HeapWellTyped function.context middle := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured := by
    intro before after id value type covers locals heapTyped typed execution
    exact wellFormed.wholeLanguagePreservation.expression function.context function.evidence function.source
      function.captured before after id value type runtime covers locals heapTyped typed execution
  have reached := Dynamic.ExpressionsEvaluate.preserves expressionPreserves covers startLocals startTyped sourceArguments trace.sound
  exact ⟨reached.1, reached.2.1⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    functions) captured code
    (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet) heap store
    owner.key.frameLocation)

/-- The caller packet, transported to the formed state that holds the copies
of the callee's captured cells. -/
def formedState : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
    ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩ :=
  (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller).extend ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

/-- Transport relates the caller packet to its formed state. -/
theorem formedState_related : Relates initial (formedState captured code support owner initial packet functions formed).val :=
  (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller).related ⟨initial, packet⟩
    formed.maps formed.worlds formed.frame formed.copy.metadata_extends

include admitted in
/-- Admission holds at the formed state: copies keep the heap typing, and rows
stay stable across the administrative extension. -/
theorem formedState_admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context (formedState captured code support owner initial packet functions formed) :=
  ⟨admitted.heap.copy formed.copy,
    CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial (formedState captured code support owner initial packet functions formed).val
      admitted.rows formed.frame⟩

include profile heaps admitted selection sourceArguments in
/-- The genuine formation value is the real guard prefix of the unchanged
admitted sequence fold. Its Source typing row stays independent of Tree types. -/
theorem sequence_preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
  intro size outcome after trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.preserves
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (formedState captured code support owner initial packet functions formed) (formedState_admitted captured code support owner initial packet functions admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include profile heaps admitted selection sourceArguments in
/-- Native arguments use the same actual guarded input and independent Source
row, preserving the original strict sequence grade. -/
theorem sequence_reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured) :
    ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
  intro size result finalStore trace bounded
  have closureTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact CallableIndexedOwnedAdmittedSequenceProducer.reflects
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (formedState captured code support owner initial packet functions formed) (formedState_admitted captured code support owner initial packet functions admitted formed) selection.children support.unique sourceArguments
    (captured.represented.extend formed.maps formed.worlds) formed.heaps (locals.mono formed.copy.metadata_extends)
    (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix captured.agrees _) .unit)
    (.cons .unit (.cons closureTyped (captured.typed.weaken formed.worlds))) budget children trace bounded

include prefixContext observed syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The actual ordered argument post supplies raw Source admission and its
current owned row to the selected parameter/body prefix. -/
theorem arguments_preserves
    (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize
      function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after)
    (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore result finalStore finalMap finalWorld,
      Evaluates (.unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
        formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native :: formed.closureActual)
        middleStore (code.body.rename formed.embedding.lift.lift) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
        ⟨initial, packet⟩ ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩ := by
  obtain ⟨packed, middleStore, middleMap, middleWorld, argumentEvaluation, argumentResult, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    sequence (.values argumentsTrace) argumentsWithin
  cases argumentResult with
  | @values sources payloads represented =>
    rw [selection.nativeTypes] at represented
    have representedArguments := arguments_of_values code.receipt.loweredParameters represented
    let future := formed.captures.extend argumentMaps argumentWorlds
    let history := formed.closureHistory
    have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
      (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) argumentsTrace
    have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : future.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code support]
      exact (observed.of_slots formed.slots).reference
    have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
      (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
        formed.copy.agrees locals).extend argumentMetadata
    let recaptured : Support formed.closureCode registry faults := support.recapture formed.captured
    have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
        recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
    have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.source_continuation
      (nativeArguments := payloads) (function := formed.closure) future formed.closureCode history recaptured.body.toContext
      functions owner argumentState.val (recaptured.body_origin selection.escaped) raw.2 raw.1 stable support.caller
      (observed.of_slots formed.slots) prefixContext
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin captured code support owner initial packet).metadata
      recapturedSyntax wellFormed rfl budget below
    obtain ⟨result, finalStore, finalMap, finalWorld, bodyEvaluation, resultRep, finalHeaps,
        maps, worlds, frame, metadata, finalState, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at (function := formed.closure)
        future formed.closureCode history recaptured.body.toContext functions
        representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
        (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
        (recaptured.body_origin selection.escaped)
        budget meaning called callWithin
    obtain ⟨returned, _samePool, relatedCaller⟩ :=
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller).restore
        ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
        (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
        (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
        ((formedState_related captured code support owner initial packet functions formed).trans (argumentRelated.trans related))
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    exact ⟨_, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
      resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps), formed.worlds.trans (argumentWorlds.trans worlds),
      formed.frame.trans (argumentFrame.trans frame), formed.copy.metadata_extends.trans (argumentMetadata.trans metadata),
      returned, relatedCaller⟩

include prefixContext observed syntaxTree wellFormed runtime covers locals admitted sourceArguments selection in
/-- The native argument completion reconstructs its own Source grade before
selecting the exact actual body prefix and the same restored caller pool. -/
theorem arguments_reflects (budget : Nat)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument result : Value} {middleStore finalStore : Store}
    (argumentsTrace : EvaluationSize argumentsSize (.unit :: value code formed.embedding
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      formed.finalStore (((SourceCoreCalls.packArguments compiler.codes).expression.rename captured.embedding).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore)
    (argumentsWithin : argumentsSize < budget)
    (bodyTrace : EvaluationSize bodySize (argument :: SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native :: formed.closureActual)
      middleStore (code.body.rename formed.embedding.lift.lift) result finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) sourceArgumentsSize
        function.context function.evidence function.source function.captured formed.finalHeap ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceCallSize
        function.context function.evidence function.evidence middle (.closure formed.closure) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
        ⟨initial, packet⟩ ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩ := by
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
  obtain ⟨sourceArgumentsSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, argumentResult, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    sequence argumentsTrace argumentsWithin
  cases argumentResult with
  | @values sources payloads represented =>
    cases argumentTrace with
    | values sourceArgumentsTrace =>
      rw [selection.nativeTypes] at represented
      have representedArguments := arguments_of_values code.receipt.loweredParameters represented
      let future := formed.captures.extend argumentMaps argumentWorlds
      let history := formed.closureHistory
      have raw := arguments_admitted captured code support sourceArguments wellFormed runtime covers
        (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy) sourceArgumentsTrace
      have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative initial argumentState.val admitted.rows (formed.frame.trans argumentFrame)
      obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
      have reference : future.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code support]
        exact (observed.of_slots formed.slots).reference
      have capturesValid : FunctionValues.SourceCapturesValid middle (.closure formed.closure) :=
        (show FunctionValues.SourceCapturesValid formed.finalHeap (.closure formed.closure) from
          formed.copy.agrees locals).extend argumentMetadata
      let recaptured : Support formed.closureCode registry faults := support.recapture formed.captured
      have recapturedSyntax : GenericImperativeMatch.Syntax function.source (recaptured.expressionSyntax function.source)
          recaptured.body.context (.statements true function.body) function.resultType := syntaxTree
      have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.native_continuation
        (function := formed.closure) future formed.closureCode history recaptured.body.toContext functions owner
        argumentState.val (recaptured.body_origin selection.escaped) raw.2 raw.1 stable support.caller
        (observed.of_slots formed.slots) prefixContext
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin captured code support owner initial packet).metadata
        recapturedSyntax wellFormed rfl budget below
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at (function := formed.closure)
          future formed.closureCode history recaptured.body.toContext functions
          representedArguments owner argumentState.val middleHeaps capturesValid reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed formed.closureCode history)
          (recaptured.body_origin selection.escaped)
          budget meaning bodyTrace bodyWithin
      obtain ⟨returned, _samePool, relatedCaller⟩ :=
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller).restore
          ⟨initial, packet⟩ finalState (formed.maps.trans (argumentMaps.trans maps))
          (formed.worlds.trans (argumentWorlds.trans worlds)) (formed.frame.trans (argumentFrame.trans frame))
          (formed.copy.metadata_extends.trans (argumentMetadata.trans metadata))
          ((formedState_related captured code support owner initial packet functions formed).trans (argumentRelated.trans related))
      exact ⟨sourceArgumentsSize, sourceCallSize, sources, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, formed.maps.trans (argumentMaps.trans maps),
        formed.worlds.trans (argumentWorlds.trans worlds), formed.frame.trans (argumentFrame.trans frame),
        formed.copy.metadata_extends.trans (argumentMetadata.trans metadata), returned, relatedCaller⟩

include selection in
/-- The same original parent type and projected result are retained. -/
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {result : Value}
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result) :
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
      finalMap finalWorld compiler.original.type lowered.type faults outcome result := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, selection.nativeResult]
  cases represented with
  | value related => exact .value (.compatible selection.rawResult related)
  | fault matched => exact .fault matched

variable (parentTyped : ExpressionHasType function.source function.context id compiler.original.type)

/-- Full whole-parent outputs preserve the same actual reached nested Header pool,
with deep admission only on successful Source completion. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
    functions)
    finalMap finalWorld compiler.original.type lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
    PostAdmission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context compiler.original.type outcome reached

include prefixContext observed inclusion selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original ordinary-lambda formation closes the callee internally. Ordered
admitted children and the strict dependent body IH close the whole call. -/
theorem preserves_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, callSize, calleeCaptured, calleeHeap, calleeTrace, calleeCopy, suffix,
      _calleeSmall, argumentsSmall, callWithin⟩ :=
    CallableIndexedOwnedSelectedIndirectHeads.suffix_of_source compiler.found compiler.originalForm parent.coercions
      compiler.argumentCoercions parent.arity (lambda captured code coercions) support.unique wellFormed runtime covers locals
      admitted.heap sourceArguments sourceCount trace
  obtain ⟨formed, _source, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.formation captured code support owner initial packet profile prefixContext observed functions inclusion
      heaps copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional calleeCopy formed.copy
  rw [lambda_function captured code coercions] at calleeTrace suffix
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
    intro size outcome after childTrace childBound
    exact sequence_preserves captured code support owner initial packet profile functions compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [selection.nativeResult] at emitted
  cases suffix with
  | argumentFault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, argumentEvaluation, result, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      sequence (.fault failed) (Nat.le_trans (Nat.le_of_lt argumentsSmall) within)
    cases result with
    | fault matched =>
      rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
      have whole := CallableContract.call_argument_failure (result := code.receipt.resultCore) prepared.site.gates native.diagnostics.unknown
        calleeEvaluation selection.stageAccepted argumentEvaluation
      rw [← emitted] at whole
      exact ⟨_, finalStore, finalMap, finalWorld, whole,
        parent_result captured code functions compiler prepared selection (.fault matched), finalHeaps,
        formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
        formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet functions formed).trans related,
        after_expression_sized (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
          parentTyped trace (formed.frame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, result, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
        resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_preserves captured code support owner initial packet prefixContext observed functions compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace
        (Nat.le_trans (Nat.le_of_lt argumentsSmall) within) called (Nat.le_trans callWithin within)
    have whole := CallableContract.call_success prepared.site.gates native.diagnostics.unknown calleeEvaluation
      selection.stageAccepted argumentEvaluation selection.arityAccepted bodyEvaluation
    rw [← emitted] at whole
    exact ⟨result, finalStore, finalMap, finalWorld, whole,
      parent_result captured code functions compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped trace frame⟩

include prefixContext observed inclusion selection sameCallee copied ordinary coercions parent sourceCount sourceArguments syntaxTree
  wellFormed runtime covers locals heaps admitted parentTyped in
/-- The original native call exposes its measured arguments and body children.
Reflection reconstructs the whole Source parent with independent grades. -/
theorem reflects_bounded (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  obtain ⟨formed, sourceCallee, nativeFormed, _represented, _determined⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.formation captured code support owner initial packet profile prefixContext observed functions inclusion
      heaps copied ordinary coercions
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size sourceCallee
  have calleeEvaluation : Evaluates actual store (compiler.calleeCode.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual)) formed.finalStore := by
    rw [sameCallee]; exact nativeFormed
  have sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
      (program := Program.ofChecked compiled.sourceProgram) (context := function.context) (evidence := function.evidence)
      (source := function.source) (environment := function.captured)
      (actual := .unit :: value code formed.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native formed.closureActual :: actual)
      (ξ := (Renaming.insertion 0).comp ((Renaming.insertion 0).comp captured.embedding)) (ids := ids)
      (sourceTypes := code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) (codes := compiler.codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions) (formedState captured code support owner initial packet functions formed) budget := by
    intro size result finalStore childTrace childBound
    exact sequence_reflects captured code support owner initial packet profile functions compiler prepared selection
      sourceArguments heaps admitted formed budget children locals childTrace childBound
  have emitted := prepared.lowered_rename compiler captured.embedding
  rw [emitted, selection.nativeResult] at trace
  cases completed code (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet) formed.embedding formed.closureActual
      calleeEvaluation selection.stageAccepted selection.arityAccepted trace within with
  | failed argumentsTrace argumentsStrict =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨sourceArgumentsSize, argumentOutcome, after, finalMap, finalWorld, argumentTrace, resultRep, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ := sequence argumentsTrace argumentsStrict
    cases resultRep with
    | fault matched =>
      cases argumentTrace with
      | fault failed =>
        obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
          compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
          wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
          sourceArguments sourceCount calleeTrace
          (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, sourceTrace,
          parent_result captured code functions compiler prepared selection (.fault matched), finalHeaps,
          formed.maps.trans maps, formed.worlds.trans worlds, formed.frame.trans frame,
          formed.copy.metadata_extends.trans metadata, reached, (formedState_related captured code support owner initial packet functions formed).trans related,
          after_expression_sized (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals
            parentTyped sourceTrace (formed.frame.trans frame)⟩
  | applied argumentsTrace bodyTrace argumentsStrict bodyStrict =>
    obtain ⟨sourceArgumentsSize, sourceCallSize, arguments, middle, outcome, after, finalMap, finalWorld,
        sourceArgumentsTrace, called, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_reflects captured code support owner initial packet prefixContext observed functions compiler prepared selection sourceArguments
        syntaxTree wellFormed runtime covers locals admitted formed budget sequence below argumentsTrace argumentsStrict
        bodyTrace (Nat.le_of_lt bodyStrict)
    obtain ⟨sourceSize, sourceTrace⟩ := CallableIndexedOwnedIndirectSourceAdapters.SourceSuffix.to_expression
      compiler.found compiler.originalForm parent.requirements parent.coercions compiler.argumentCoercions parent.arity
      wellFormed runtime covers (locals.mono formed.copy.metadata_extends) (admitted.heap.copy formed.copy)
      sourceArguments sourceCount calleeTrace
      (CallableIndexedOwnedIndirectExpressionHeads.SourceSuffix.called sourceArgumentsTrace called)
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace,
      parent_result captured code functions compiler prepared selection resultRep, finalHeaps,
      maps, worlds, frame, metadata, reached, related,
      after_expression_sized (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals parentTyped sourceTrace frame⟩

/-- The same original compiler selection retains only authentic static ordinary
Source and Code receipts, independent of actual execution. -/
structure Receipt (certificate : GenericExpressionMeaning.Certificate) where
  native : SourceCoreGeneralFunctions.CallableContext
  prepared : Prepared compiler native
  parent : SourceParent compiler
  selection : CallableIndexedOwnedSelectedIndirectHeads.Selection (compiled := compiled)
    (faults := faults) (certificate := certificate) compiler prepared code
  sameCallee : compiler.calleeCode = code.lowered
  ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions []
  coercions : code.sourceNode.coercions = []
  copied : code.policy.snapshotLambda code.id = true
  sourceArguments : ExpressionsHaveTypes function.source function.context ids support.body.types
  sourceCount : support.body.types.length = metadata.argumentCount
  syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
    support.body.context (.statements true function.body) function.resultType
  parentTyped : ExpressionHasType function.source function.context id compiler.original.type

include prefixContext observed inclusion wellFormed runtime covers locals heaps admitted in
/-- This actual static receipt selects the internally proved literal producer;
only genuine strictly smaller argument and extended-family body children remain. -/
theorem preserves_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap id outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename captured.embedding) result finalStore ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  exact preserves_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (prefixContext := prefixContext) (observed := observed) (functions := functions) (inclusion := inclusion) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (copied := issued.copied)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

include prefixContext observed inclusion wellFormed runtime covers locals heaps admitted in
/-- Native receipt selection preserves its measured child bounds while the
whole Source trace and successful admission are reconstructed independently. -/
theorem reflects_at_receipt (issued : Receipt captured code support compiler certificate) (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      function.context function.evidence function.source certificate faults size)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget)
    {size : Nat} {result : Value} {finalStore : Store}
    (trace : EvaluationSize size actual store (lowered.expression.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap id outcome after ∧
      ResultAt captured code support owner initial packet functions compiler outcome after result finalStore finalMap finalWorld := by
  exact reflects_bounded (captured := captured) (code := code) (support := support) (owner := owner)
    (initial := initial) (packet := packet) (profile := profile) (prefixContext := prefixContext) (observed := observed) (functions := functions) (inclusion := inclusion) (compiler := compiler)
    (prepared := issued.prepared) (parent := issued.parent) (selection := issued.selection)
    (sameCallee := issued.sameCallee) (ordinary := issued.ordinary) (coercions := issued.coercions)
    (copied := issued.copied)
    (sourceArguments := issued.sourceArguments) (sourceCount := issued.sourceCount) (syntaxTree := issued.syntaxTree)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heaps := heaps)
    (admitted := admitted) (parentTyped := issued.parentTyped) budget children below trace within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaSelectedCall
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads
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
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
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
      copied := head.formation.site.snapshots, sourceArguments := head.sourceArguments, sourceCount := head.sourceCount,
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionRuntimeBounds
/-! Accepted unrestricted ordinary formation and literal selected calls feed
the same existing expression support fold and finite dispatcher. Runtime literal
meaning comes from the actual Source ledger. Every heap retains supplied
functions; only formed closures are included forward. Strict extended-family
body children remain the shared measured IH, with independent Source grades. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionRuntimeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads (Head)
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (bridge model)
open CallableIndexedOwnedExtendedJointReadyContinuations (PreservingBelow ReflectingBelow)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}

/-- The original Tree construction retains the genuine finite ordinary Head. -/
abbrev Tree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree
    (Head (registry := registry) (faults := faults) caller context evidence)
    fuel (.initial compiled.compatible.checked) source context solved reasonAt

/-- The literal receipt is the actual original Source requirement ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree.WithLiterals
    (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
    (values := .initial compiled.compatible.checked) (source := source) (context := context)
    (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
theorem preserves_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Preserves
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context evidence
      source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.preserves_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) caller context evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CompatibleExpressionBuiltins.preserves_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              evidence unique uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.preserves_at_with_calls
      (bridge (headers := headers) caller owner)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      functions
      extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) caller context evidence) budget child childWithin children
    exact CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads.preserves_at
      caller context evidence owner profile functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
theorem reflects_at_with_literals [FunctionCalls.FaultTokens faults] {literals : GenericExpressionMeaning.Certificate}
    (literalMeaning : GenericExpressionMeaning.Reflects
      (model (registry := registry) functions)
      (Program.ofChecked compiled.sourceProgram) context evidence
      source literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals
        (calls := Head (registry := registry) (faults := faults) caller context evidence) (fuel := fuel)
        (values := .initial compiled.compatible.checked)
        (source := source) (context := context)
        (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  apply CallableIndexedOwnedAdmittedExpressionBounds.reflects_tree_at_with_literals
    functions
    (Head (registry := registry) (faults := faults) caller context evidence) budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful
      wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _
        (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CompatibleExpressionBuiltins.reflects_with_literals
              functions
              extension faithful observations functionTypes (Program.ofChecked compiled.sourceProgram)
              evidence uninitialized missing literalMeaning)) child))
  · intro certificate child childWithin children
    apply CallableIndexedOwnedAdmittedExpressionCallsHeads.reflects_at_with_calls
      (bridge (headers := headers) caller owner)
      (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
      functions
      extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (Head (registry := registry) (faults := faults) caller context evidence) budget child childWithin children
    exact CallableIndexedOwnedGeneralOrdinaryLambdaExpressionHeads.reflects_at
      caller context evidence owner profile functions inclusion complete globals slots prefixZero wellFormed runtime covers sameSource budget child childWithin
      (fun smaller strict => children smaller (Nat.le_of_lt strict)) below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem preserves_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : PreservingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (RuntimeTree (registry := registry) (faults := faults) (source := source) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) caller context evidence) faults size := by
  exact preserves_at_with_literals caller context evidence owner profile functions inclusion complete globals prefixZero slots extension faithful observations
    functionTypes wellFormed runtime covers sameSource unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.preserves
      functions
      (Program.ofChecked compiled.sourceProgram) context evidence sameLedger runtimeLedger unique faults)
    budget size within below

include inclusion complete globals prefixZero slots extension faithful observations functionTypes wellFormed runtime covers sameSource unique uninitialized missing in
/-- The runtime literal producer and concrete heads discharge expression
semantics internally through the original support fold. -/
theorem reflects_at_runtime [FunctionCalls.FaultTokens faults] (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (budget size : Nat) (within : size ≤ budget)
    (below : ReflectingBelow (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions wellFormed budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      (bridge (headers := headers) caller owner)
      (model (registry := registry) functions)
      context evidence source
      (RuntimeTree (registry := registry) (faults := faults) (source := source) (solved := solved)
        (reasonAt := reasonAt) (fuel := fuel) caller context evidence) faults size := by
  exact reflects_at_with_literals caller context evidence owner profile functions inclusion complete globals prefixZero slots extension faithful observations
    functionTypes wellFormed runtime covers sameSource unique uninitialized missing
    (CompatibleExpressionLiteralRuntime.reflects
      functions
      (Program.ofChecked compiled.sourceProgram) context evidence sameLedger runtimeLedger source faults)
    budget size within below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaExpressionRuntimeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
/-! An ordinary lambda certificate contains only its authentic ranked static
receipt. The generic admitted leaf constructs captures, code and history from
the actual input environment and nested packet through the original producer.
The additive model is used throughout the input heap and returned payload. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedLambdaNestedRuntimeBodyMeaning RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}

/-- Static formation support fixes the genuine Header and original Source
occurrence. Captures and runtime authority are supplied at the actual input. -/
def Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ rank, Nonempty
    (LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)

def bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)

def model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
  (CallableIndexedOwnedMethodLambdaValues.model headers keys registry faults profile)

variable
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)

include complete globals slots prefixZero wellFormed runtime covers sameSource unique in
/-- The original finite formation proof is selected by the static certificate
and consumes exactly the caller packet and represented environment it receives. -/
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (headers := headers) (bridge (headers := headers) caller owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) context evidence source
      (Certificate (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨rank, ⟨head⟩⟩ := certified
  have sourceFound : source.lookupExpression? id = some head.code.sourceNode := by
    simpa only [sameSource, CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨result, finalStore, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.preserves_at head profile complete globals slots owner prefixZero
      initial.val initial.property environments agrees nativeTyped wellFormed runtime covers locals typed
      sameSource unique heaps admitted trace
  exact ⟨result, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

include complete globals slots prefixZero wellFormed runtime covers sameSource unique in
/-- Native completion is reflected by the same authentic formation producer;
the original Source formation is independently sized at the unchanged pool. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (headers := headers) (bridge (headers := headers) caller owner)
      (model (headers := headers) (keys := keys) (registry := registry) (faults := faults) profile) context evidence source
      (Certificate (headers := headers) (registry := registry) (faults := faults)
        (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨rank, ⟨head⟩⟩ := certified
  have sourceFound : source.lookupExpression? id = some head.code.sourceNode := by
    simpa only [sameSource, CallableIndexedLambdaGeneration.closure, head.identifier] using head.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨sourceSize, outcome, after, trace, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedOrdinaryLambdaFormation.reflects_at head profile complete globals slots owner prefixZero
      initial.val initial.property environments agrees nativeTyped wellFormed runtime covers locals typed
      sameSource unique heaps admitted completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaFormationHeads
end
