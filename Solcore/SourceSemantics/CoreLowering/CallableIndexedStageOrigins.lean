import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientStageOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationHeads

/-! Actual indexed function leaves retain source preparation alongside their
same Code and History. The real stage table turns those static receipts into
callsite coverage under the same ambient function model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues

variable {values : SourceCoreCompatibleValues.Context}
  (indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked)

/-- Source preparation is separate from the captured history and native type. -/
def provenanceCondition (checkedProgram : CheckedProgram) (support : SupportFamily indexed)
    (prior : SupportCondition indexed support) : SupportCondition indexed support :=
  fun {_ _ function _ _} captured code history body =>
    prior captured code history body ∧
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source

theorem provenance_stable (checkedProgram : CheckedProgram) (support : SupportFamily indexed)
    (prior : SupportCondition indexed support)
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures indexed mapping world scope function.captured actual)
      (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)
    (supported : provenanceCondition indexed checkedProgram support prior captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    provenanceCondition indexed checkedProgram support prior (captured.extend maps worlds) code history body :=
  ⟨stable captured code history body supported.1 maps worlds, supported.2⟩

/-- The retained branch keeps its actual parameter order and full dictionary. -/
theorem retained_origin {checkedProgram : CheckedProgram}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : CallableIndexedRetainedNamedValues.Represents indexed world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier := by
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin builtin =>
      cases builtin with
      | builtin selected number descriptor typed =>
        exact RecursiveStageProjection.builtin_origin accepted descriptor _
    | named row number projection descriptor native =>
      apply RecursiveStageProjection.named_origin accepted descriptor
      simpa only [CallableNamedReversal.global, CallableNamedReversal.target_reverse,
        CallableNamedMetadata.global] using row.target

/-- Only function-leaf constructors are inspected. Data representation keeps
its existing single induction in CompatibleAmbientStageOrigins. -/
theorem origin_of_represents {checkedProgram : CheckedProgram}
    {support : SupportFamily indexed} {prior : SupportCondition indexed support}
    {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : RepresentsWith indexed support (provenanceCondition indexed checkedProgram support prior)
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier := by
  cases related with
  | retained prior => exact retained_origin indexed accepted prior
  | lambda captured code history body supported typed =>
    exact CompatibleAmbientStageOrigins.actual_lambda_origin accepted code.descriptor supported.2.1
      code.viewOfSource supported.2.2 code.found (code.form.trans code.sourceForm) _

section Coverage
variable {checkedProgram : CheckedProgram} {support : SupportFamily indexed}
  {prior : SupportCondition indexed support}
  (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
    prior captured code history body →
    ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
    prior (captured.extend maps worlds) code history body)
  (profile : values.checked.catalog.callableContracts = true)

abbrev model : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions indexed) :=
  modelWith indexed support (provenanceCondition indexed checkedProgram support prior)
    (provenance_stable indexed checkedProgram support prior stable) profile

theorem function_origins {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table)
    {registry : SourceCoreRawMetadata.Registry} {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = indexed.base.plan)
    (sameTable : site.table = indexed.ancestry.graph.inputs.callable.table) :
    CompatibleAmbientStageOrigins.FunctionOrigins
      (model indexed stable profile (checkedProgram := checkedProgram)) registry sidecar site := by
  intro mapping world sourceType source carrier type related
  rw [samePlan, sameTable]
  exact origin_of_represents indexed accepted related

end Coverage

private theorem callsite_table {table : SourceCoreStageCodebook.Table}
    {owner : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table owner call reasonAt = .ok site) :
    site.table = table := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

/-- Public preparation fixes both tables and the full sidecar plan. Function
origins are derived from this same model, rather than supplied as a law. -/
theorem actual_coverage
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {support : SupportFamily (values := .initial compiled.compatible.checked) compiled.indexed}
    {prior : SupportCondition (values := .initial compiled.compatible.checked) compiled.indexed support}
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (registry : SourceCoreRawMetadata.Registry) (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (model (values := .initial compiled.compatible.checked) compiled.indexed stable profile (checkedProgram := compiled.sourceProgram)))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have sameNative : native = compiled.indexed.ancestry.graph.inputs.callable :=
    Option.some.inj (prepared.present.symm.trans compiled.indexed.ancestry.graph.inputs.callableSelected)
  have accepted := prepared.accepted
  rw [sameNative] at accepted
  intro mapping world source carrier contract represented bound
  exact CompatibleAmbientStageOrigins.actual_coverage (rawRegistry := registry)
    (functions := model (values := .initial compiled.compatible.checked) compiled.indexed stable profile
      (checkedProgram := compiled.sourceProgram)) prepared issued caller contains form
    (function_origins (values := .initial compiled.compatible.checked) compiled.indexed stable profile accepted
      (CallContractCertificates.sidecar_of_accepted caller).1
      ((callsite_table issued).trans (congrArg SourceCoreGeneralFunctions.CallableContext.table sameNative))) sourceType type represented bound

/-- The indexed artifact already retains its present callable context.
This entry constructs the real stage preparation receipt internally. -/
theorem actual_compiled_coverage
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    {support : SupportFamily (values := .initial compiled.compatible.checked) compiled.indexed}
    {prior : SupportCondition (values := .initial compiled.compatible.checked) compiled.indexed support}
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code) (body : support code),
      prior captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      prior (captured.extend maps worlds) code history body)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite compiled.indexed.ancestry.graph.inputs.callable.table context.owner node.id
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (registry : SourceCoreRawMetadata.Registry) (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (model (values := .initial compiled.compatible.checked) compiled.indexed stable profile (checkedProgram := compiled.sourceProgram)))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  intro mapping world source carrier contract represented bound
  exact actual_coverage compiled stable profile prepared issued caller contains form registry sourceType type represented bound

section Formation
open ReadOnly RecursiveNamedLambdaFormationHeads RecursiveNamedLambdaFormationEntries

variable {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {caller : RecursiveNamedCatalog.Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : LambdaWith expressionSyntax certificates (registry := registry) (faults := faults)
    caller context evidence scope id lowered)
  {compilation : SourceCoreFunctions.Context} {capturePrefix : Nat}
  (header : FormationHeader (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller compilation capturePrefix)

include header in
/-- The ordinary generation site supplies its original source preparation;
the static body independently supplies uniqueness of the complete source. -/
theorem formation_receipt (checkedProgram : CheckedProgram) (environment : Dynamic.Environment) :
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      (head.actualCode environment).compilation.owner (head.actualCode environment).active
      (head.formed environment).source ∧ NodeOccurrencesUnique (head.formed environment).source := by
  constructor
  · change LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      head.code.compilation.owner head.code.active (CallableIndexedNamedGeneration.source caller.named)
    rw [head.compilation, head.active]
    exact .original header.record
  · exact (head.actualBody environment).unique

variable {headers : RecursiveNamedCatalog.Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ other, other ∈ headers → other.slot < indexed.base.globals.length)
  (entry : RecursiveNamedLambdaFormationEntries.Entry
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1
    scope mapping world heap store canonical)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative scope environment canonical indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)

abbrev bodySupport : SupportFamily indexed :=
  fun code => CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults

abbrev capturePrior : SupportCondition indexed
    (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
      (program := program) (registry := registry) (faults := faults)) :=
  captureCondition indexed program _ (fun _ _ => True) (headers := headers) (locations := locations) 1

include header slots in
/-- Both origin and capture conditions are built at this actual formation.
No relation on an already represented weak heap is strengthened. -/
theorem formation_condition (checkedProgram : CheckedProgram) :
    provenanceCondition indexed checkedProgram
      (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
        (program := program) (registry := registry) (faults := faults))
      (capturePrior indexed (headers := headers) (locations := locations)
        (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults))
      (captures complete globals entry related agrees typed) (head.actualCode environment)
      (head.history entry environment) (head.actualBody environment) := by
  exact ⟨head.capture_condition (fun _ _ => True) complete globals slots entry related agrees typed trivial,
    formation_receipt indexed head header checkedProgram environment⟩

variable (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store indexed.layouts.definitions)

include header slots profile stored in
/-- Source formation and native formation retain the same actual full store
and captured environment under the stronger static predicate. -/
theorem formation (checkedProgram : CheckedProgram) :
    let captured := captures complete globals entry related agrees typed
    let code := head.actualCode environment
    let history := head.history entry environment
    Dynamic.ExpressionEvaluates program context evidence (head.formed environment).source environment heap
      code.id (.closure (head.formed environment)) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    RepresentsWith indexed (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
        (program := program) (registry := registry) (faults := faults))
      (provenanceCondition indexed checkedProgram _ (capturePrior indexed (headers := headers) (locations := locations)
        (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults)))
      mapping world (FunctionValues.sourceType (head.formed environment)) (.closure (head.formed environment))
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  exact CallableIndexedLambdaRuntimeValues.formation_with indexed program
    (captures complete globals entry related agrees typed) (head.actualCode environment) (head.history entry environment)
    (head.actualBody environment)
    (formation_condition indexed head header complete globals slots entry related agrees typed checkedProgram)
    profile stored (head.reference complete globals entry related agrees typed) entry.catalog.authority.frame.read
    heap head.ordinary head.coercions

include header slots profile stored in
/-- The original native completion gives the same source formation, result,
and full store. The static predicate is built from the actual site again. -/
theorem reflects_original (checkedProgram : CheckedProgram) {result : Value} {after : Store}
    (completed : Evaluates actual store
      ((head.actualCode environment).lowered.expression.rename ξ) result after) :
    let captured := captures complete globals entry related agrees typed
    let code := head.actualCode environment
    let history := head.history entry environment
    result = .inRight .word (value code captured.embedding history.native actual) ∧ after = store ∧
    Dynamic.ExpressionEvaluates program context evidence (head.formed environment).source environment heap
      code.id (.closure (head.formed environment)) heap ∧
    RepresentsWith indexed (bodySupport indexed (expressionSyntax := expressionSyntax) (certificates := certificates)
        (program := program) (registry := registry) (faults := faults))
      (provenanceCondition indexed checkedProgram _ (capturePrior indexed (headers := headers) (locations := locations)
        (expressionSyntax := expressionSyntax) (certificates := certificates) (registry := registry) (faults := faults)))
      mapping world (FunctionValues.sourceType (head.formed environment)) (.closure (head.formed environment))
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  exact CallableIndexedLambdaRuntimeValues.reflects_with indexed program
    (captures complete globals entry related agrees typed) (head.actualCode environment) (head.history entry environment)
    (head.actualBody environment)
    (formation_condition indexed head header complete globals slots entry related agrees typed checkedProgram)
    profile stored (head.reference complete globals entry related agrees typed) entry.catalog.authority.frame.read
    heap head.ordinary head.coercions completed

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
