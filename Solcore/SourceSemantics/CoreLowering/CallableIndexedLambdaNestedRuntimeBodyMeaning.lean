import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNamedRuntimeBodyMeaning

/-! Nested formation uses the same ranked static receipts and function model
as every argument and heap value. Runtime decrease remains the original body
size; only nested literal support uses the independent static rank. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedLambdaFormationHeads
open CallableIndexedLambdaNestedRuntimeCertificates

variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

abbrev LowerSupport (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) (rank : Nat) :
    RankedSupport (indexed := indexed) :=
  fun childRank {_ _ _} code => if _smaller : childRank < rank then
    BodyAt headers caller registry faults childRank code else Empty

abbrev LambdaAt (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (rank : Nat) (source : TypedSource) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :=
  CallableIndexedLambdaNestedRuntimeCertificates.Lambda
    (LowerSupport headers caller registry faults rank) rank caller source context evidence

section Leaf
variable (head : LambdaAt headers caller registry faults rank source context evidence scope id lowered)

def formed (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def actualCode (environment : Dynamic.Environment) : Code indexed (formed head environment) scope (nativePrefix caller) :=
  recaptureCode head.code environment

def childBody : BodyAt headers caller registry faults head.childRank head.code := by
  simpa only [LowerSupport, dif_pos head.smaller] using head.body

def actualSupport (environment : Dynamic.Environment) :
    Support headers registry faults (actualCode head environment) :=
  ⟨caller, head.childRank, (childBody head).recapture environment⟩

def historyAt {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (environment : Dynamic.Environment) : History (actualCode head environment) where
  native := entry.catalog.authority.current
  ghost := entry.catalog.authority.ghost
  metadata := CallableIndexedNamedGeneration.state caller.named
  carried := entry.history
  source := rfl
  owner := by change caller.named.signature.key = head.code.compilation.owner; rw [head.compilation]; rfl
  active := head.active.symm

theorem reference_index : head.code.referenceIndex = scope.length + 1 + indexed.base.globals.length := by
  simp only [Code.referenceIndex, head.compilation, SourceCoreCallableIndexedAncestry.creationReferenceIndex,
    CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext]

/-- No current ghost is replaced while forming the nested value. Captured
history and the finite global prefix are built from the same reached state. -/
theorem formation
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {ξ : Renaming}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store indexed.layouts.definitions) :
    ∃ value,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head environment)) heap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) store ∧
      CompatiblePayload.ValueRep values.checked registry
        (model headers locations registry faults profile)
        mapping world head.code.sourceNode.type (.closure (formed head environment)) value lowered.type := by
  let captured : Captures indexed mapping world scope environment actual := captures_for complete globals entry related agrees typed
  let code : Code indexed (formed head environment) scope captured.administrative := actualCode head environment
  let history : History code := historyAt head entry environment
  let body : Support headers registry faults code := actualSupport head environment
  have supported : Condition (registry := registry) (faults := faults) headers locations
      (function := formed head environment) (scope := scope) (mapping := mapping) (world := world) (actual := actual) captured code history body := by
    change history.metadata = CallableIndexedNamedGeneration.state caller.named ∧ ∃ location,
      CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations 1 scope captured.canonical location
    exact ⟨rfl, entry.catalog.authority.frameLocation, capture_globals_for complete globals slots entry related agrees typed⟩
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef indexed.ancestry.layout.frame.type entry.catalog.authority.frameLocation) := by
    have bound : head.code.referenceIndex < scope.length + (nativePrefix caller).length := by
      rw [reference_index head]
      simp only [nativePrefix, List.length_cons, List.length_append, List.length_map, List.length_nil]
      omega
    change (canonical.take (scope.length + (nativePrefix caller).length))[head.code.referenceIndex]? = _
    rw [List.getElem?_take, if_pos bound, reference_index head, ← globals]
    exact entry.reference
  obtain ⟨sourceValue, native, represented⟩ := CallableIndexedLambdaRuntimeValues.formation_with
    indexed program (function := formed head environment) (scope := scope)
    (support := Support headers registry faults) (P := Condition headers locations)
    captured code history body supported profile stored reference entry.catalog.authority.frame.read heap
    (by change Dynamic.OrdinaryRequirementLayout head.code.sourceNode.requirements head.code.sourceNode.coercions []; rw [head.requirements, head.coercions]; rfl) head.coercions
  refine ⟨CallableIndexedLambdaValues.value code captured.embedding history.native actual, ?_, ?_, ?_⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (formed head environment)) heap at sourceValue
    simpa only [head.identifier] using sourceValue
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code captured.embedding history.native actual)) store)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.emitted)) native
  · rw [head.sourceType, head.nativeType]
    exact .function represented

local notation "F" => model headers locations registry faults
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1

theorem preserves_leaf_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (size : Nat) (unique : NodeOccurrencesUnique source) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (F profile)) program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt headers caller registry faults rank source context evidence scope id lowered)) faults P := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    related heaps locals agrees typed installed trace
  obtain ⟨leaf⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some leaf.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, leaf.identifier] using leaf.code.sourceFound
  rw [sameSource] at found unique trace
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  cases trace.sound with
  | value evaluated =>
    rename_i result
    have original : Dynamic.ExpressionEvaluates program (formed leaf environment).context (formed leaf environment).evidence
        (formed leaf environment).source (formed leaf environment).captured before leaf.code.id result after := by
      simpa only [formed, CallableIndexedLambdaGeneration.closure, leaf.identifier] using evaluated
    obtain ⟨rfl, rfl⟩ := source_value_of_code (actualCode leaf environment) unique leaf.coercions original
    obtain ⟨value, _, native, represented⟩ := formation leaf profile complete globals slots entry related agrees typed heaps.runtime_hasTypes
    exact ⟨.inRight .word value, store, mapping, world, native, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | fault failed =>
    rename_i reason
    apply False.elim
    apply excludes_fault_of_code (program := program) (actualCode leaf environment) unique leaf.coercions
    change Dynamic.ExpressionFaults program context evidence (CallableIndexedNamedGeneration.source caller.named) environment before leaf.code.id reason after
    simpa only [leaf.identifier] using failed

theorem reflects_leaf_at
    (profile : values.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
    (globals : caller.globals = indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry (F profile)) program context evidence source
      (fun scope id lowered => Nonempty (LambdaAt headers caller registry faults rank source context evidence scope id lowered)) faults P := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    related heaps locals agrees typed installed completed
  obtain ⟨leaf⟩ := certified
  obtain ⟨entry⟩ := installed
  have sourceFound : (CallableIndexedNamedGeneration.source caller.named).lookupExpression? id = some leaf.code.sourceNode := by
    simpa only [CallableIndexedLambdaGeneration.closure, leaf.identifier] using leaf.code.sourceFound
  rw [sameSource] at found
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨nativeValue, sourceValue, native, represented⟩ := formation leaf profile complete globals slots entry related agrees typed heaps.runtime_hasTypes
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id
      (.value (.closure (formed leaf environment))) before := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceValue)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, before, mapping, world, sized, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

end Leaf

section Expressions
variable
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
local notation "Calls" => CallableIndexedLambdaNestedRuntimeCertificates.Head
  (LowerSupport headers caller registry faults rank) rank caller headers
  (CallableIndexedNamedGeneration.context indexed caller.named) source context evidence
local notation "Cert" => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
  (LowerSupport headers caller registry faults rank) rank caller headers
  (CallableIndexedNamedGeneration.context indexed caller.named) fuel source context evidence solved reasonAt

private theorem observations : CompatibleEquality.FunctionObservations values.checked.catalog F (Identity indexed) :=
  CallableIndexedLambdaRuntimeValues.observationsWith indexed (Support headers registry faults) (Condition headers locations)
    (condition_stable (headers := headers) (locations := locations) (registry := registry) (faults := faults)) profile

private theorem runtimeViews : FunctionRuntimeViews F :=
  CallableIndexedLambdaRuntimeValues.runtimeViewsWith indexed (Support headers registry faults) (Condition headers locations)
    (condition_stable (headers := headers) (locations := locations) (registry := registry) (faults := faults)) profile

include complete globals slots extension family valid sameSource unique owners uninitialized missing in
/-- The same expression fold closes ordered children. Only actual named callee
profiles enter the existing catalog strong induction; nested formation supplies
its smaller static receipt without a runtime body execution premise. -/
theorem expressions_preserves_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry F) program context evidence source Cert faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.preserves_at_runtime_evidence
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) owners
    family.uninitialized family.missing family.escaped family.prefixMatches family.profiles
  intro scope id lowered certified
  exact RecursiveNamedExpressionTreeBounds.preserves_at_with_literals_with_for (fuel := fuel)
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence unique uninitialized missing
    Calls P (CompatibleExpressionLiteralRuntime.preserves F program context evidence valid.ledger valid.runtime unique faults)
    budget size within (by
      intro certificate child childWithin children
      apply RecursiveNamedExpressionTreeBounds.head_preserves_at_with_calls
        F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence unique missing
        P CallableIndexedLambdaNestedFormationEntries.transport Calls budget child childWithin children
      intro scope id lowered receipt
      cases receipt with
      | lambda leaf =>
        exact preserves_leaf_at profile complete globals slots sameSource child unique ⟨leaf⟩
      | existing receipt =>
        exact CallableIndexedLambdaNamedRuntimeBodyMeaning.head_preserves_for F P
          CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.catalog
          (fun _ => fun _ => True) (fun _ _ => by unfold RecursiveNamedCatalogInvocationBounds.BodyAuthorization; intros; trivial)
          budget child childWithin valid.runtime.idsUnique unique owners
          (fun smaller strict => children smaller (Nat.le_of_lt strict))
          (by
            intro header member smaller _ arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
            exact bodies smaller header member entry trace) receipt) certified

include complete globals slots extension family valid sameSource uninitialized missing in
/-- Native reflection uses the original ordered children and obtains an
independent source grade. Formation compares only the same pure native leaf. -/
theorem expressions_reflects_at (budget size : Nat) (within : size ≤ budget) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry F) program context evidence source Cert faults P := by
  have bodies := RecursiveNamedCatalogMutualMeaning.reflects_at_runtime_evidence
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile)
    family.uninitialized family.missing family.escaped family.prefixMatches family.profiles
  intro scope id lowered certified
  exact RecursiveNamedExpressionTreeBounds.reflects_at_with_literals_with_for (fuel := fuel)
    F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence uninitialized missing
    Calls P (CompatibleExpressionLiteralRuntime.reflects F program context evidence valid.ledger valid.runtime source faults)
    budget size within (by
      intro certificate child childWithin children
      apply RecursiveNamedExpressionTreeBounds.head_reflects_at_with_calls
        F extension (identity_faithful indexed) (observations profile) (runtimeViews profile) evidence missing
        P CallableIndexedLambdaNestedFormationEntries.transport Calls budget child childWithin children
      intro scope id lowered receipt
      cases receipt with
      | lambda leaf => exact reflects_leaf_at profile complete globals slots sameSource child ⟨leaf⟩
      | existing receipt =>
        exact CallableIndexedLambdaNamedRuntimeBodyMeaning.head_reflects_for F P
          CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.catalog
          (fun _ => fun _ => True) (fun _ _ => by unfold RecursiveNamedCatalogInvocationBounds.BodyAuthorization; intros; trivial)
          budget child childWithin (fun smaller strict => children smaller (Nat.le_of_lt strict))
          (by
            intro header member smaller _ arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after _ trace
            exact bodies smaller header member entry trace) receipt) certified
end Expressions

section Body
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)

abbrev Body (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) (rank : Nat)
    (code : Code indexed function outerScope administrative) :=
  BodyReceipt (LowerSupport headers caller registry faults rank) rank caller headers code registry faults

/-- The actual compiler view supplies the canonical Tree through the shared
transport. The same dictionary and every ordered child code remain in the receipt. -/
theorem Body.of_tree
    (sameSource : function.source = CallableIndexedNamedGeneration.source caller.named)
    (sameCompilation : code.compilation = CallableIndexedNamedGeneration.context indexed caller.named)
    (sameActive : code.active = []) (sameAdministrative : administrative = nativePrefix caller)
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree indexed.layouts code.compilation.owner code.active
      indexed.ancestry.layout.frame indexed.base.globals.length code.allocationError values code.view
      (Nodes code.view)
      (fun context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation readFuel code.view context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body headers caller registry faults rank code,
      body.body.toContext = inputs ∧ body.body.readFuel = readFuel ∧ body.body.policy = policy ∧ body.body.flow = flow := by
  obtain ⟨body, sameContext, sameFuel, samePolicy, sameFlow, _⟩ :=
    CallableIndexedLambdaStaticBodySupport.BodyWith.of_tree
      (expressionSyntax := Nodes)
      (certificates := fun fuel source context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation fuel source context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      code inputs frame readFuel policy callback edited avoids unique sameLedger
      (fun id reached receipt => by
        obtain ⟨node, found⟩ := receipt
        exact ⟨node, (CallableLambdaBodyReachability.expression_lookup edited avoids reached).trans found⟩)
      (fun _ _ _ _ reached receipt => CallableIndexedLambdaNestedRuntimeCertificates.transport
        ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
        (avoids.view edited.metadata) receipt (reached.metadata edited.metadata))
      projection generated sites
  exact ⟨⟨sameSource, sameCompilation, sameActive, sameAdministrative, body⟩, sameContext, sameFuel, samePolicy, sameFlow⟩

def Body.toKernel (body : Body headers caller registry faults rank code) :
    CallableRuntimeBodyKernel.BodyFor indexed.layouts code.compilation.owner code.active
      indexed.ancestry.layout.frame indexed.base.globals.length code.allocationError values function
      (Nodes function.source)
      (fun context => CallableIndexedLambdaNestedRuntimeCertificates.Certificates
        (LowerSupport headers caller registry faults rank) rank caller headers code.compilation body.body.readFuel function.source context
        function.evidence code.compilation.solvedRequirements code.reasonAt)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions indexed)
      administrative body.body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults :=
  { flow := body.body.flow, tree := body.body.tree, sites := body.body.sites, initialValid := body.body.valid,
    projection := body.body.projection, unique := body.body.unique, emitted := body.body.emitted }

end Body

section Execution
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code indexed function outerScope administrative)
  (body : Body headers caller registry faults rank code)
  (profile : values.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (globals : caller.globals = indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < indexed.base.globals.length)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (family : CallableIndexedLambdaNamedRuntimeBodyMeaning.CatalogFamily headers locations 0
    (model headers locations registry faults profile) registry faults)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))
  (escaped : faults .controlEscapedFunction code.compilation.internalReason)
local notation "F" => model headers locations registry faults profile
local notation "P" => CallableIndexedLambdaNestedFormationEntries.protectedEntry caller headers locations 0 1
include body complete globals slots extension owners family uninitialized missing escaped in
/-- The source grade is the original parent-supplied body grade. Named callee
meaning is closed by CatalogFamily's static profiles and the existing mutual
induction; the lambda ghost remains in its independent source entry. -/
theorem Body.preserves_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function body.body.context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry F) program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (LowerSupport headers caller registry faults rank) rank caller headers code.compilation
          body.body.readFuel function.source context function.evidence code.compilation.solvedRequirements code.reasonAt) faults (P)) := by
    intro context valid child within scope id lowered certified
    apply expressions_preserves_at (rank := rank) (fuel := body.body.readFuel) (solved := code.compilation.solvedRequirements)
      profile complete globals slots extension family valid body.source body.body.unique owners uninitialized missing budget child within
    simpa only [body.compilation] using certified
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.preserves_sized F rfl (CallableIndexedAmbient.frame_registered indexed) extension program
      (identity_faithful indexed) (observations profile) escaped
      CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata, entry⟩

include body complete globals slots extension family uninitialized missing escaped in
/-- Reflection consumes the original native body witness. No source execution
or preservation theorem is used to obtain its independent source grade. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      environment canonical indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry F mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before body.body.context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext indexed.layouts.definitions)
    (reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope).length +
      1 + indexed.base.globals.length]? = some (.cellRef indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (encode indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : P
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
      mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function body.body.context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry F)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry F finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      P
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ outerScope)
        finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context,
      CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry F) program context function.evidence function.source
        (CallableIndexedLambdaNestedRuntimeCertificates.Certificates
          (LowerSupport headers caller registry faults rank) rank caller headers code.compilation
          body.body.readFuel function.source context function.evidence code.compilation.solvedRequirements code.reasonAt) faults (P)) := by
    intro context valid child smaller scope id lowered certified
    apply expressions_reflects_at (rank := rank) (fuel := body.body.readFuel) (solved := code.compilation.solvedRequirements)
      profile complete globals slots extension family valid body.source uninitialized missing budget child (Nat.le_of_lt smaller)
    simpa only [body.compilation] using certified
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, entry⟩ :=
    body.toKernel.reflects_sized F rfl (CallableIndexedAmbient.frame_registered indexed) extension program
      (identity_faithful indexed) (observations profile) (runtimeViews profile) escaped
      CallableIndexedLambdaNestedFormationEntries.transport CallableIndexedLambdaNestedFormationEntries.binds
      (fun valid extended => valid.extend extended) (fun valid => valid) budget size within expressions
      environments heaps locals agrees typed reference read unmapped installed evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, entry⟩
end Execution

section ReachedEntry
variable {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code indexed function outerScope administrative} {history : History code}
  (body : Body headers caller registry faults rank code)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {environment : Dynamic.Environment} {canonical : Environment} {before : Dynamic.Heap} {store : Store}

/-- The actual lambda ghost and full carried metadata are retained. Only the
bundle tag uses the original reached environment's independent type relation. -/
def Body.entry_of_source
    (installed : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0
      code.compilation.administrativePrefix scope mapping world before store canonical)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state caller.named)
    (globals : caller.globals = indexed.base.globals.length)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical indexed.layouts.definitions) :
    CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world before store canonical := by
  have samePrefix : code.compilation.administrativePrefix = 1 := by
    rw [body.compilation]
    rfl
  have same : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations 0 1
      scope mapping world before store canonical := by simpa only [samePrefix] using installed
  exact CallableIndexedLambdaNestedFormationEntries.Entry.of_lambda same metadata
    (CallableIndexedLambdaNestedFormationEntries.bundle_of_environment related (by rw [body.administrative]; rfl)) globals
end ReachedEntry
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning
