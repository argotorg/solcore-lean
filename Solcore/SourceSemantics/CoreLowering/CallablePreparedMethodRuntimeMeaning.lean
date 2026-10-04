import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentMeaning
import Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection

/-! Actual prepared methods retain their independent trait-method source frame,
full dictionary and installed code. The body profile is static and uses reached
builtin runtime certificates, including the complete unused requirement ledger.
Original native prefix witnesses supply every finite body bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

/-- The actual measured marked prefix, with no unsized-to-sized recovery. -/
structure Prefix (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) (size : Nat) (result : Value) (afterStore : Store) where
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  childSize : Nat
  completed : EvaluationSize childSize actualBody store (body.rename embedding) result afterStore
  bounded : childSize ≤ size
  strict : bindings ≠ [] → childSize < size

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih


theorem parameter_prefix_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    ∃ entry : Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs)
      (by simpa using reference) read unmapped completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length
      (DataPatternValues.packValues nativeArguments) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  have finalReference : finalLogical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : bindings.length + 1 + globals = added.length + (globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  refine ⟨⟨environment, heap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, child, bodyCompletion, childLe, childStrict⟩, added, prefixLength, ?_⟩
  exact logicalEq

theorem parameter_prefix
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    Nonempty (Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore) := by
  obtain ⟨entry, _⟩ := parameter_prefix_with_spine functions onError accepted parameters inputs extended definitions registered
    represented environments heaps initialLocals actualLayout actualTyped reference read unmapped completed
  exact ⟨entry⟩

section ConcreteBody
structure Body (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (function : Dynamic.Closure)
    (expressionSyntax : ExpressionId → Prop) (readFuel : Nat) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (administrative : Core.Context) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (output : Ty) (code : Expr) (fellThrough escaped : Word)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  flow : Expr
  tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values
      function.source context solved reasonAt) ambient.definitions administrative context scope
    (.statements true function.body) function.resultType output flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence
  projection : values.checked.catalog.project function.resultType = .ok output
  unique : NodeOccurrencesUnique function.source
  emitted : code = CompatibleStatements.finish output flow fellThrough escaped

private abbrev builtinEntry : ProtectedExpressionMeaning.Entry := fun _ _ _ _ _ _ => True
private theorem builtinTransport : ProtectedExpressionMeaning.Transport builtinEntry := ⟨fun _ _ _ _ _ => True.intro⟩
private theorem builtinBindings : ProtectedExpressionMeaning.Binds builtinEntry :=
  ⟨fun _ => True.intro, fun _ => True.intro⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {output : Ty} {code : Expr} {fellThrough escaped : Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body layouts owner active frameLayout globals onError values function expressionSyntax readFuel solved reasonAt
    ambient administrative context scope output code fellThrough escaped registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)

/-- A covering dictionary changes only the source evidence field. The actual
flow, tree, sites, and complete runtime ledger are retained verbatim. -/
def Body.with_evidence (dictionary : Dynamic.EvidenceEnvironment) (covers : dictionary.Covers context) :
    Body layouts owner active frameLayout globals onError values { function with evidence := dictionary }
      expressionSyntax readFuel solved reasonAt ambient administrative context scope output code
      fellThrough escaped registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites
    valid := ⟨body.valid.ledger, body.valid.runtime, covers⟩
    projection := body.projection, unique := body.unique, emitted := body.emitted }

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- The original source grade feeds the single imperative proof. The returned
heap and reached lexical exit belong to this exact emitted body. -/
theorem Body.preserves_sized (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  have flow := RecursiveNamedImperativeFor.preservesAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := function.evidence) (transport := builtinTransport) (bindings := builtinBindings)
    (budget := size) (faithful := faithful) (observations := observations)
    (meaningMost := fun context valid child _ => RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed builtinEntry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child)
    .reachable body.unique body.tree body.sites size (Nat.le_refl size)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    RecursiveNamedFunctionFinishBounds.preserves_at_emitted functions program body.tree body.projection body.unique
      escapedFault builtinTransport body.emitted
      (fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
      size flow body.valid environments heaps locals agrees typed reference read unmapped True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- Source-only sizing is confined to preservation. -/
theorem Body.preserves
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact body.preserves_sized functions definitions registered extension program faithful observations functionTypes
    uninitialized missing escapedFault size environments heaps locals agrees typed reference read unmapped sized

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- Reflection consumes the actual measured body completion. The finish proof
passes its original strict flow child to the same bounded statement proof. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults builtinEntry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed builtinEntry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime uninitialized missing)) budget
  have flow := RecursiveNamedImperativeFor.reflectsAt_match_with
    (validity := fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (extend := fun valid extended => valid.extend extended) (runtimeOf := fun _ valid => valid)
    functions definitions registered extension program function.evidence builtinTransport builtinBindings
    budget expressions faithful observations .reachable functionTypes body.unique body.tree body.sites
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    RecursiveNamedFunctionFinishBounds.reflects_at_emitted functions program body.tree body.projection body.unique
      escapedFault builtinTransport body.emitted
      (fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
      budget size within flow body.valid environments heaps locals agrees typed reference read unmapped True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

end ConcreteBody

section Hook
open CallableAncestryPairedLookup
open NamedCalls (withFrame_rename)
private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
/-- The original hook completion supplies a strict parameter prefix, followed
by its real marked allocation receipt. No continuation agreement supplies a size. -/
theorem hook_prefix_with_spine {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata bodyStore prefixSize,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      (∃ entry : Prefix prepared.layout.frame allocationGlobals location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore,
        ∃ added : Environment, added.length = bindings.length ∧
          entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at evaluation
  obtain ⟨nextSize, prefixSize, nextValue, nextStore, bodyStore, nextEvaluation, prefixEvaluation,
    _, smaller, finalEq⟩ := RecursiveNamedCallBounds.with_frame (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation.sound
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at prefixEvaluation
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry, added, length, spine⟩ := parameter_prefix_with_spine functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped prefixEvaluation
  exact ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, added, length, spine⟩


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
theorem hook_prefix {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata bodyStore prefixSize,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      Nonempty (Prefix prepared.layout.frame allocationGlobals location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore) := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, _⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  exact ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, ⟨entry⟩⟩


variable {expressionSyntax : ExpressionId → Prop}
  (profile : Body layouts owner active prepared.layout.frame allocationGlobals onError values function
    expressionSyntax readFuel solved reasonAt ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (escapedFault : faults .controlEscapedFunction escaped)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped
  extension uninitialized missing faithful functionLeaves functionTypes profile escapedFault in
/-- The concrete runtime body closes the shared native hook continuation. -/
theorem hook_preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  exact BuiltinNamedCalls.hook_preserves_with (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (fun {_ _ _ _ _} entry {_ _} trace => BuiltinNamedCalls.Parameters.preserves_with (functions := functions) (program := program) entry
      (fun bodyTrace => profile.preserves functions definitions registered extension program faithful
        functionLeaves functionTypes uninitialized missing escapedFault entry.environments entry.heaps
        entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped bodyTrace) trace)
    allocated trace

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped
  extension uninitialized missing faithful functionLeaves functionTypes profile escapedFault in
/-- Reflection uses the original strict hook child and its actual allocation
prefix; source execution receives its own independent grade. -/
theorem hook_reflects_sized {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, ⟨entry⟩⟩ :=
    hook_prefix (prepared := prepared) (functions := functions)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, related, finalHeaps,
    maps, worlds, frame, sourceMetadata, reached⟩ :=
    profile.reflects_sized functions definitions registered extension program faithful functionLeaves functionTypes
      uninitialized missing escapedFault size entry.childSize (Nat.le_trans entry.bounded (Nat.le_of_lt smaller))
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
      entry.unmapped entry.completed
  exact BuiltinNamedCalls.hook_reflects_from_prefix (prepared := prepared) (functions := functions)
    (program := program) (registered := registered) (heaps := heaps) (unmapped := unmapped) (typed := typed)
    (caller := caller) (snapshots := snapshots) owned history finalEq
    (fun _ _ => ⟨entry.environment, entry.heap, outcome, after, finalMap, finalWorld, entry.allocation,
      sourceTrace.sound, related, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
      entry.frame.trans frame, entry.metadata.trans sourceMetadata, reached⟩)

open CallableCoercionMethodFrame (BodyOutcome)

variable {sourceBody : Dynamic.BodyInstance}
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)

include profile parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame escapedFault in
/-- Independent method body execution drives the actual marked parameters,
frame install, concrete body and restoration. The selected evidence is fixed. -/
theorem preserves {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  apply CallableCoercionMethodBody.preserves_with (prepared := prepared) (functions := functions) (program := program)
    (parameters := parameters) (extended := extended) (represented := represented) (sourceFrame := sourceFrame)
    (trace := trace)
  intro environment bound after outcome allocated bodyTrace
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluated, related,
    finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    hook_preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (profile := profile) (escapedFault := escapedFault) (parameters := parameters) (inputs := inputs)
      (extended := extended) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) allocated bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds,
    frame, metadata, finalCaller, finalSnapshots⟩

include profile parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame escapedFault in
/-- A completed real hook supplies source allocation and a concrete body
trace. Source method invocation follows without ordinary global instantiation. -/
theorem reflects_sized {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    hook_reflects_sized
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (profile := profile) (escapedFault := escapedFault) (parameters := parameters) (inputs := inputs)
      (extended := extended) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) completed
  exact CallableCoercionMethodBody.reflects_with (prepared := prepared) (functions := functions) (program := program)
    (extended := extended) (sourceFrame := sourceFrame)
    ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
      related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots⟩


end Hook


section Actual

/-- The source method remains independent of the ordinary function catalogue.
This view uses the actual compiled ordered statement roots and full dictionary. -/
abbrev methodFunction {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment) : Dynamic.Closure :=
  CallableCoercionMethodFrame.view sourceBody dictionary compiled.statements

/-- Only static source and compiler receipts. The actual compilation fixes the
body, ordered binders, hook, diagnostics and emitted closure. -/
structure Profile {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (values : SourceCoreCompatibleValues.Context) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compiled sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  expressionSyntax : ExpressionId → Prop
  readFuel : Nat
  body : Body prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
    (fun error => .sourceAllocation (reprStr error)) values (methodFunction compiled sourceBody dictionary)
    expressionSyntax readFuel named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
    ambient (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
    (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) named.signature.resultType compiled.body
    compiled.own.fellThroughReason compiled.own.table.escapedReason registry faults
  definitions : prepared.layouts.definitions = ambient.definitions
  registered : prepared.ancestry.layout.frame.Registered ambient.definitions
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)

/-- Source attribution comes from the actual trait-method judgment. Native
signature equality does not create it. -/
def Profile.of_selected {program : Program} {callerContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence traitName methodName requirements sourceBody dictionary)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
    (parameters : sourceBody.source.inputs = named.inputs.map Prod.fst)
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context)
    {expressionSyntax : ExpressionId → Prop} {readFuel : Nat}
    (body : Body prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) values (methodFunction compiled sourceBody dictionary)
      expressionSyntax readFuel named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
      ambient (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) named.signature.resultType compiled.body
      compiled.own.fellThroughReason compiled.own.table.escapedReason registry faults)
    (definitions : prepared.layouts.definitions = ambient.definitions)
    (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)) :
    Profile compiled values ambient sourceBody dictionary administrative registry faults :=
  ⟨sameSource, parameters, CallableCoercionMethodFrame.of_selected selected compiled sameSource.symm,
    context, types, extended, expressionSyntax, readFuel, body, definitions, registered, parameterType⟩

/-- The observed installed closure and both administrative histories are kept
at the actual caller heap. No execution meaning is stored here. -/
structure Installed (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (before : Dynamic.Heap) (store : Store)
    (callerEnvironment : Environment) where
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before sourceBody.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  capturedReference : captured[embedding prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.ancestry.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
    frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
    prepared.ancestry.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure named.signature.parameterType (LanguageResult.resultType named.signature.resultType)
      (compiled.output.rename embedding.lift) captured))

variable (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)

include profile in
private theorem actual_parameters : SourceCoreSourceCells.bindParameters
    (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
  rw [profile.sameSource]; exact compiled.parametersCompiled

include profile extension faithful observations functionTypes uninitialized missing escaped in
theorem Profile.preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (trace : NamedCalls.BodyOutcome program sourceBody dictionary before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodRuntimeMeaning.preserves (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (allocationGlobals := prepared.base.globals.length) (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (profile := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (uninitialized := uninitialized) (missing := missing) (faithful := faithful)
    (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := actual_parameters compiled profile) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) trace

include profile extension faithful observations functionTypes uninitialized missing escaped in
theorem Profile.reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodRuntimeMeaning.reflects_sized (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (allocationGlobals := prepared.base.globals.length) (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (profile := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (uninitialized := uninitialized) (missing := missing) (faithful := faithful)
    (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := actual_parameters compiled profile) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) completed

end Actual

section ConcreteCall
private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)


variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only actual argument effects transport the installed global and caller
frame. No source identity is inferred from the closure's native type. -/
def Installed.extend {functions : FunctionModel values.checked.catalog ambient}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions futureMapping futureWorld after futureStore callerEnvironment := by
  have frameBound := (List.getElem?_eq_some_iff.mp installed.caller.read).1
  have globalBound := (List.getElem?_eq_some_iff.mp installed.globalRead).1
  have frame := preserved installed.frameLocation installed.unmapped frameBound
  have global := preserved installed.globalLocation installed.globalUnmapped globalBound
  exact { installed with
    environments := installed.environments.extend maps worlds
    locals := installed.locals.mono metadata
    captureTyped := installed.captureTyped.weaken worlds
    unmapped := frame.1
    frameTyped := worlds.lookup installed.frameTyped
    caller := ⟨frame.2.trans installed.caller.read, installed.caller.history⟩
    snapshots := installed.snapshots.transport preserved
    globalUnmapped := global.1
    globalRead := global.2.trans installed.globalRead }

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (named.inputs.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = named.inputs.map Prod.snd)
  (packedType : named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes packedType profile in
/-- The first failing argument skips the installed body; successful ordered
arguments enter the same concrete method profile at their actual final heap. -/
theorem call_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before ids sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
      program callerEvidence callerValid.ledger callerValid.runtime unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments named.inputs represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ :=
      profile.preserves compiled functions extension program faithful observations functionTypes uninitialized missing escaped
        next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

private theorem failed_call {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {before middle after : Store} {token : Word} {value : Value} {size : Nat}
    (argument : Evaluates environment before arguments (.inLeft signature.parameterType (.word token)) middle)
    (completed : EvaluationSize size environment before (SourceCoreCalls.call signature index arguments reason) value after) :
    value = .inLeft signature.resultType (.word token) ∧ after = middle := by
  cases completed with
  | caseLeft actual branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic actual.sound argument
    cases same
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        exact ⟨rfl, rfl⟩
  | caseRight actual _ => cases (evaluation_deterministic actual.sound argument).1

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes packedType profile in
/-- Original call children supply the argument completion and strict method
body witness. The source trace is reconstructed independently at each step. -/
theorem call_reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value} {size : Nat}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (SourceCoreCalls.call named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
        before ids sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentSize, argumentValue, middleStore, argumentStrict, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
      program callerEvidence callerValid.ledger callerValid.runtime callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation.sound
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := failed_call (packedType.symm ▸ argumentEvaluation.sound) completed
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      exact ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, .fault matched, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments named.inputs represented
      obtain ⟨bodySize, bodyStrict, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩ :=
        profile.reflects_sized compiled functions extension program faithful observations functionTypes uninitialized missing escaped
          next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

end ConcreteCall

section OperatorSource
open CallablePreparedMethodSelection
open CallableCoercionExpressionCertificates (Projector Specialized Lowered rawNode)

variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}

/-- Dispatch and the full source selector come from the same actual checker
return. An arbitrary source receipt is never identified by its trait name. -/
structure OperatorSource
    (receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output)
    extends SourceReceipt receipt where
  dispatch : match node.form with
    | .unary operator _ => UnaryTraitDispatch operator traitName methodName
    | .binary _ operator _ => BinaryTraitDispatch operator traitName methodName
    | _ => False

private theorem unary_dispatch {operator : Syntax.UnaryOp} {traitName methodName : String}
    (accepted : Detail.unaryOperatorDispatch operator = .traitMethod traitName methodName) :
    UnaryTraitDispatch operator traitName methodName := by
  cases operator <;> cases accepted <;> constructor

private theorem binary_dispatch {operator : Syntax.BinaryOp} {traitName methodName : String}
    (accepted : Detail.binaryOperatorDispatch operator = .traitMethod traitName methodName) :
    BinaryTraitDispatch operator traitName methodName := by
  cases operator <;> cases accepted <;> constructor

/-- Reuse the real unary/binary method certificate and retain its dispatch. -/
theorem OperatorSource.of_accepted
    (receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output) :
    Nonempty (OperatorSource receipt) := by
  have accepted := receipt.selectedMethod
  have rawRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? (rawNode node receipt.requirements) =
      some receipt.requirements := by
    change (if receipt.requirements.length < 0 then none else
      if receipt.requirements = receipt.requirements.take (receipt.requirements.length - 0) ++ [] then
        some (receipt.requirements.take (receipt.requirements.length - 0)) else none) = some receipt.requirements
    simp
  rcases receipt.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, dispatch, owned, ⟨certificate⟩⟩ := unary_of_accepted accepted
    exact ⟨⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩, by simpa only [form] using unary_dispatch dispatch⟩⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, dispatch, owned, ⟨certificate⟩⟩ := binary_of_accepted accepted
    exact ⟨⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩, by simpa only [form] using binary_dispatch dispatch⟩⟩

private theorem binary_strict {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : BinaryTraitDispatch operator traitName methodName) : Dynamic.StrictBinaryOperator operator := by
  cases dispatch <;> constructor

variable
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

include selected selection in
/-- This pure bridge builds the actual source operator judgment from the same
ordered argument trace and independently selected method body. -/
theorem OperatorSource.raw {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : NamedCalls.Arguments.Trace program context evidence dictionary source environment before
      receipt.arguments sourceBody outcome after) :
    CallableCoercionExpressionMeaning.RawOutcome program context evidence source environment before node outcome after := by
  have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions receipt.requirements := by
    have owned := receipt.ordinary
    change (let suffix := coercionRequirementIds node.coercions
      if node.requirements.length < suffix.length then none else
        let owned := node.requirements.take (node.requirements.length - suffix.length)
        if node.requirements = owned ++ suffix then some owned else none) = some receipt.requirements at owned
    dsimp only at owned
    split at owned
    · contradiction
    · split at owned
      · have same := Option.some.inj owned
        change node.requirements = receipt.requirements ++ coercionRequirementIds node.coercions
        rw [← same]
        exact ‹node.requirements = _›
      · contradiction
  have dispatch := selected.dispatch
  rcases receipt.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · simp only [form] at dispatch
    rw [arguments] at trace
    cases trace with
    | argumentFault fault =>
      cases fault with
      | head fault =>
        dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
        rw [form]
        exact .unaryOperand layout fault
      | tail _ fault => cases fault
    | apply evaluated body =>
      cases evaluated with
      | cons operandEvaluated remaining =>
        cases remaining
        cases body with
        | value invoked =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .unary layout operandEvaluated (.method dispatch selection invoked)
        | fault failed =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .unaryApply layout operandEvaluated (.method dispatch selection failed)
  · simp only [form] at dispatch
    rw [arguments] at trace
    cases trace with
    | argumentFault fault =>
      cases fault with
      | head fault =>
        dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
        rw [form]
        exact .binaryLeft layout fault
      | tail leftEvaluated fault =>
        cases fault with
        | head fault =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .binaryRight layout leftEvaluated (.strict (binary_strict dispatch)) fault
        | tail _ fault => cases fault
    | apply evaluated body =>
      cases evaluated with
      | cons leftEvaluated remaining =>
        cases remaining with
        | cons rightEvaluated remaining =>
          cases remaining
          cases body with
          | value invoked =>
            dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
            rw [form]
            exact .binaryEvaluateRight layout leftEvaluated
              (.strict (binary_strict dispatch)) rightEvaluated (.method dispatch selection invoked)
          | fault failed =>
            dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
            rw [form]
            exact .binaryApply layout leftEvaluated
              (.strict (binary_strict dispatch)) rightEvaluated (.method dispatch selection failed)

include selected selection in
/-- The old whole-expression entry adds the empty coercion path to the same
raw operator proof. The raw proof retains the original ordered requirements. -/
theorem OperatorSource.expression {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (trace : NamedCalls.Arguments.Trace program context evidence dictionary source environment before
      receipt.arguments sourceBody outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  have raw := selected.raw selection trace
  cases outcome with
  | value value =>
    exact .value (.intro (lookupExpression?_sound receipt.found) raw (coercions ▸ .nil))
  | fault reason => exact .fault (.form (lookupExpression?_sound receipt.found) raw)

end OperatorSource

section EmittedOperator
open CallableCoercionExpressionCertificates

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

/-- Full retained method and dictionary equality accompany the real compiled
closure. Signature equality alone never supplies method source attribution. -/
structure OperatorAlignment : Prop where
  retained : named.specialized = receipt.selection.method.specialized
  sourceBody : sourceBody = CallableCoercionMethodInstantiation.bodyInstance checkedProgram receipt.selection.method
  dictionary : dictionary = CallableNamedMetadata.environment receipt.dictionary
  signature : receipt.native.signature = named.signature

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)

include alignment in
/-- The actual operator operand is the issued method call, independently of
its retained output-coercion suffix. -/
theorem OperatorAlignment.operand_emitted (ξ : Renaming) :
    receipt.operand.expression.rename ξ = SourceCoreCalls.call named.signature
      (ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
      ((SourceCoreCalls.packArguments receipt.loweredArguments).expression.rename ξ) compilation.internalReason := by
  simpa only [NamedCalls.Arguments.call_rename, alignment.signature] using
    congrArg (fun value : SourceCoreBasic.LoweredExpr => value.expression.rename ξ) receipt.native.emitted

include alignment in
/-- The original suffix receipt is still retained. This final-expression
consumer handles the explicit empty suffix only. -/
theorem OperatorAlignment.emitted (coercions : node.coercions = []) (ξ : Renaming) :
    output.expression.rename ξ = SourceCoreCalls.call named.signature
      (ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
      ((SourceCoreCalls.packArguments receipt.loweredArguments).expression.rename ξ) compilation.internalReason := by
  have suffix := receipt.suffix.accepted
  rw [coercions] at suffix
  have same : receipt.operand = output := Except.ok.inj suffix
  exact (congrArg (fun value : SourceCoreBasic.LoweredExpr => value.expression.rename ξ) same.symm).trans
    (alignment.operand_emitted receipt ξ)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem operator_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before receipt.arguments sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    call_preserves compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
      callerValid callerUninitialized callerMissing children nativeTypes packedType
      installed environments heaps locals layout actualTyped unique execution
  exact ⟨value, finalStore, finalMap, finalWorld, selected.expression selection coercions execution,
    emitted.symm ▸ evaluated, rest⟩

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem operator_reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {size : Nat}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  rw [emitted] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    call_reflects_sized compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
      callerValid callerUninitialized callerMissing children nativeTypes packedType
      installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, selected.expression selection coercions trace, rest⟩

end EmittedOperator

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
