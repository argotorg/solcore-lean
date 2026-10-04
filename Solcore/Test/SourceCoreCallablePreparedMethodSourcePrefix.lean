import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds

/-! The common hook envelope retains the actual parameter spine and a source
trace's original grade. The prefix continuation remains the internal interface;
this file does not assert a closed method body semantics. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodSourcePrefix
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames

abbrev actual_parameters := @TypedMixedNamedParameters.entry_of_accepted_with_spine
abbrev legacy_parameters := @TypedMixedNamedParameters.entry_of_accepted
abbrev actual_hook := @BuiltinNamedCalls.hook_preserves_with_spine
abbrev legacy_hook := @BuiltinNamedCalls.hook_preserves_with

section Graded
variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
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
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped in
theorem original_source_grade (child : Nat)
    (prefixMeaning : ∀ (origin : Word) (index : Int) (metadata : MetadataState),
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin →
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
      ∀ {prefixContext : Core.Context} {prefixActual : Environment} {embedding : Renaming}
      (entry : TypedMixedNamedParameters.Entry prepared.layout.frame allocationGlobals location (.state index)
        values functions registry function context bindings arguments before
        (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative prefixContext prefixActual embedding parameterCode body)
      (added : Environment), added.length = bindings.length →
      entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical →
      ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      RecursiveNamedCallBounds.BodyTrace program child function context entry.environment entry.heap outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates prefixActual (store.set location (encode prepared.layout.frame (.state index)))
          (parameterCode.rename embedding) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld function.resultType output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping (store.set location (encode prepared.layout.frame (.state index))) finalMap finalStore ∧
        Dynamic.HeapMetadataExtend before after ∧
        TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
          (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child function context environment bound outcome after) :
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
  exact BuiltinNamedCalls.hook_preserves_with_spine (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (RecursiveNamedCallBounds.BodyTrace program child function context) prefixMeaning allocated trace
end Graded

section ActualSpine
variable {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {location : Location} {native : NativeFrame}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {bindings : List Binding}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {actual canonical added : Environment} {nativeArguments : List Value} {ξ : Renaming} {parameterCode body : Expr}
  (entry : TypedMixedNamedParameters.Entry layout globals location native values functions registry function context bindings arguments before store mapping world
    administrative actualContext actual ξ parameterCode body)
  (length : added.length = bindings.length)
  (spine : entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

include length spine in
theorem ordered_suffix : entry.canonical.drop (bindings.length + 1) = canonical := by
  rw [spine, ← length]
  simp

include length spine in
theorem physical_global (index : Nat) :
    entry.canonical[bindings.length + 1 + index]? = canonical[index]? := by
  rw [spine, ← length]
  rw [List.getElem?_append_right (by omega)]
  have offset : added.length + 1 + index - added.length = index + 1 := by omega
  rw [offset]
  rfl

include length spine in
theorem empty_parameters (empty : bindings = []) :
    entry.canonical = DataPatternValues.packValues nativeArguments :: canonical := by
  have noAdded : added = [] := by
    cases added with
    | nil => rfl
    | cons head tail => simp [empty] at length
  simpa [noAdded] using spine

include length spine in
theorem globals_and_unused_suffix (first second : Value) (unused : Environment)
    (original : canonical = first :: second :: unused) :
    entry.canonical[bindings.length + 1]? = some first ∧
    entry.canonical[bindings.length + 2]? = some second ∧
    entry.canonical.drop (bindings.length + 3) = unused := by
  rw [spine, original, ← length]
  simp [Nat.add_assoc]

include entry in
theorem full_reached_state :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions entry.mapping entry.world entry.heap entry.store ∧
    Dynamic.HeapMetadataExtend before entry.heap ∧
    AdministrativePreserved mapping store entry.mapping entry.store :=
  ⟨entry.heaps, entry.metadata, entry.frame⟩
end ActualSpine

/-- Empty parameter lists still use the actual one-slot packed argument carrier. -/
theorem empty_pack_slot (canonical : Environment) :
    DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := rfl
end Tests.SourceCoreCallablePreparedMethodSourcePrefix
