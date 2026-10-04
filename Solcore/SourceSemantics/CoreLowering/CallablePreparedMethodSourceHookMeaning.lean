import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning

/-! Source method body execution enters the actual compiled hook through its
retained parameter spine. Catalog authority is constructed before body
completion from real installation and allocation effects. The original source
body grade and its family hypothesis remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodOriginMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor compiled values ambient sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)


section Parameters
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming}
  {location : Location} {next : NativeFrame}
  (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The accepted parameter entry supplies every field before body evaluation.
Its actual installation, complete history and ordered spine construct the same protected origin entry. -/
def entry_of_parameters : CallableRuntimeBodyOrigins.Entry
    (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := location
  native := next
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  installed := ⟨source_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata
    length spine reached.reference owned history profile.sourceFrame profile.sameSource⟩

end Parameters

/-- The original source body grade executes the real compiled hook. The
neutral family hypothesis is consumed once at the actual parameter state;
the shared envelope restores the full caller catalog and snapshots. -/
theorem ProfileFor.preserves_hook_of_below (budget child : Nat) (strict : child < budget)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.PreservesAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf)))
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
      profile.context environment bound outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have acceptedPrefix : SourceCoreSourceCells.bindParameters
      (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
      named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
    rw [profile.sameSource]
    exact compiled.parametersCompiled
  obtain ⟨originId, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    evaluated, related, finalHeaps, maps, worlds, frame, sourceMetadata, caller, snapshots, reachedExit⟩ :=
    BuiltinNamedCalls.hook_preserves_with_spine
      (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
      (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
      (functions := functions) (program := program) (onError := fun error => .sourceAllocation (reprStr error))
      (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
      (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
      (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
      (heaps := heaps) (initialLocals := installed.locals)
      (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
      (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
      (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller) (snapshots := installed.snapshots)
      (RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary) profile.context)
      (by
        intro originId index metadata owned history prefixContext prefixActual embedding entry added length spine outcome after sourceTrace
        let actualEntry := entry_of_parameters compiled profile functions escaped extend runtimeOf
          entry initial sameFrame length spine owned history
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds,
          frame, sourceMetadata, reachedExit, retained⟩ := below child strict actualEntry sourceTrace
        exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, related, finalHeaps,
          entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans sourceMetadata, reachedExit⟩)
      allocated trace
  have source := profile.sourceFrame.body_of_trace profile.extended allocated trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, source, related, finalHeaps,
    maps, worlds, frame, sourceMetadata, reachedExit, ⟨initial.extend maps worlds frame sourceMetadata⟩, caller, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
