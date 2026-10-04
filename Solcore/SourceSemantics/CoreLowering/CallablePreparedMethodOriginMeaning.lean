import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning

/-! Actual method profiles enter the neutral body family with their own full
source dictionary and protected method entry. Original hook completion supplies
the strict native child. The family induction hypothesis is consumed once;
restoration reuses the actual prefix and caller receipts. Source preservation
is exposed only at an already reached entry, not for the whole source hook. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning
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


/-- Every field comes from this actual compiled profile and dictionary. The
protected entry retains method attribution separately from its named history. -/
def ProfileFor.origin : CallableRuntimeBodyOrigins.Origin values ambient registry faults where
  layouts := prepared.layouts
  owner := named.signature.key
  active := []
  frameLayout := prepared.ancestry.layout.frame
  globals := prepared.base.globals.length
  onError := fun error => .sourceAllocation (reprStr error)
  function := methodFunction compiled sourceBody dictionary
  expressionSyntax := expressionSyntax
  certificates := certificates
  validity := validity
  diagnosticPolicy := diagnosticPolicy
  administrative := SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative
  context := profile.context
  scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
  output := named.signature.resultType
  code := compiled.body
  fellThrough := compiled.own.fellThroughReason
  escaped := compiled.own.table.escapedReason
  solved := named.specialized.function.solvedRequirements
  protectedEntry := protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
    headers locations capturePrefix (callerPrefix + 1)
  body := profile.body
  definitions := profile.definitions
  registered := profile.registered
  escapedFault := escaped
  transport := CallablePreparedMethodCatalogEntries.transport
  binders := CallablePreparedMethodCatalogEntries.binds
  extend := extend
  runtimeOf := runtimeOf

/-- The source budget stays the original budget. The caller supplies a reached
entry; no unsized parameter entry or source hook execution is reconstructed. -/
theorem ProfileFor.preserves_reached_of_below (budget child : Nat) (strict : child < budget)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.PreservesAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf))) :
    CallableRuntimeBodyOrigins.PreservesAt functions program
      (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf) child :=
  below child strict

section Prefix
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming} {prefixSize : Nat} {value : Value} {bodyStore : Store}
  {location : Location} {next : NativeFrame}
  (reached : Prefix prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body prefixSize value bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The original reached prefix supplies every dynamic field; the full spine
is used by the existing catalog constructor at the same physical frame. -/
def entry_of_prefix : CallableRuntimeBodyOrigins.Entry
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
  installed := ⟨source_entry reached initial sameFrame length spine owned history profile.sourceFrame profile.sameSource⟩

end Prefix

theorem ProfileFor.reflects_hook_of_below (budget : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (within : size ≤ budget)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.ReflectsAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf)))
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
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
  obtain ⟨originId, index, metadata, bodyStore, prefixSize, owned, history, prefixStrict, finalEq,
    reached, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
      (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
      (functions := functions) (onError := fun error => .sourceAllocation (reprStr error))
      (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
      (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
      (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
      (heaps := heaps) (initialLocals := installed.locals)
      (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
      (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
      (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller) completed
  have strict : reached.childSize < budget := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt reached.bounded prefixStrict) within
  let actualEntry := entry_of_prefix compiled profile functions escaped extend runtimeOf
    reached initial sameFrame length spine owned history
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds,
    frame, sourceMetadata, reachedExit, retained⟩ := below reached.childSize strict actualEntry reached.completed
  obtain ⟨restoredHeaps, restoredCatalog, restoredFrame, restoredCaller⟩ :=
    restore_catalog reached initial sameFrame installed.caller profile.registered finalHeaps maps worlds frame sourceMetadata
  have source := profile.sourceFrame.body_of_trace profile.extended reached.allocation trace.sound
  subst finalStore
  exact ⟨sourceSize, reached.environment, reached.heap, outcome, after, finalMap, finalWorld,
    reached.allocation, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans sourceMetadata, reachedExit, restoredCatalog, restoredCaller,
    installed.snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
