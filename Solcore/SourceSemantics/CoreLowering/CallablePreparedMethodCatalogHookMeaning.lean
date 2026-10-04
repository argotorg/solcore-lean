import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning

/-! The original compiled hook retains its measured parameter prefix. The
same-dictionary body kernel reflects that exact child and restores the complete
caller catalog. Source method attribution is supplied independently; the bounded
expression premise is an internal induction interface, not a closed whole-body
claim. No body execution law is stored in a receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}

variable {sourceBody : Dynamic.BodyInstance}
section Hook
variable (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
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
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame base.globals.length
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
  (canonicalReference : canonical[base.globals.length]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)



variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (kernel : CallableRuntimeBodyKernel.BodyFor layouts owner active prepared.layout.frame base.globals.length onError
    values function expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (escapedFault : faults .controlEscapedFunction escaped)
  (extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence)
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
  (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped kernel extension
  faithful functionLeaves functionTypes escapedFault extend runtimeOf sourceFrame sameSource initial sameFrame in
/-- The body child is extracted from the original completed hook exactly once.
Its independent source trace is lifted through the actual method frame. -/
theorem reflects_hook_sized {size : Nat} {value : Value} {finalStore : Store}
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (certificates context) faults (protectedEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1))))
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore canonical) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, prefixStrict, finalEq,
    reached, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  have strict : reached.childSize < size := Nat.lt_of_le_of_lt reached.bounded prefixStrict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, _, _, _, _, _, reachedExit,
    _, finalHeaps, restoredCatalog, restoredFrame, restoredCaller, maps, worlds, metadata⟩ :=
    CallablePreparedMethodCatalogBodyMeaning.reflects_prefix_sized reached initial sameFrame length spine
      owned history sourceFrame sameSource kernel definitions registered extension faithful functionLeaves functionTypes
      escapedFault extend runtimeOf size strict expressions caller
  have source := sourceFrame.body_of_trace extended reached.allocation trace.sound
  subst finalStore
  exact ⟨sourceSize, reached.environment, reached.heap, outcome, after, finalMap, finalWorld,
    reached.allocation, trace, source, related, finalHeaps, maps, worlds, restoredFrame, metadata,
    reachedExit, restoredCatalog, restoredCaller, snapshots.transport restoredFrame⟩

end Hook
section Compiled

/-- Static attribution and the generic kernel for this actual compilation.
The expression induction interface is supplied to the theorem, not this record. -/
structure ProfileFor {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (values : SourceCoreCompatibleValues.Context) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (expressionSyntax : ExpressionId → Prop) (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (validity : SourceSemantics.Context → Prop) (diagnosticPolicy : AssignmentDiagnosticPolicy) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compiled sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  body : CallableRuntimeBodyKernel.BodyFor prepared.layouts named.signature.key [] prepared.ancestry.layout.frame
    prepared.base.globals.length (fun error => .sourceAllocation (reprStr error)) values
    (methodFunction compiled sourceBody dictionary) expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
    (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) named.signature.resultType compiled.body
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

/-- The existing concrete receipt supplies its exact static fields. -/
def of_builtin (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults) :
    ProfileFor compiled values ambient sourceBody dictionary administrative registry faults profile.expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate profile.readFuel values sourceBody.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key))
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      .reachable :=
  { sameSource := profile.sameSource, parameters := profile.parameters, sourceFrame := profile.sourceFrame
    context := profile.context, types := profile.types, extended := profile.extended, body := profile.body.toKernel
    definitions := profile.definitions, registered := profile.registered, parameterType := profile.parameterType }

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

include profile extension faithful observations functionTypes escaped extend runtimeOf in
/-- Reflect this actual compiled hook. The bounded expression interface is
internal to the enclosing mutual proof; it is not a whole-program premise. -/
theorem ProfileFor.reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context dictionary sourceBody.source
        (certificates context) faults (protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
          headers locations capturePrefix (callerPrefix + 1))))
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
  exact reflects_hook_sized (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (kernel := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (faithful := faithful) (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) (sameSource := profile.sameSource)
    (initial := initial) (sameFrame := sameFrame) (extend := extend) (runtimeOf := runtimeOf) expressions completed

end Compiled
end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
