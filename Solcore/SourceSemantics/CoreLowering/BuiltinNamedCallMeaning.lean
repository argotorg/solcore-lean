import Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentMeaning

/-! Ordinary named calls retain their actual source definition, installed
closure and indexed frame history. Concrete recursive builtin argument and
lexical body trees discharge the child and body semantics. Parameter allocation
and the finish helper use their real compiler receipts; no semantic field is
stored in the static body certificate. -/
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Frontend SourceInference
private theorem definition_unique {definitions : List FunctionDefinition}
    (unique : (definitions.map (fun definition => definition.body.owner)).Nodup)
    {left right : FunctionDefinition} (leftMem : left ∈ definitions) (rightMem : right ∈ definitions)
    (owner : left.body.owner = right.body.owner) : left = right := by
  induction definitions with
  | nil => cases leftMem
  | cons head tail ih =>
    obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
    simp only [List.mem_cons] at leftMem rightMem
    rcases leftMem with rfl | leftMem
    · rcases rightMem with rfl | rightMem
      · rfl
      · exact False.elim (absent (List.mem_map.mpr ⟨right, rightMem, owner.symm⟩))
    · rcases rightMem with rfl | rightMem
      · exact False.elim (absent (List.mem_map.mpr ⟨left, leftMem, owner⟩))
      · exact ih unique leftMem rightMem

theorem instantiation_unique {program : Program} {instantiation : DeclarationInstantiation}
    {left right : Dynamic.BodyInstance}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (first : Dynamic.FunctionInstantiates program instantiation left)
    (second : Dynamic.FunctionInstantiates program instantiation right) : left = right := by
  cases first with
  | @intro signature definition _ signatureMem definitionMem declaration owner valid source result context =>
    cases second with
    | @intro otherSignature otherDefinition _ otherSignatureMem otherDefinitionMem otherDeclaration otherOwner otherValid otherSource otherResult otherContext =>
      have same : definition = otherDefinition := definition_unique unique definitionMem otherDefinitionMem
        ((owner.trans declaration.symm).trans (otherOwner.trans otherDeclaration.symm).symm)
      cases same
      cases left
      cases right
      simp_all

theorem instantiation_unique_of_wellFormed {program : Program} {instantiation : DeclarationInstantiation}
    {left right : Dynamic.BodyInstance} (wellFormed : ProgramWellFormed program)
    (first : Dynamic.FunctionInstantiates program instantiation left)
    (second : Dynamic.FunctionInstantiates program instantiation right) : left = right :=
  instantiation_unique wellFormed.function_ids first second

/-- A real independent global dispatch uses the exact catalog body in its
source frame. Owner uniqueness and the represented argument arity rule out
missing/arity faults; neither Core code nor a specialization shape selects it. -/
theorem source_dispatch {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (called : FunctionCallBody.Outcome program context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    NamedCalls.BodyOutcome program body function.evidence before arguments outcome after := by
  cases called with
  | value evaluated =>
    cases evaluated with
    | global actual invocation covers invoked =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact .value invoked
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ signatureMem declaration.symm)
    | globalBodyMissing missing =>
      cases frame.instantiated with
      | intro signatureMem definitionMem declaration owner valid source result context =>
        exact False.elim (missing _ definitionMem (owner.trans declaration.symm))
    | globalArity actual mismatch =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact False.elim (mismatch (by simpa only [frame.parameters] using arity))
    | globalBody actual invocation failed =>
      have same := instantiation_unique unique frame.instantiated actual
      cases same
      exact .fault failed

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls.Parameters
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
  (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
theorem preserves_with
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (continuation : ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached⟩ := continuation trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

theorem reflects_with
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (continuation : ∀ {value : Value} {finalStore : Store},
      Evaluates entry.actualBody entry.store (body.rename entry.embedding) value finalStore →
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    continuation (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem preserves
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  exact preserves_with functions program entry
    (fun trace => certificate.preserves functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped trace) trace

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem reflects
    (entry : TypedMixedNamedParameters.Entry layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome := by
  exact reflects_with functions program entry
    (fun evaluated => certificate.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped evaluated) evaluated

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls.Parameters

namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
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
/-- Shared native frame envelope. Its parameter continuation is supplied only by the concrete legacy or runtime body proof. -/
theorem hook_preserves_with
    (prefixMeaning : ∀ {next : NativeFrame} {parameterStore : Store}
      {prefixContext : Core.Context} {prefixActual : Environment} {embedding : Renaming}
      (entry : TypedMixedNamedParameters.Entry prepared.layout.frame allocationGlobals location next
        values functions registry function context bindings arguments before parameterStore mapping world
        administrative prefixContext prefixActual embedding parameterCode body)
      {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates prefixActual parameterStore (parameterCode.rename embedding) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld function.resultType output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping parameterStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
          (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
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
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    prefixMeaning entry trace
  rw [rename_prefix] at bodyEvaluation
  have evaluated := CallableContextFrames.withFrame_evaluates (.var actualReference) caller.read
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current)) bodyEvaluation
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  exact ⟨origin, index, metadata, value, _, finalMap, finalWorld, owned, history,
    renamed.symm ▸ evaluated, represented, restoredHeaps, maps, worlds, restoredFrame, sourceMetadata,
    restoredCaller, snapshots.transport restoredFrame, by simpa only [sameEnvironment, sameHeap] using reached⟩


include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped in
/-- A source allocation and its finite body trace execute the real full named
hook. Parameters are compared with the independently constructed allocation. -/
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
  exact hook_preserves_with (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (fun {_ _ _ _ _} entry {_ _} trace => BuiltinNamedCalls.Parameters.preserves functions extension definitions registered program
      contextValid unique uninitialized missing faithful functionLeaves functionTypes entry certificate trace) allocated trace

include registered heaps unmapped typed caller snapshots in
/-- Restore the exact caller from one reflected parameter-prefix result. The
caller supplies the original split, so a sized consumer keeps its own native child. -/
theorem hook_reflects_from_prefix {value : Value} {finalStore bodyStore : Store}
    {origin : Word} {index : Int} {metadata : MetadataState}
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata))
    (finalEq : finalStore = bodyStore.set location (encode prepared.layout.frame current))
    (prefixMeaning :
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before
        (store.set location (encode prepared.layout.frame (.state index))) →
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location (.state index) (.named origin)
        (store.set location (encode prepared.layout.frame (.state index))) →
    ∃ environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping (store.set location (encode prepared.layout.frame (.state index))) finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome) :
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
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadataExtend, reached⟩ := prefixMeaning installedHeaps installedCaller
  obtain ⟨restoredHeaps, restoredFrame, restoredCaller⟩ :=
    CallableIndexedBodyFrames.restore registered unmapped typed caller finalHeaps worlds frame
  subst finalStore
  exact ⟨origin, index, metadata, environment, bound, outcome, after, finalMap, finalWorld, owned, history,
    allocated, trace, related, restoredHeaps, maps, worlds, restoredFrame, metadataExtend,
    restoredCaller, snapshots.transport restoredFrame, reached⟩

include certificate parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  contextValid unique uninitialized missing faithful functionLeaves functionTypes actualTyped in
/-- Completed actual native execution constructs both source parameter
allocation and the independent body trace from the installed call context with its actual lexical stopping context. -/
theorem hook_reflects {value : Value} {finalStore : Store}
    (evaluation : Evaluates actual store (code.rename ξ) value finalStore) :
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
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at evaluation
  obtain ⟨nextValue, nextStore, bodyStore, nextEvaluation, bodyEvaluation, finalEq⟩ :=
    CallableContextFrames.withFrame_reflects (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at bodyEvaluation
  apply hook_reflects_from_prefix (prepared := prepared) (functions := functions) (program := program)
    (registered := registered) (heaps := heaps) (unmapped := unmapped)
    (typed := typed) (caller := caller) (snapshots := snapshots) owned history finalEq
  intro installedHeaps installedCaller
  obtain ⟨entry⟩ := TypedMixedNamedParameters.entry_of_accepted functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩ :=
    BuiltinNamedCalls.Parameters.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry certificate bodyEvaluation
  exact ⟨entry.environment, entry.heap, outcome, after, finalMap, finalWorld,
    entry.allocation, trace, represented, finalHeaps, maps, worlds, frame, sourceMetadata, reached⟩


end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
open CallableIndexedHistory CallableIndexedParameterCertificates
open SourceCoreCallableIndexedFrames

open NamedCalls.Arguments (call_rename arguments_complete body_complete expression)
abbrev Trace := NamedCalls.Arguments.Trace
abbrev Emission := NamedCalls.Arguments.Emission

abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-- Static body compilation and independent declaration attribution. There
is no source execution, native execution or body meaning field. -/
structure Body {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  closed : named.specialized.assumptions = []
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame globals onError readFuel values
    function.source context solved reasonAt (bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    function.body function.resultType output policy fuel fellThrough escaped body
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)

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

private theorem arguments_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {bindings : List Binding}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads) :
    RuntimeValueHasType world (DataPatternValues.packValues payloads)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) definitions := by
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => simpa [DataPatternValues.packValues, SourceCoreCompatibleCatalog.packTypes] using model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Real installed environments, code and frame state. These observational
facts grant no source declaration or body semantics; those are in `Body`. -/
structure Installed {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {program : Program} (body : Body prepared values ambient.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)
    (before : Dynamic.Heap) (store : Store) (callerEnvironment : Environment) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before body.function.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[body.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType body.named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure body.named.signature.parameterType (LanguageResult.resultType body.named.signature.resultType)
      (body.code.rename embedding.lift) captured))

/-- Argument effects preserve the exact installed closure and both protected
administrative histories. Captured environment typing is weakened along the
actual world extension, including all non-source slots. -/
def Installed.extend {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {program : Program}
    {body : Body prepared values ambient.definitions program} {registry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed functions body registry futureMapping futureWorld after futureStore callerEnvironment := by
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

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} (body : Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include extension uninitialized missing faithful functionLeaves functionTypes in
/-- The concrete parameter/body certificates close this body invocation after
the real argument effects. The only source execution premise is the particular
independent invocation being preserved. -/
theorem body_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]; exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := body.frame.trace_of_body body.extended arity executed
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluation, result, finalHeaps,
    maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    hook_preserves prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing faithful functionLeaves functionTypes body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots allocated trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds,
    preserved, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Independent global application dispatches to the exact retained source
body under actual program owner uniqueness. The concrete builtin body closes
its semantics; an exact-body source trace is not a premise of this consumer. -/
theorem body_dispatch_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed program)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (called : FunctionCallBody.Outcome program callerContext callerEvidence body.function.evidence before
      (.global ⟨body.instantiation, body.function.evidence⟩) arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]
    exact represented.length.1
  exact body_preserves functions extension body uninitialized missing faithful functionLeaves functionTypes
    installed represented heaps (source_dispatch wellFormed.function_ids body.frame arity called)

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Completed actual body execution constructs parameter allocation and the
independent invocation from the concrete lexical tree, with frame restoration. -/
theorem body_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
      (body.code.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace, result,
    finalHeaps, maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    hook_reflects prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing faithful functionLeaves functionTypes body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots executed
  exact ⟨outcome, after, finalMap, finalWorld, body.frame.body_of_trace body.extended allocated trace,
    result, finalHeaps, maps, worlds, preserved, metadata, current, snapshots⟩

variable {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleExpressionLiterals.ContextValid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd)
  (packedType : body.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Concrete recursive builtin argument trees close all child meaning. Arguments are
evaluated before the global read; their first fault skips the body. The body
uses its actual static parameter/lexical certificates at the intervening heap. -/
theorem preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
    simpa only [body.resultType] using
      (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (sourceType := body.function.resultType) (type := body.output) matched)
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments body.bindings represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ := body_preserves functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType body.named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Every finite native call completion reconstructs its ordered source
argument trace and concrete independent named-body invocation. Neither child
evaluations nor a universal body preservation hypothesis are supplied. -/
theorem reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
        before ids body.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentValue, middleStore, argumentEvaluation⟩ := arguments_complete completed
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltins.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
        (internalReason := reason) (packedType.symm ▸ argumentEvaluation)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      refine ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, ?_, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
      simpa only [body.resultType] using
        (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
          (sourceType := body.function.resultType) (type := body.output) matched)
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments body.bindings represented
      have bodyEvaluation := body_complete argumentEvaluation installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩ := body_reflects functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Actual compiler success, independent source attribution and concrete
argument/body certificates close reflection at the emitted expression itself. -/
theorem accepted_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  rw [emitted, call_rename, ← located] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    reflects functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed trace,
    result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Preservation starts with this exact independently instantiated source body
and ordered argument trace. The actual accepted emitted expression is evaluated,
including argument faults and lexical body faults with their preceding writes. -/
theorem accepted_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    preserves functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped unique execution
  have completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore := by
    rw [emitted, call_rename, ← located]; exact evaluation
  exact ⟨value, finalStore, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed execution,
    completed, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinNamedCalls
