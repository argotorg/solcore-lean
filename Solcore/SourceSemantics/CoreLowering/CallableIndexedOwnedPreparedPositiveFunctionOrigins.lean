import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts

/-! Positive function origins retain their actual bootstrap owner and immutable
key. Named leaves retain the actual current capture, full Source dictionary and
installed code. Closure leaves retain the existing direct compiler association
and the same bootstrap owner. The bootstrap basis is independent of this model,
so storing its provenance does not define a recursive function model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey NamedCapture NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedNamedBootstrapReceipts (Bootstrap NamedOwner)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}

abbrev Owner := NamedOwner (headers := headers) keys
  (CallableIndexedLambdaValues.model compiled.indexed profile) bodyRegistry

/-- Coverage is finite static ownership of the fixed key domain. Its producer
below uses the actual singleton bootstrap; it contains no execution claim. -/
def OwnerCover (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) : Prop :=
  ∀ owner : OwnedKey keys, ∃ origin : Owner (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (profile := profile), origin.owner = owner

/-- Read the physical owner from the actual constructor without erasure. -/
def association_owner {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (association : CallableIndexedOwnedPreparedNativeDirectCellOrigins.Association qualification
      headers keys bodyRegistry faults mapping world function native bindings parameter result) : OwnedKey keys := by
  cases association with
  | ordinary owner _ _ _ _ _ _ _ _ _ _ _ => exact owner
  | principal owner _ _ _ _ _ _ _ _ _ _ _ => exact owner

structure ClosureAssociation (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  association : CallableIndexedOwnedPreparedNativeDirectCellOrigins.Association qualification
    headers keys bodyRegistry faults mapping world function native bindings parameter result
  origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile)
  sameOwner : origin.owner = association_owner association

abbrev ClosureMember (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
    function native bindings parameter result)

section Closures
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

def ClosureAssociation.extend
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ClosureAssociation qualification headers keys bodyRegistry faults profile futureMapping futureWorld
      function native bindings parameter result := by
  refine ⟨packet.association.extend maps worlds, packet.origin, ?_⟩
  have same : association_owner (packet.association.extend maps worlds) = association_owner packet.association := by
    cases packet.association <;> rfl
  exact packet.sameOwner.trans same.symm

/-- The physical prefix is inherited from the actual complete bootstrap key.
It is independent of the lexical lambda capture scope. -/
theorem ClosureAssociation.capture_zero
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result) :
    (association_owner packet.association).key.capturePrefix = 0 := by
  rw [← packet.sameOwner]
  exact packet.origin.capture_zero

theorem ClosureAssociation.globals
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length := packet.origin.globals member

theorem ClosureAssociation.global_locations
    (packet : ClosureAssociation qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    (association_owner packet.association).key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rw [← packet.sameOwner]
  exact packet.origin.global_locations header

theorem ClosureMember.direct
    (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result) :
    CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers keys
      bodyRegistry faults mapping world function native bindings parameter result := by
  obtain ⟨packet⟩ := member
  exact ⟨packet.association⟩

theorem ClosureMember.extend
    (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ClosureMember qualification headers keys bodyRegistry faults profile futureMapping futureWorld
      function native bindings parameter result := by
  obtain ⟨packet⟩ := member
  exact ⟨packet.extend maps worlds⟩

theorem closure_of_direct
    (owners : OwnerCover headers keys bodyRegistry profile)
    (member : CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers
      keys bodyRegistry faults mapping world function native bindings parameter result) :
    ClosureMember qualification headers keys bodyRegistry faults profile mapping world
      function native bindings parameter result := by
  obtain ⟨association⟩ := member
  obtain ⟨origin, same⟩ := owners (association_owner association)
  exact ⟨⟨association, origin, same⟩⟩
end Closures

/-- The actual formed named carrier is retained; no arbitrary capture is
identified with a static chooser or upgraded to bootstrap ownership. -/
inductive NamedAssociation
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.GlobalFunction → Value → Ty → Type where
  | named {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
      {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction} {identity : Word}
      (origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile))
      (member : header ∈ headers) (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers origin.owner.key header mapping world) (installed : NamedInstalledCode capture)
      (number : Word.ofNat? (header.slot + 1) = some identity)
      (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table (.named header.named.signature.key))
      (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
        header.named.signature.functionType compiled.indexed.layouts.definitions) :
      NamedAssociation headers keys bodyRegistry profile mapping world header.named.specialized.function.type source
        (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured))
          (.word descriptor.id)) (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)

section Named
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}

def NamedAssociation.extend
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    NamedAssociation headers keys bodyRegistry profile futureMapping futureWorld sourceType source native type := by
  cases packet with
  | named origin member sourceAt capture installed number projection descriptor typed =>
    exact .named origin member sourceAt (capture.extend maps worlds) installed number projection descriptor (typed.weaken worlds)

def NamedAssociation.origin
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile) := by
  cases packet with
  | named origin _ _ _ _ _ _ _ _ => exact origin

theorem NamedAssociation.capture_zero
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    packet.origin.owner.key.capturePrefix = 0 := packet.origin.capture_zero

theorem NamedAssociation.globals
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length := packet.origin.globals member

theorem NamedAssociation.global_locations
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    packet.origin.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot :=
  packet.origin.global_locations header

theorem NamedAssociation.general
    (packet : NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type) :
    CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults mapping world
      sourceType (.global source) native type := by
  cases packet with
  | named origin member sourceAt capture installed number projection descriptor typed =>
    exact .prior (.prior (.named origin.owner member sourceAt capture installed number projection descriptor typed))
end Named

inductive FunctionOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : ClosureMember qualification headers keys bodyRegistry faults profile mapping world function native bindings parameter result) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}
      (member : Nonempty (NamedAssociation headers keys bodyRegistry profile mapping world sourceType source native type)) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType (.global source) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType (.builtin function) native type

theorem FunctionOrigins.direct {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world sourceType source native type) :
    CallableIndexedOwnedPreparedNativeDirectCellOrigins.FunctionOrigins qualification headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure member.direct
  | global member => obtain ⟨packet⟩ := member; exact .global packet.general
  | builtin related => exact .builtin related

/-- Runtime growth preserves the exact key, Source dictionary, installed code
and carrier. Only actual capture environment typing grows. -/
def functions (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins qualification headers keys bodyRegistry faults profile mapping world
  projection := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) origin.direct
  runtime_hasType := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) origin.direct
  source_function := fun origin => (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) origin.direct
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global member => obtain ⟨packet⟩ := member; exact .global ⟨packet.extend maps worlds⟩
    | builtin related => exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)

theorem includes_direct (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions qualification headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedNativeDirectCellOrigins.functions qualification headers keys bodyRegistry faults profile) :=
  fun origin => origin.direct

abbrev PayloadOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

abbrev CellOrigins (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

section Outputs
variable {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem payload_static_member
    (owners : OwnerCover headers keys bodyRegistry profile)
    {function : Dynamic.Closure} {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : CallableIndexedOwnedPreparedNativeDirectCellOrigins.StaticMember qualification headers keys
      bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) :=
  .function (.closure (closure_of_direct owners member))

theorem global_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .global function →
      ∃ actualType, SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType actualType ∧
        Nonempty (NamedAssociation headers keys bodyRegistry profile mapping world actualType function native type) := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | global member => intro function same; cases same; exact ⟨_, rfl, member⟩
    | closure member => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function equal
    obtain ⟨actualType, previous, packet⟩ := ih function equal
    exact ⟨actualType, same.trans previous, packet⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

theorem closure_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        ClosureMember qualification headers keys bodyRegistry faults profile mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | closure member => intro function same; cases same; exact ⟨_, _, _, member, rfl⟩
    | global member => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Outputs

/-- The source heap is literally empty at bootstrap. Retargeting preserves the
actual store, entry, frame, world and keys; only its vacuous cell model changes. -/
def bootstrap_retarget
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry} {world : StoreTyping}
    (packet : Bootstrap (headers := headers) initial initialRegistry world)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) : Bootstrap (headers := headers) future futureRegistry world where
  recipe := packet.recipe
  accepted := packet.accepted
  ledger := packet.ledger
  sizes := packet.sizes
  locals := packet.locals
  heaps := ⟨packet.heaps.length_eq, packet.heaps.injective, packet.heaps.runtime_hasTypes, by
    intro source target impossible
    simp at impossible⟩
  entry := packet.entry

/-- Complete bootstrap keys are definitionally unchanged by the empty-heap
retarget. This forwards a genuine owner to a new runtime model. -/
def owner_retarget
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry}
    (packet : NamedOwner (headers := headers) keys initial initialRegistry)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) : NamedOwner (headers := headers) keys future futureRegistry :=
  ⟨packet.world, bootstrap_retarget packet.bootstrap future futureRegistry, packet.embedding⟩

theorem owner_retarget_owner
    {initial : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {initialRegistry : SourceCoreRawMetadata.Registry}
    (packet : NamedOwner (headers := headers) keys initial initialRegistry)
    (future : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (futureRegistry : SourceCoreRawMetadata.Registry) :
    (owner_retarget packet future futureRegistry).owner = packet.owner := rfl

/-- The singleton bootstrap manufactures complete owner coverage directly.
No equality is inferred from an arbitrary reached pool or closure value. -/
theorem bootstrap_owner_cover {world : StoreTyping}
    (packet : Bootstrap (headers := headers)
      (CallableIndexedLambdaValues.model compiled.indexed profile) bodyRegistry world) :
    OwnerCover headers packet.keys bodyRegistry profile := by
  intro owner
  let embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding packet.keys packet.keys :=
    ⟨fun key => key, fun _ => rfl⟩
  let origin := NamedOwner.of_bootstrap packet embedding
  refine ⟨origin, ?_⟩
  have same : owner = packet.owner := by
    have position_eq : owner.position = packet.owner.position := by
      apply Fin.ext
      have bound := owner.position.isLt
      simp only [Bootstrap.keys, List.length_singleton] at bound
      have zero : packet.owner.position.val = 0 := rfl
      omega
    cases owner with
    | mk position => exact congrArg OwnedKey.mk position_eq
  exact (show origin.owner = packet.owner from rfl).trans same.symm

theorem observations (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions qualification headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry)
    origin.direct.lambda_represents

theorem runtime_views (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions qualification headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry)
    origin.direct.lambda_represents

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
