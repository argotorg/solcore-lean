import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalNamedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Physical payloads retain old associations and actual prepared closures.
The latter keep their captured slots and support reached diagnostics. Only
projection to the raw function model is exposed for all leaves. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (StaticMember)
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A closure leaf carries its exact positive static member. Named leaves retain the actual installed capture, while builtin leaves
retain their original source-shaped receipt. Neither branch admits an erased closure. The body registry is independent of outer payload metadata. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember headers keys bodyRegistry faults mapping world
        function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys
        mapping world sourceType function native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys
        bodyRegistry faults mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        sourceType (.builtin function) native type

/-- Projection retains the actual Code, captures, and native typing. -/
theorem FunctionOrigins.forget {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact member.represents
  | global related => exact (related.represents (registry := bodyRegistry) (faults := faults)).forget
  | builtin related => exact related.forget

/-- Only map/world extension acts on a positive member; it does not assert that
any source or native cell still contains that member after a write. -/
def functions (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedLambdaValues.model compiled.indexed profile).projection
      (registry := bodyRegistry) origin.forget
  runtime_hasType := fun origin =>
    (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
      (registry := bodyRegistry) origin.forget
  source_function := fun origin =>
    (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
      (registry := bodyRegistry) origin.forget
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related =>
        exact .global (related.extend maps worlds)
    | builtin related =>
        exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)

theorem functions_include_raw
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedLambdaValues.model compiled.indexed profile) :=
  fun origin => origin.forget

theorem includes_physical
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile).Includes
      (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type related
  cases related with
  | closure member => exact .closure (StaticMember.legacy member)
  | global related => exact .global related
  | builtin related => exact .builtin related

theorem runtime_views (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile
    (registry := registry) related.forget

theorem observations (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile
    (registry := registry) related.forget

/-- Existing payload constructors recurse over positive function leaves. -/
abbrev PayloadOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functions headers keys bodyRegistry faults profile)

section Payload
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Attach a newly formed member to that exact value, without changing the
original formation action or its receiving model. -/
theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) :=
  .function (.closure member)

theorem PayloadOrigins.forget
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedLambdaValues.model compiled.indexed profile)
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_raw profile)

/-- Positive source-shape projection includes compatible raw-type wrappers.
It does not inspect an erased general-model representation. -/
theorem PayloadOrigins.closure_member
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | closure member =>
          intro function same
          cases same
          exact ⟨_, _, _, member, rfl⟩
      | global related => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible
      cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- Named inputs retain their exact original installed capture through compatible
raw-type wrappers; call dispatch does not infer it from native typing. -/
theorem PayloadOrigins.named_member
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      sourceType source native type) :
    ∀ function, source = .global function →
      ∃ originalType,
        CallableIndexedOwnedPhysicalNamedAssociation.StaticMember headers keys mapping world originalType function native type ∧
        SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType originalType := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
      cases related with
      | global member => intro function same; cases same; exact ⟨_, member, rfl⟩
      | closure member => intro function impossible; cases impossible
      | builtin related => intro function impossible; cases impossible
  | compatible same _ ih =>
      intro function selected
      obtain ⟨originalType, member, rawType⟩ := ih function selected
      exact ⟨originalType, member, same.trans rawType⟩
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
      intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Payload

section Heap
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {heap after : Dynamic.Heap} {store : Store}

/-- The initial empty heap has no manufactured closure leaves. -/
theorem CellOrigins.empty :
    CellOrigins headers keys bodyRegistry registry faults profile [] [] ⟨[]⟩ [] :=
  GenericHeap.HeapRepresents.empty

theorem CellOrigins.forget
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedLambdaValues.model compiled.indexed profile)
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_raw profile)
    (.refl _) origins

/-- Real administrative allocation appends a typed native cell while preserving
all mapped source cells. No blanket administrative write premise is used. -/
theorem CellOrigins.allocate_administrative {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping (world ++ [type])
      heap (store.allocate native).1 :=
  GenericHeap.HeapRepresents.allocate_administrative origins typed

/-- Actual source allocation and its optional payload grow both stores at their
independent lengths. Every old leaf is transported by the original generic
heap proof. -/
theorem CellOrigins.allocate
    {sourceType : TypeSystem.Ty} {sourceValue : Option Dynamic.Value} {location : Dynamic.Location}
    {native : Value} {payload : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (cell : GenericHeap.CellRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions headers keys bodyRegistry faults profile)) mapping world
      ⟨sourceType, sourceValue, none⟩ native payload)
    (allocated : Dynamic.Heap.Allocates heap sourceType sourceValue location after) :
    CellOrigins headers keys bodyRegistry registry faults profile
      (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload]) after (store.allocate native).1 ∧
    ReferenceRepresents (mapping ++ [store.length]) (world ++ [OptionalCell.cellType payload])
      location store.length payload :=
  GenericHeap.HeapRepresents.allocate origins cell allocated

/-- Only the real write and an authenticated replacement payload update a
mapped cell. The replacement may contain positive closure leaves at any depth. -/
theorem CellOrigins.write_initialized
    {location : Dynamic.Location} {target : Location} {payload : Ty}
    {cell : Dynamic.Cell} {sourceValue : Dynamic.Value} {native : Value}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (reference : ReferenceRepresents mapping world location target payload)
    (read : Dynamic.Heap.Reads heap location cell)
    (replacement : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      cell.type sourceValue native payload)
    (written : Dynamic.Heap.Writes heap location (some sourceValue) after) :
    ∃ updated, store.write? target (.inRight .unit native) = some updated ∧
      CellOrigins headers keys bodyRegistry registry faults profile mapping world after updated ∧
      AdministrativePreserved mapping store mapping updated :=
  GenericHeap.HeapRepresents.write_initialized origins reference read replacement written

/-- A real typed write to an unmapped administrative cell retains every
positive source-visible leaf. An arbitrary administrative-frame relation does
not replace these actual write, type and separation receipts. -/
theorem CellOrigins.write_administrative
    {updated : Store} {target : Location} {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some target)
    (found : world[target]? = some type)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions)
    (written : store.write? target native = some updated) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap updated :=
  GenericHeap.HeapRepresents.write_administrative origins absent found typed written

/-- A real initialized read extracts the stronger member and the exact native
cell without recovering physical slots from an erased representation. -/
theorem CellOrigins.stored_at {location : Dynamic.Location} {function : Dynamic.Closure}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩) :
    ∃ native bindings parameter result,
      StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
      ∃ target, ReferenceRepresents mapping world location target
        (CallableContract.functionType parameter result) ∧
        store.read? target = some (.inRight .unit native) := by
  obtain ⟨target, value, payload, reference, nativeRead, represented⟩ := origins.read read
  cases represented with
  | initialized positive =>
      obtain ⟨bindings, parameter, result, member, sameType⟩ :=
        PayloadOrigins.closure_member profile positive function rfl
      subst payload
      exact ⟨_, bindings, parameter, result, member, target, reference, nativeRead⟩

end Heap

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
