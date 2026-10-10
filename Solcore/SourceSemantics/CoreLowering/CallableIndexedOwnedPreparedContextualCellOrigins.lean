import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! Prospective positive cells retain the actual prepared ordinary or selected
method packet at every closure leaf. Preparation survives the original generic
payload constructors and actual allocation, write and read proofs. Forward
projection reaches the current positive model at the same Source/native values,
Code and state. Existing plain leaves are never upgraded. The body registry is
independent of the receiving payload registry. Generalized cells and the mixed
expression/body semantic induction remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Both branches retain the prepared packet which actually supplied their
plain typed Association. The principal branch retains its selected dictionary. -/
inductive Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Type where
  | ordinary (receipt : CallableIndexedOwnedPreparedOrdinaryBodyProjection.Receipt
      headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      Association headers keys bodyRegistry faults mapping world function native bindings parameter result
  | principal (receipt : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Receipt
      headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      Association headers keys bodyRegistry faults mapping world function native bindings parameter result

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- Preparation erases only in the forward direction, preserving every index. -/
def Association.forget
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys bodyRegistry faults
      mapping world function native bindings parameter result := by
  cases association with
  | ordinary receipt => exact receipt.forget
  | principal receipt => exact receipt.forget

/-- Extension acts on the actual captures and finite runtime typing. It retains
the same compiler packet, JointBody, method authority and authentic history. -/
def Association.extend
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  cases association with
  | ordinary receipt => exact .ordinary (receipt.extend maps worlds)
  | principal receipt => exact .principal (receipt.extend maps worlds)

end Members

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association headers keys bodyRegistry faults mapping world function native bindings parameter result)

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem StaticMember.ordinary
    (receipt : CallableIndexedOwnedPreparedOrdinaryBodyProjection.Receipt headers keys bodyRegistry faults
      mapping world function native bindings parameter result) :
    StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result :=
  ⟨.ordinary receipt⟩

theorem StaticMember.principal
    (receipt : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Receipt headers keys bodyRegistry faults
      mapping world function native bindings parameter result) :
    StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result :=
  ⟨.principal receipt⟩

theorem StaticMember.forget
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember headers keys bodyRegistry faults
      mapping world function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.forget⟩

theorem StaticMember.extend
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

end Members

/-- Global and builtin authority is unchanged. The closure constructor requires
the stronger retained packet before generic payload construction begins. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native
        (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.global function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty}
      {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.builtin function) native type

theorem FunctionOrigins.forget {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedOwnedContextualCellOrigins.FunctionOrigins headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure member.forget
  | global related => exact .global related
  | builtin related => exact .builtin related

def functions
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile).projection
      (registry := bodyRegistry) origin.forget
  runtime_hasType := fun origin =>
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) origin.forget
  source_function := fun origin =>
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile).source_function
      (registry := bodyRegistry) origin.forget
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related =>
        exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)
    | builtin related =>
        exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
          related registries maps worlds)

theorem functions_include_plain
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget

/-- Compatible payload recursion preserves preparation in products, nominal
fields, every ordered mapping entry and its optional default. -/
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
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_plain profile)

/-- Source-shape inversion is performed on the strong payload itself, including
compatible wrappers. Erased current/general leaves supply no preparation. -/
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

end Payload

/-- A stored occurrence retains its prepared Association alongside the actual
Source and native reads. This statement asserts no continuing read after a write. -/
def StoredAt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (location : Dynamic.Location) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  StaticMember headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
  ∃ target, ReferenceRepresents mapping world location target (CallableContract.functionType parameter result) ∧
    Dynamic.Heap.Reads heap location ⟨FunctionValues.sourceType function, some (.closure function), none⟩ ∧
    store.read? target = some (.inRight .unit native)

theorem StoredAt.forget {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {function : Dynamic.Closure} {native : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (stored : StoredAt headers keys bodyRegistry faults mapping world heap store
      location function native bindings parameter result) :
    CallableIndexedOwnedContextualInitializedClosureReceipts.TypedStoredAt headers keys bodyRegistry faults
      mapping world heap store location function native bindings parameter result :=
  ⟨stored.1.forget, stored.2⟩

section Heap
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping}
  {heap after : Dynamic.Heap} {store : Store}

theorem CellOrigins.empty :
    CellOrigins headers keys bodyRegistry registry faults profile [] [] ⟨[]⟩ [] :=
  GenericHeap.HeapRepresents.empty

theorem CellOrigins.forget
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CallableIndexedOwnedContextualCellOrigins.CellOrigins headers keys bodyRegistry registry faults profile
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_plain profile) (.refl _) origins

theorem CellOrigins.allocate_administrative {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping (world ++ [type])
      heap (store.allocate native).1 :=
  GenericHeap.HeapRepresents.allocate_administrative origins typed

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

theorem CellOrigins.write_administrative
    {updated : Store} {target : Location} {native : Value} {type : Ty}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (absent : ∀ {source : Nat}, mapping[source]? ≠ some target)
    (found : world[target]? = some type)
    (typed : RuntimeValueHasType world native type compiled.indexed.layouts.definitions)
    (written : store.write? target native = some updated) :
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap updated :=
  GenericHeap.HeapRepresents.write_administrative origins absent found typed written

/-- The actual read extracts preparation from the strong relation. The resulting
member retains the same Code, History and JointBody which entered that cell. -/
theorem CellOrigins.stored_at {location : Dynamic.Location} {function : Dynamic.Closure}
    (origins : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location
      ⟨FunctionValues.sourceType function, some (.closure function), none⟩) :
    ∃ native bindings parameter result,
      StoredAt headers keys bodyRegistry faults mapping world heap store
        location function native bindings parameter result := by
  obtain ⟨target, value, payload, reference, nativeRead, represented⟩ := origins.read read
  cases represented with
  | initialized positive =>
      obtain ⟨bindings, parameter, result, member, sameType⟩ :=
        PayloadOrigins.closure_member profile positive function rfl
      subst payload
      exact ⟨_, bindings, parameter, result, member, target, reference, read, nativeRead⟩

end Heap

/-- Strong cells and result payload belong to the original existential's actual
reached state, including a fault row. This is an output facet, not a body law. -/
structure PostWithOrigins
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins headers keys bodyRegistry registry faults profile
    index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

theorem post_at_same_state
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol)
    {context : SourceSemantics.Context}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sourceType : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
    (admitted : PostAdmission bridge context sourceType outcome reached)
    (cells : CellOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world index.heap index.store)
    (represented : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions headers keys bodyRegistry faults profile))
      index.mapping index.world sourceType type faults outcome value) :
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type outcome value reached :=
  ⟨admitted, cells, represented⟩

theorem PostWithOrigins.forget
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol}
    {context : SourceSemantics.Context}
    {profile : compiled.compatible.checked.catalog.callableContracts = true}
    {sourceType : TypeSystem.Ty} {type : Ty}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type outcome value reached) :
    CallableIndexedOwnedContextualCellOrigins.PostWithOrigins
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type outcome value reached := by
  refine ⟨post.admission, CellOrigins.forget profile post.cells, ?_⟩
  cases post.result with
  | value represented => exact .value (PayloadOrigins.forget profile represented)
  | fault represented => exact .fault represented

theorem PostWithOrigins.at_value
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun _ => True) callerProtocol}
    {context : SourceSemantics.Context}
    {profile : compiled.compatible.checked.catalog.callableContracts = true}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Dynamic.Value} {native : Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile sourceType type (.value source) (.inRight .word native) reached) :
    Admission bridge context reached ∧
    Dynamic.ValueHasType context index.heap source sourceType ∧
    PayloadOrigins headers keys bodyRegistry registry faults profile
      index.mapping index.world sourceType source native type := by
  have typed := post.admission.at_value
  cases post.result with
  | value represented => exact ⟨typed.2, typed.1, represented⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins
