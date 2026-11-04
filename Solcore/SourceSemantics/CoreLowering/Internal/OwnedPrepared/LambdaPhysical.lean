import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.Staging.RecursiveScope
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState

/-!
# Prepared callables: physical lambdas

Physical closure association and cell origins, lambda parameters, scope declarations and protocol packets.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
/-! A physical closure retains either its original legacy association or the
actual prepared body and all captured slots. The representation projection
retains the actual closure Code and does not require uniform diagnostics. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Association
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | legacy {function native bindings parameter result}
      (original : CallableIndexedOwnedPhysicalClosureAssociation.Association
        headers keys registry faults mapping world function native bindings parameter result) :
      Association headers keys registry faults mapping world function native bindings parameter result
  | preparedOrdinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code) (origin : SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code support)
      (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
      (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
        support.caller function.context function.evidence)) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

  | preparedBranching {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : PreparedLambdaBodySupport.Support code)
      (origin : PreparedLambdaBodySupport.SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedLambdaBodySupport.PreparedAt code support)
      (slots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
      (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
        support.caller function.context function.evidence)) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem Association.represents
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := by
  cases member with
  | legacy original => exact original.original.represents.forget
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .lambda captured code history typed

  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .lambda captured code history typed

def Association.extend
    (member : Association headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  cases member with
  | legacy original => exact .legacy (original.extend maps worlds)
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .preparedOrdinary owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) prepared slots callerReceipt

  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed prepared slots callerReceipt =>
    exact .preparedBranching owner (captured.extend maps worlds) code history support origin prefixContext globals
      referenceIndex (typed.weaken worlds) prepared slots callerReceipt

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association headers keys registry faults mapping world function native bindings parameter result)

theorem StaticMember.represents
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result) := by
  obtain ⟨association⟩ := member
  exact association.represents

theorem StaticMember.extend
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys registry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

theorem StaticMember.legacy
    (member : CallableIndexedOwnedPhysicalClosureAssociation.StaticMember
      headers keys registry faults mapping world function native bindings parameter result) :
    StaticMember headers keys registry faults mapping world function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨.legacy association⟩


theorem Association.stage_origin
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  cases member with
  | legacy original => exact original.original.stage_origin
  | preparedOrdinary _owner captured code _history support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted code.descriptor
      support.source_receipt code.viewOfSource support.unique code.found
      (code.form.trans code.sourceForm) _

  | preparedBranching _owner captured code _history support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted code.descriptor
      support.source_receipt code.viewOfSource support.unique code.found
      (code.form.trans code.sourceForm) _

theorem StaticMember.stage_origin
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) native := by
  obtain ⟨association⟩ := member
  exact association.stage_origin

theorem Association.source_binders
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  cases member with
  | legacy original => exact original.original.source_binders
  | preparedOrdinary _owner _captured code _history _support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

  | preparedBranching _owner _captured code _history _support _origin _prefix _globals _reference _typed _prepared _slots _callerReceipt =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.projected_bindings
    (member : Association headers keys registry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases member with
  | legacy original => exact original.original.projected_bindings
  | preparedOrdinary _owner _captured _code _history _support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact prepared.projected_bindings

  | preparedBranching _owner _captured _code _history _support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact prepared.projected_bindings

theorem Association.parameter_core
    (member : Association headers keys registry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  cases member with
  | legacy original => exact original.original.parameter_core profile
  | preparedOrdinary _owner _captured code _history support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
      prepared.projected_bindings support.body.projection

  | preparedBranching _owner _captured code _history support _origin _prefix _globals _reference _typed prepared _slots _callerReceipt =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
      prepared.projected_bindings support.body.projection

theorem StaticMember.source_binders
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) =
      function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.projected_bindings
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember headers keys registry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalClosureAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
/-! Real parameter allocation retains the actual installed stable frame.
All rows sharing that physical frame carry the new history; other rows keep
their own stable histories. The literal allocation frame then authenticates
every row of the reached pool. Original Source argument typing supplies the
deep heap field at that same parameter endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- Installation updates every key sharing the written physical frame. Its
actual stable history authenticates all of those rows, including duplicates. -/
theorem install_rows {index : ProtectedStateTransition.Index}
    (saved : State headers keys index) (selected : Fin keys.length)
    (stable : StableRows saved) {next : NativeFrame} {ghost : GhostFrame}
    {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata) :
    StableRows (install saved selected (.stable history)) := by
  intro i
  have current := CallableIndexedAuthorityPool.Pool.install_current saved selected i (.stable history)
  have actualGhost := CallableIndexedAuthorityPool.Pool.install_ghost saved selected i (.stable history)
  change ((install saved selected (.stable history)).rows i).authority.current = _ at current
  change ((install saved selected (.stable history)).rows i).authority.ghost = _ at actualGhost
  by_cases same : keys[i.val].frameLocation = keys[selected.val].frameLocation
  · refine ⟨metadata, ?_⟩
    erw [current, actualGhost, if_pos same, if_pos same]
    exact history
  · obtain ⟨oldMetadata, oldHistory⟩ := stable i
    refine ⟨oldMetadata, ?_⟩
    erw [current, actualGhost, if_neg same, if_neg same]
    exact oldHistory

/-- The genuine frame-preserving allocation may have any returned pool with
its own actual cells and ghosts. No record-prefix inverse supplies stability. -/
theorem after_parameters {index reachedIndex : ProtectedStateTransition.Index}
    (saved : State headers keys index) (reached : State headers keys reachedIndex)
    (selected : Fin keys.length) (stable : StableRows saved)
    {next : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table next ghost metadata)
    (frame : AdministrativePreserved index.mapping
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reachedIndex.mapping reachedIndex.store) :
    StableRows reached :=
  StableRows.after_administrative (install saved selected (.stable history)) reached
    (install_rows saved selected stable history) frame

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
  (reached : State headers keys
    ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
      entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)

/-- Full body admission is derived at the literal parameter entry. The real
ClosureFrame and Source-typed arguments supply heap typing; entry.nextHistory
and entry.frame supply every reached stable row. -/
theorem at_parameters (frame : Dynamic.ClosureFrame program function)
    (beforeTyped : Dynamic.HeapWellTyped function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
    (stable : StableRows caller) :
    Admission CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context reached := by
  refine ⟨CallableIndexedOwnedLambdaSourceAdmission.heap_typed_at_parameters
    captured code history inputs functions entry frame beforeTyped argumentsTyped, ?_⟩
  exact after_parameters caller reached owner.position stable entry.nextHistory entry.entry.frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaParameterAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
/-! A prepared principal packet retains the actual selected method, dictionary
and cached named compilation. Its one JointBody projects to existing method
support with no ordinary Header. Actual method Sites establish provenance;
prepared flow uses owning issuance and reached diagnostic interpretation at the
receiving registry. Prospective positive leaves retain preparation before
forward erasure. Existing plain StaticMember leaves cannot be upgraded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
open CallableIndexedOwnedPreparedOrdinaryBodyProjection (actualTree bodyWith)
open CallableIndexedOwnedTypedLambdaStaticBody (Body)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The selected method authority accompanies its actual prepared body. -/
structure Support (code : Code compiled.indexed function scope administrative) where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source principal.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed principal.named
  active : code.active = []
  issued : IssuedSource compiled code.compilation.owner function.source
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : JointBody principal.cached.compilation code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax certificates diagnosticPolicy
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault

section Site
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary environment scope administrative)

/-- The complete real method selector and same-Site joint body are retained. -/
def Support.of_site
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled site.code.compilation.owner
      (CallableIndexedNamedGeneration.source principal.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
      expressionSyntax certificates diagnosticPolicy
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault) : Support site.code :=
  ⟨method, principal, expressionSyntax, certificates, rfl, site.compilation, site.active,
    issued, diagnosticPolicy, body⟩

end Site

variable {code : Code compiled.indexed function scope administrative} (support : Support code)

/-- Recapture retains method selection, dictionary, preparation and exact flow. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) where
  method := support.method
  principal := support.principal
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  issued := support.issued
  diagnosticPolicy := support.diagnosticPolicy
  body := {
    toBody := {
      toContext := RecursiveNamedLambdaFormationHeads.recaptureContext
        (values := .initial compiled.compatible.checked) code support.body.toBody.toContext environment
      frame := RecursiveNamedLambdaFormationHeads.recaptureFrame support.body.frame environment
      readFuel := support.body.readFuel, flow := support.body.flow, projection := support.body.projection
      emitted := support.body.emitted, tree := support.body.tree, valid := support.body.valid
      unique := support.body.unique, syntaxTree := support.body.syntaxTree }
    recipe := support.body.recipe, generated := support.body.generated
    actual := support.body.actual, prepared := support.body.prepared }

/-- The genuine emitted hook's full method Source seed remains explicit. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.principal.named

/-- The original selected Site and its method dictionary establish provenance. -/
inductive PreparedAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) → Support code → Prop where
  | recaptured {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
        context principal.dictionary [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (issued : IssuedSource compiled site.code.compilation.owner
        (CallableIndexedNamedGeneration.source principal.named))
      (diagnosticPolicy : AssignmentDiagnosticPolicy)
      (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax certificates diagnosticPolicy
        issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
      (binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code)
      (issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained principal.named site.code)
      (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView site.code)
      (environment : Dynamic.Environment) :
      PreparedAt (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((Support.of_site principal site expressionSyntax certificates issued diagnosticPolicy body).recapture environment)

section Projection
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)

/-- Forward projection retains the full Principal and dictionary verbatim. -/
def Support.plain : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults where
  method := support.method
  principal := support.principal
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  body := bodyWith support.body actualSites sites

theorem Support.plain_typed :
    Body.of_body_with (support.plain actualSites sites).body support.body.syntaxTree = support.body.toBody := rfl

theorem Support.plain_source_origin {history : History code} (origin : SourceOrigin support history) :
    CallableIndexedOwnedMethodLambdaSupport.SourceOrigin (support.plain actualSites sites) history := ⟨origin.metadata⟩

include support in
/-- Method authority remains the original selected trait implementation. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original support.principal.record

theorem PreparedAt.plain_provenance (prepared : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code (support.plain actualSites sites) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView environment =>
    exact .recaptured principal site expressionSyntax certificates
      (bodyWith body actualSites sites) binderPolicy
      (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe principal.cached.compilation body.recipe)
      compilerPolicy issuedRecipe bodyView body.syntaxTree environment

theorem PreparedAt.projected_bindings (prepared : PreparedAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

end Projection

section Flow
variable
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (sameCode : Code compiled.indexed function scope captured.administrative)
  (prepared : Support sameCode)
  (baseActualSites : (actualTree prepared.body).CatalogSites .reachable bodyRegistry faults)
  (baseSites : prepared.body.tree.CatalogSites .reachable bodyRegistry faults)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : prepared.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    prepared.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    prepared.issued.assignments reason token → faults reason token)
  (interprets : ∀ context,
    Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := prepared.certificates prepared.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        prepared.diagnosticPolicy function.source prepared.issued.invalidOperand)
      (faults := faults) (registry := registry) prepared.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Original prepared head/loop producers discharge same-body flow preservation
at the receiving registry from strict expression children and reached tables. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context,
      Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context function.evidence function.source
          (prepared.certificates prepared.body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured sameCode
        (Body.of_body_with (prepared.plain baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [Support.plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.preserves_flow
    prepared.principal.cached.compilation captured sameCode prepared.issued prepared.body functions extension faithful
    observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget meaning

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Native flow keeps its own strict grade and independent Source completion. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context,
      Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context function.evidence function.source
          (prepared.certificates prepared.body.readFuel function.source context) faults size)) :
    RecursiveNamedCatalogInvocationBounds.Below budget
      (FlowReflects captured sameCode
        (Body.of_body_with (prepared.plain baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [Support.plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.reflects_flow
    prepared.principal.cached.compilation captured sameCode prepared.issued prepared.body functions extension faithful
    observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes reflection

end Flow

section Receipts
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A prospective method-authorized leaf keeps preparation beside its actual
captured method Source, emitted history and principal leading bundle. -/
inductive Receipt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code)
      (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
      (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
      (origin : SourceOrigin support history) (prepared : PreparedAt code support)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Receipt headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Existing typed association is a forward projection of the selected method. -/
def Receipt.forget
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore := by
  cases receipt with
  | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
    exact .principal owner captured code history (support.plain actualSites sites)
      (support.plain_source_origin actualSites sites origin) globals leading referenceIndex typed
      (PreparedAt.plain_provenance support actualSites sites prepared)

/-- Real capture and runtime-typing extension preserves all method authority. -/
def Receipt.extend
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Receipt headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases receipt with
  | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
    exact .principal owner (captured.extend maps worlds) code history support actualSites sites origin prepared
      globals leading referenceIndex (typed.weaken worlds)

end Receipts

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector
/-! Compiler-qualified ordinary bodies retain the actual selected formation
receipt and ChosenFactory before recapture. Their child certificates are the
original accepted compiler actions. The existing compiler induction constructs
one exact literal-supported expression Tree from each action; there is no
certificate-to-execution assumption. This finite ordinary/named/indirect static
collector does not classify arbitrary prepared Supports. A method collector
must retain its authentic Principal rather than manufacture an ordinary Header.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open CallableIndexedOwnedPreparedMixedBodySiteInputs

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {host : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed host.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) host.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)

/-- This constructor is available only at the actual compiler-produced
Formation. Code, Support, JointBody and Source environment are copied from it.
In particular there is no constructor accepting a certificate equality. -/
inductive Collected : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    Support code → Prop where
  | formed {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      (receipt : CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts.Receipt host diagnostics namedCode compilation
        context evidence scope id lowered)
      (chosen : ChosenFactory root expressionSyntax receipt)
      (environment : Dynamic.Environment) :
      Collected (receipt.formation.code environment) (receipt.formation.support environment)

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
  {support : Support code}

/-- The factory follows from the actual positive constructor, including the
exact original readFuel. It is never used as an inverse on old Supports. -/
theorem Collected.factories (collected : Collected root expressionSyntax code support) :
    support.expressionSyntax = expressionSyntax ∧ support.certificates = certificates root expressionSyntax := by
  cases collected with
  | formed receipt chosen environment =>
    have actual := recaptured_factory root expressionSyntax receipt chosen environment
    exact ⟨actual.1, actual.2.1⟩

theorem Collected.caller (collected : Collected root expressionSyntax code support) :
    support.caller = host := by
  cases collected with
  | formed receipt chosen environment => rfl

/-- Actual preparation remains attached to the same recaptured body. -/
theorem Collected.prepared (collected : Collected root expressionSyntax code support) :
    PreparedAt code support := by
  cases collected with
  | formed receipt chosen environment => exact receipt.formation.prepared environment

section Coverage
variable
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
  (domain : DomainAt root expressionSyntax support.body.readFuel currentContext function.evidence childScope headers)
  (valid : CompatibleRuntimeContextValidity.Valid (context compiled.indexed host.named).solvedRequirements
    currentContext function.evidence)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) currentContext function.source)

include runtime

/-- Only static Source/context/scope/metadata and accepted lowering receipts
enter this collector. Actual named selection and Principal authority remain
separate. All runtime child meanings are supplied by the later grade induction.
The output has the original child id and lowered value, with no existential
replacement of the compiler's expression or ordered physical children. -/
theorem Collected.cover_for (supported : Bool)
    (collected : Collected root expressionSyntax code support)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : support.certificates support.body.readFuel function.source currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers supported)
      support.body.readFuel (.initial compiled.compatible.checked) (source host.named) currentContext
      (context compiled.indexed host.named).solvedRequirements rootReasonAt childScope child output := by
  cases collected with
  | formed receipt chosen environment =>
    exact support_cover_for root expressionSyntax receipt supported chosen environment headers domain valid runtime actual

/-- The public static endpoint selects the genuine supported mode, keeping
ordinary, named and indirect call heads and original literal-site receipts. -/
theorem Collected.cover
    (collected : Collected root expressionSyntax code support)
    {child : ExpressionId} {output : SourceCoreBasic.LoweredExpr}
    (actual : support.certificates support.body.readFuel function.source currentContext childScope child output) :
    RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsFor
      (CallsFor root expressionSyntax (indirect_factory root expressionSyntax headers domain valid) headers true)
      support.body.readFuel (.initial compiled.compatible.checked) (source host.named) currentContext
      (context compiled.indexed host.named).solvedRequirements rootReasonAt childScope child output :=
  Collected.cover_for root expressionSyntax headers domain valid runtime true collected actual

end Coverage
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCompilerChildCollector
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
/-! One reusable static qualification facet restricts the positive prepared
closure leaves before payload or heap construction. Ordinary and Principal
Supports keep their original distinct authority. Map/world extension copies the
same Code and Support, so every qualification is preserved directly. Generic
ValueRep and GenericHeap operations use this function model without another
copy of allocation, write or payload recursion APIs. A concrete semantic family
must instantiate both facets from actual compiler collectors; an arbitrary
qualification, or the unrestricted prepared prototype, proves no body meaning.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualCellOrigins (Association)

/-- Qualification concerns the actual immutable compiler packet. It has no
execution, completion, grade or certificate-to-meaning field. Principal support
already contains its selected method, dictionary and cached compilation. -/
structure Facet (compiled : SourceCoreUnifiedCompilation.Compiled) where
  ordinary : ∀ {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context},
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code → Prop
  principal : ∀ {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context},
    (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (facet : Facet compiled)
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- Qualification inspects only the actual positive receipt's own Code and
Support. It cannot select or recover another body from the carrier's type. -/
def Association.Qualified
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result) : Prop := by
  cases association with
  | ordinary receipt =>
    cases receipt with
    | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed _callerGlobals _callerReceipt =>
      exact facet.ordinary code support
  | principal receipt =>
    cases receipt with
    | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
      exact facet.principal code support

/-- The original extension changes captures and runtime typing only. Static
qualification sees exactly the original Code, Support and selected authority. -/
theorem Association.Qualified.extend
    (association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (qualified : Association.Qualified facet association)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association.Qualified facet (association.extend maps worlds) := by
  cases association with
  | ordinary receipt =>
    cases receipt with
    | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed _callerGlobals _callerReceipt =>
      exact qualified
  | principal receipt =>
    cases receipt with
    | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
      exact qualified

/-- The proof is retained beside the exact prepared Association under Type;
public source-shaped membership exposes it under Nonempty. -/
structure QualifiedAssociation
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) where
  association : Association headers keys bodyRegistry faults mapping world function native bindings parameter result
  qualified : Association.Qualified facet association

def QualifiedAssociation.extend
    (member : QualifiedAssociation facet headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    QualifiedAssociation facet headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result :=
  ⟨member.association.extend maps worlds, Association.Qualified.extend facet member.association member.qualified maps worlds⟩

abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (QualifiedAssociation facet headers keys bodyRegistry faults mapping world function native bindings parameter result)

theorem StaticMember.forget
    (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedContextualCellOrigins.StaticMember headers keys bodyRegistry faults
      mapping world function native bindings parameter result := by
  obtain ⟨member⟩ := member
  exact ⟨member.association⟩

theorem StaticMember.extend
    (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember facet headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨member⟩ := member
  exact ⟨member.extend facet maps worlds⟩

/-- The same original global and builtin authority is preserved. Only closure
leaves acquire the static qualification, at their actual positive constructor. -/
inductive FunctionOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember facet headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      FunctionOrigins headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.global function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins headers keys bodyRegistry faults mapping world sourceType (.builtin function) native type

theorem FunctionOrigins.forget {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {type : Ty}
    (origin : FunctionOrigins facet headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedOwnedPreparedContextualCellOrigins.FunctionOrigins headers keys bodyRegistry faults
      mapping world sourceType source native type := by
  cases origin with
  | closure member => exact .closure (member.forget facet)
  | global related => exact .global related
  | builtin related => exact .builtin related

/-- The receiving registry is independent of the body's preparation registry.
All runtime type/projection facts are the existing forward facts. -/
def functions
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins facet headers keys bodyRegistry faults mapping world
  projection := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).projection
      (registry := bodyRegistry) (origin.forget facet)
  runtime_hasType := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) (origin.forget facet)
  source_function := fun origin =>
    (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile).source_function
      (registry := bodyRegistry) (origin.forget facet)
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type
      origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend facet maps worlds)
    | global related =>
      exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        related registries maps worlds)
    | builtin related =>
      exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        related registries maps worlds)

theorem functions_include_prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (functions facet headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile) :=
  fun origin => origin.forget facet

/-- The generic recursive payload and heap relations carry the qualification
through every nested function leaf. Their existing generic operations apply. -/
abbrev PayloadOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions facet headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functions facet headers keys bodyRegistry faults profile)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
/-! The actual lambda occurrence supplies declaration membership for every
parameter. Original parameter typing extends a genuine captured-scope lookup
correspondence to the compiler's reversed body scope. Native parameter types
remain arbitrary; they do not determine the original source schemes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
open Core Frontend SourceInference
open CallableIndexedLambdaValues

/-- The original typed lambda, rather than a native type projection, locates
its parameter declarations in the full source node table. -/
theorem parameters_declared {program : Program} {function : Dynamic.Closure}
    (frame : Dynamic.ClosureFrame program function) :
    ∀ binder ∈ function.parameters, binder ∈ SourceCoreDataPlaces.declaredBinders function.source := by
  intro binder member
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.expression node, contains.1, ?_⟩
  simpa only [form] using member

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty))
    (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih =>
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The same accepted parameter vector and raw context extension supply the
body's lookup correspondence. Captured declarations remain genuine inputs. -/
theorem at_parameters {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context) :
    CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      inputs.context := by
  have parameters := CallableIndexedLambdaEntryPrefix.parameters code
  have member : ∀ binding ∈ code.receipt.loweredParameters,
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders function.source := by
    intro binding present
    apply parameters_declared frame
    rw [parameters]
    exact List.mem_map.mpr ⟨binding, present, rfl⟩
  have extended := inputs.extended
  rw [parameters] at extended
  have declarations := RecursiveNamedHeaderScopeDeclarations.parameters member extended captured
  simpa only [reversed_scope] using declarations

/-- Every actual staged closure scope retains the same source declarations. -/
theorem at_selected_scope {values : SourceCoreCompatibleValues.Context}
    {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure function child) :
    CompatibleExpressionReads.ScopeDeclarations child.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      inputs.context := by
  rw [stages.source selected]
  exact at_parameters code inputs frame captured

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
/-! Actual ordinary and selected-method supports supply canonical protocol
packets at the genuine parameter Entry/Prefix. Their original captured globals,
physical bundle prefix and full Source metadata authenticate the same reached
row's own ghost. The body is the retained JointBody's literal typed projection;
no body-registry equality, escaped row or base-pool inverse is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedTypedLambdaProtocolContinuations (Packets)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {arguments : List Dynamic.Value} {nativeArguments : List Value} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

namespace Ordinary
variable (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)

include origin observed prefixContext in
/-- Both actual original producers derive their packet at this receiving
registry directly from the true parameter spine/read. The support's base
CatalogSites and any equality of independent registries play no role. -/
def packets : Packets (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
    captured code history support.body.toBody functions
    (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller) owner caller where
  source := by
    intro entry added length copied spine kept reached
    exact ⟨⟨reached, CallableIndexedOwnedLambdaNestedEntries.source_packet
      captured code history support.body.toBody.toContext functions owner support.caller
      observed prefixContext origin.metadata caller entry added length copied spine kept reached⟩, rfl⟩
  native := by
    intro entry reached
    exact ⟨⟨reached, CallableIndexedOwnedLambdaNestedEntries.native_packet
      captured code history support.body.toBody.toContext functions owner support.caller
      observed prefixContext origin.metadata caller entry reached⟩, rfl⟩

end Ordinary
namespace Principal
variable (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)

include origin observed leading in
/-- The Principal branch uses its actual Named and dictionary, with its own
bundle and metadata seed. It never constructs an ordinary Header. The exact
Entry/Prefix environments and reads manufacture the full canonical packet. -/
def packets : Packets (registry := registry) (arguments := arguments) (nativeArguments := nativeArguments)
    captured code history support.body.toBody functions
    (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) owner caller where
  source := by
    intro entry added length copied spine kept reached
    refine ⟨⟨reached, ?_⟩, rfl⟩
    apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
    · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
        entry.entry.reference⟩
    · exact entry.entry.environments
    · exact leading
    · exact origin.metadata ▸ entry.nextHistory
    · exact entry.entry.read
  native := by
    intro entry reached
    refine ⟨⟨reached, ?_⟩, rfl⟩
    obtain ⟨added, copied, length, spine, kept⟩ := entry.spine
    apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner support.principal.named reached
    · exact ⟨CallableIndexedOwnedLambdaCanonicalEntries.globals_after_prefix captured code owner 1 observed added length copied spine kept,
        entry.reference⟩
    · exact entry.environments
    · exact leading
    · exact origin.metadata ▸ entry.nextHistory
    · exact entry.read

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaProtocolPackets
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
/-! Authentic canonical bundle/global/frame observations and EnvRepresents
construct the used capture prefix. The owner's complete capture prefix and
ordered pool stay intact. Source history comes from the actual Nested or
Principal packet; native tags identify only the corresponding prefix types.
The selected method Site must separately match this prefix. No arbitrary
native environment or bare pool acquires Source authority here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedNamedGeneration (Named)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}

def «prefix» (named : Named) : Core.Context :=
  named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]

variable (named : Named) (owner : OwnedKey keys)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical actual : Environment}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {ξ : Renaming}
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope canonical owner.key.frameLocation)
  (bundle : (canonical.map Value.type)[scope.length]? = some named.signature.parameterType)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)

include complete observed bundle related in
/-- Every used slot follows the real packet and finite compiled inventory.
No global closure authority is cast to a different capture-prefix index. -/
theorem prefix_agrees : NativeExpressionContextSupport.Agrees
    («prefix» (compiled := compiled) named).length («prefix» (compiled := compiled) named) administrative := by
  have tags := related.runtime_hasTypes.type_tags
  have tag {index : Nat} {value : Value} (found : canonical[index]? = some value) :
      (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some value.type := by
    rw [← tags]
    simp [found]
  intro index smaller
  cases index with
  | zero =>
    rw [tags] at bundle
    simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append] using bundle
  | succ slot =>
    have bound : slot < compiled.indexed.base.globals.length + 1 := by
      simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil] at smaller
      omega
    by_cases globalSlot : slot < compiled.indexed.base.globals.length
    · let signature := compiled.indexed.base.globals[slot]
      have selected : compiled.indexed.base.globals[slot]? = some signature :=
        List.getElem?_eq_some_iff.mpr ⟨globalSlot, rfl⟩
      obtain ⟨target, member, sameSlot, sameSignature⟩ := complete slot signature selected
      have atType := tag (observed.globals target member)
      rw [sameSlot] at atType
      have outside : ¬ scope.length + 1 + slot < scope.length := by omega
      have offset : scope.length + 1 + slot - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append, outside, offset,
        globalSlot, selected, signature, sameSignature, SourceCoreCalls.Signature.referenceType,
        OptionalCell.referenceType, Value.type] using atType
    · have last : slot = compiled.indexed.base.globals.length := by omega
      have atType := tag observed.reference
      have outside : ¬ scope.length + 1 + compiled.indexed.base.globals.length < scope.length := by omega
      have offset : scope.length + 1 + compiled.indexed.base.globals.length - scope.length = slot + 1 := by omega
      simpa [SourceCoreLocalCell.coreContext, «prefix», List.getElem?_append, outside, offset,
        last, Value.type] using atType

include complete observed bundle related agrees typed in
/-- Only the used canonical administrative suffix is shortened. The complete
actual environment, Source cells, embedding and runtime typing stay original. -/
def capture : Captures compiled.indexed mapping world scope environment actual := by
  let represented := RecursiveNamedLambdaFormationHeads.environments_prefix related («prefix» (compiled := compiled) named)
    (prefix_agrees named owner complete observed bundle related)
  let same : EnvironmentsAgree ξ (canonical.take (scope.length + («prefix» (compiled := compiled) named).length)) actual :=
    RecursiveNamedLambdaFormationHeads.agrees_prefix agrees (scope.length + («prefix» (compiled := compiled) named).length)
  exact {
    administrative := «prefix» (compiled := compiled) named
    canonical := canonical.take (scope.length + («prefix» (compiled := compiled) named).length)
    actualContext := actualContext, embedding := ξ, represented := represented, agrees := same
    respects := TypedLexicalWhile.environment_respects represented.runtime_hasTypes typed same
    typed := typed }

/-- Original finite slot bounds keep every actual global and physical frame
in the capture. No empty catalog or zero owner-prefix assumption is used. -/
theorem capture_globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope (capture named owner complete observed bundle related agrees typed).canonical
    owner.key.frameLocation := by
  apply observed.take
  · intro header member
    have bound := RecursiveNamedLambdaFormationHeads.cached_capture_slots compiled headers header member
    simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega
  · simp only [«prefix», List.length_cons, List.length_append, List.length_map, List.length_nil]
    omega

namespace Ordinary
variable (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

include complete related agrees typed packet in
/-- The exact original packet constructs its own capture; no new state or
semantic capture-producing callback is supplied. -/
def captured : Captures compiled.indexed mapping world scope environment actual :=
  capture caller.named owner complete packet.observed packet.bundle related agrees typed

theorem captured_prefix : (captured owner complete related agrees typed caller initial packet).administrative =
    RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller := rfl

/-- The same owned pool is reindexed only by the shortened canonical suffix.
Its own history and exact ordered rows authenticate the resulting packet. -/
theorem packet_at_capture : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
    ⟨scope, mapping, world, heap, store, (captured owner complete related agrees typed caller initial packet).canonical⟩ initial := by
  exact CallableIndexedOwnedNestedCanonicalState.packet_of_stable_read owner caller
    (canonical := (captured owner complete related agrees typed caller initial packet).canonical) initial
    (capture_globals caller.named owner complete packet.observed packet.bundle related agrees typed)
    (captured owner complete related agrees typed caller initial packet).represented (by rfl)
    packet.carried (CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position)

/-- Source admission keeps its original deep heap and every row's stable
history because the projected pool is definitionally the same witness. -/
theorem admission_at_capture (context : SourceSemantics.Context)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) context ⟨initial, packet⟩) :
    CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller) context
      (index := ⟨scope, mapping, world, heap, store, (captured owner complete related agrees typed caller initial packet).canonical⟩)
      ⟨initial, packet_at_capture owner complete related agrees typed caller initial packet⟩ :=
  ⟨admitted.heap, admitted.rows⟩
end Ordinary

namespace Principal
variable (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner named _ initial)

include complete related agrees typed packet in
/-- The genuine selected Named and its own dictionary-bearing Source seed
remain in the packet. Prefix types do not manufacture that authority. -/
def captured : Captures compiled.indexed mapping world scope environment actual :=
  capture named owner complete packet.observed packet.bundle related agrees typed

theorem captured_prefix : (captured named owner complete related agrees typed initial packet).administrative =
    «prefix» (compiled := compiled) named := rfl

/-- Matching a selected method Site's administrative context to this prefix
remains an authentic static producer obligation; this proof keeps only the
same existing pool and its original Principal history. -/
theorem packet_at_capture : CallableIndexedOwnedOriginCanonicalState.Packet owner named
    ⟨scope, mapping, world, heap, store, (captured named owner complete related agrees typed initial packet).canonical⟩ initial := by
  exact CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner named
    (canonical := (captured named owner complete related agrees typed initial packet).canonical) initial
    (capture_globals named owner complete packet.observed packet.bundle related agrees typed)
    (captured named owner complete related agrees typed initial packet).represented (by rfl)
    packet.carried (CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position)

theorem admission_at_capture (context : SourceSemantics.Context)
    (admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named) context ⟨initial, packet⟩) :
    CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner named) context
      (index := ⟨scope, mapping, world, heap, store, (captured named owner complete related agrees typed initial packet).canonical⟩)
      ⟨initial, packet_at_capture named owner complete related agrees typed initial packet⟩ :=
  ⟨admitted.heap, admitted.rows⟩
end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCanonicalCaptureReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFunctionViews
/-! The retained prepared model has the actual existing runtime observations.
Only forward inclusion is used; observations never manufacture preparation
from a raw function type, current positive leaf or General representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFunctionViews
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualCellOrigins (functions PayloadOrigins CellOrigins)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

theorem functions_include_general :
    (functions headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile) := by
  intro registry mapping world sourceType source native type origin
  exact (CallableIndexedOwnedPreparedContextualCellOrigins.FunctionOrigins.forget origin).forget

theorem observations :
    FunctionObservations compiled.compatible.checked.catalog
      (functions headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

theorem runtime_views :
    FunctionRuntimeViews (functions headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.runtime_views keys bodyRegistry faults profile
    (registry := registry) (functions_include_general profile origin)

theorem payload_general {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : PayloadOrigins headers keys bodyRegistry registry faults profile
      mapping world sourceType source native type) :
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world sourceType source native type :=
  origin.map_functions (functions_include_general profile)

theorem cells_general {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      mapping world heap store :=
  CompatibleAmbientHeap.extend_definitions (functions_include_general profile) (.refl _) cells

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFunctionViews
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelStageReflection
/-! Native reflection of a genuinely rejected first gate retains the exact
callee trace and complete receiving function model. The original two-bind
inversion keeps independent strict native child bounds. Its result is the
existing staged boundary outcome with the same callee admission and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelStageReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedStoredIndirectStageBoundary
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {calleeNode : ExpressionNode}
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  {sourceValue : Dynamic.Value} {calleeNative : Value}
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context) bridge functionModel compiler first
    sourceValue calleeHeap calleeNative store mapping world)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue calleeNative)
  {reason : Staging.CallGuard.Fault}
  (rejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar) prepared.site.call ids sourceValue reason)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee sourceValue calleeHeap)

include caller sidecarSource post rejected calleeTrace in
/-- One authentic bounded completion uses the original first-gate inversion
and preservation producer at the same full function model. -/
theorem reflects_rejected (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ token, value = .inLeft compiler.resultType (.word token) ∧
      ForModel.ResultAt (registry := registry) (context := context) (evidence := evidence)
        (calleeNode := calleeNode) (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeSize := calleeSize)
        bridge functionModel compiler prepared first dispatch reason token finalStore ∧
      RejectedCompletion budget prepared.site native.diagnostics.unknown (compiler.calleeCode.expression.rename ξ)
        actual firstStore store calleeNative token := by
  have exactGate := gate_rejected dispatch rejected native.diagnostics.unknown actual store
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  obtain ⟨same, storeEq, bounds⟩ := completed_rejected post.1 exactGate full within
  subst finalStore
  exact ⟨dispatch.reason reason, same,
    ForModel.preserves_rejected bridge functionModel compiler prepared first post caller sidecarSource dispatch rejected calleeTrace,
    bounds⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelStageReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model.
The formation copies the captured cells, and the copies keep every global slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport (Support SourceOrigin PreparedAt)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : PreparedAt code support)
  (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
  (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
    support.caller function.context function.evidence))

open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (history_at source_origin reference_index)

include packet profile prefixContext observed provenance allSlots callerReceipt in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. The member is
the formed closure over the copies of its captured cells. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code (history_at captured code support owner initial packet) heap store
        owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember headers keys registry faults formed.finalMap
        formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  let history := history_at captured code support owner initial packet
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots provenance)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated,
    ⟨.preparedOrdinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture provenance formed.captured)
      (allSlots.of_slots formed.slots) callerReceipt⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalLambdaFormation
end
