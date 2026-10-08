import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! Formation retains a prepared packet before storage. Exact selection keeps
prior General alternatives explicit; no legacy closure is upgraded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Represents (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code body) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem Represents.forget (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | prior original => exact original.forget
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection
    (registry := bodyRegistry) related.forget
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related.forget
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
    (registry := bodyRegistry) related.forget
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
      exact .prepared_ordinary owner (captured.extend maps worlds) code history body origin prefixContext globals referenceIndex
        (typed.weaken worlds) prepared

theorem includes_general (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior related

theorem observations (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) related.forget

theorem runtime_views (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) related.forget

theorem Represents.map_keys {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Represents headers futureKeys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | @prepared_ordinary function scope actual owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .prepared_ordinary (embedding.map owner) captured code history body origin prefixContext actualGlobals referenceIndex typed prepared

/-- The prior branch preserves every original alternative and makes no
prepared-body promise for it. -/
inductive Selection (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
      (selected : CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world sourceType source native type) :
      Selection headers keys registry faults mapping world sourceType source native type
  | prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code body) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)


theorem Selection.of_represents (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.of_represents original)
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared

theorem Selection.represents (selected : Selection headers keys registry faults mapping world sourceType source native type) :
    Represents headers keys registry faults mapping world sourceType source native type := by
  cases selected with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.represents original)
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared

section Observed
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {function : Dynamic.Closure}

def Selected : Prop := ∃ parameter result,
  SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
  Selection headers keys registry faults mapping world (.function parameter result) (.closure function) native type

private theorem selected_of_representation {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, Selection.of_represents value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

theorem selected_of_value
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) :=
  selected_of_representation profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context) {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Source typing and current owned readiness come from this exact post. -/
theorem selected_at_success
    (post : CallableIndexedOwnedSourceAdmission.PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw) (function := function) (native := native) (type := type) ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached := by
  exact ⟨selected_of_value profile related, post.at_value⟩
end Observed
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
