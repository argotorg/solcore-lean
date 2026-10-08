import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryStoredMembers

/-! A positive chosen branch retains the literal compiler factory in the
function relation. Every General prior alternative remains explicit. The
unchanged public Prepared relation is reached only by forward forgetting. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedRuntimeFamilyMembers (OrdinaryIndex)
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedChosenOrdinaryStoredMembers (ChosenAt extendIndex)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)


/-- The actual constructor keeps its known index, history and chosen factory. -/
inductive Represents
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {mapping world raw source native type}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world raw source native type) :
      Represents headers keys registry faults mapping world raw source native type
  | chosen_ordinary (i : OrdinaryIndex compiled) (history : History i.code)
      (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
      Represents headers keys registry faults i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
        (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {raw : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

/-- Forward erasure retains the actual payload; it recovers no qualifier. -/
theorem Represents.forget
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    CallableIndexedOwnedPreparedOrdinaryLambdaValues.Represents headers keys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior original
  | chosen_ordinary i history member => exact (member.formed root expressionSyntax).represents

def model
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ => Represents root expressionSyntax headers keys bodyRegistry faults
  projection := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).projection
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  runtime_hasType := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  source_function := fun related => (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile).source_function
    (registry := bodyRegistry) (related.forget root expressionSyntax)
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld raw source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | chosen_ordinary i history member =>
      exact .chosen_ordinary (extendIndex i maps worlds) history (member.extend root expressionSyntax maps worlds)

/-- All old General alternatives remain available as the explicit prior branch. -/
theorem includes_general
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes
      (model root expressionSyntax headers keys bodyRegistry faults profile) := fun related => .prior related

/-- Only forward forgetting is provided to the unchanged public Prepared model. -/
theorem forget_inclusion
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model root expressionSyntax headers keys bodyRegistry faults profile).Includes
      (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys bodyRegistry faults profile) :=
  fun related => related.forget root expressionSyntax

theorem observations
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model root expressionSyntax headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world raw source native type related
  exact CallableIndexedOwnedPreparedOrdinaryLambdaValues.observations headers keys bodyRegistry faults profile
    (registry := registry) (related.forget root expressionSyntax)

theorem runtime_views
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model root expressionSyntax headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedOwnedPreparedOrdinaryLambdaValues.runtime_views headers keys bodyRegistry faults profile
    (registry := registry) (related.forget root expressionSyntax)

/-- Genuine owner embedding transports only the key fields of the same member. -/
theorem Represents.map_keys {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Represents root expressionSyntax headers futureKeys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | chosen_ordinary i history member => exact .chosen_ordinary i history (member.map_keys root expressionSyntax embedding)

/-- Exact selection preserves either the old alternative or the positive constructor. -/
inductive Selection
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {priorMap : LocationMap} {priorWorld : StoreTyping} {priorRaw : TypeSystem.Ty}
      {priorSource : Dynamic.Value} {priorNative : Value} {priorType : Ty}
      (selected : CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults priorMap priorWorld priorRaw priorSource priorNative priorType) :
      Selection headers keys registry faults priorMap priorWorld priorRaw priorSource priorNative priorType
  | chosen_ordinary (i : OrdinaryIndex compiled) (history : History i.code)
      (member : ChosenAt root expressionSyntax headers keys registry faults i history) :
      Selection headers keys registry faults i.mapping i.world (FunctionValues.sourceType i.function) (.closure i.function)
        (value i.code i.captured.embedding history.native i.capturedActual)
        (CallableContract.functionType i.code.receipt.parameterCore i.code.receipt.resultCore)

theorem Selection.of_represents
    (related : Represents root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Selection root expressionSyntax headers keys registry faults mapping world raw source native type := by
  cases related with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.of_represents original)
  | chosen_ordinary i history member => exact .chosen_ordinary i history member

theorem Selection.represents
    (selected : Selection root expressionSyntax headers keys registry faults mapping world raw source native type) :
    Represents root expressionSyntax headers keys registry faults mapping world raw source native type := by
  cases selected with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.represents original)
  | chosen_ordinary i history member => exact .chosen_ordinary i history member

section Observed
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {function : Dynamic.Closure}

def Selected : Prop := ∃ parameter result,
  SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
  Selection root expressionSyntax headers keys registry faults mapping world (.function parameter result) (.closure function) native type

private theorem selected_of_representation {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, Selection.of_represents root expressionSyntax value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

/-- Function-leaf selection eliminates only this actual model representation. -/
theorem selected_of_value
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax :=
  selected_of_representation root expressionSyntax profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context) {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Current admission is taken from this exact successful tuple. -/
theorem selected_at_success
    (post : CallableIndexedOwnedSourceAdmission.PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry (model root expressionSyntax headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw) (function := function) (native := native) (type := type) root expressionSyntax ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached := by
  exact ⟨selected_of_value root expressionSyntax profile related, post.at_value⟩
end Observed
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaValues
