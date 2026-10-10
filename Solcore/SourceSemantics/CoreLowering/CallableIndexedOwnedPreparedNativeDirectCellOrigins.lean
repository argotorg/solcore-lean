import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaMeaning

/-! Direct positive closure leaves retain their real compiler body and static
qualification. Their function model uses the Code's projection and runtime
receipt directly. No universal assignment diagnostic law is required to store
or form a closure. Global and builtin leaves retain their existing authority.
Neither a legacy closure leaf nor a native type manufactures this packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}

/-- Static qualification belongs to this exact prepared Support and Code. The
body registry indices concern global/builtin authority only. -/
inductive Association
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
      (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
      (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
      (qualified : qualification.ordinary code support)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association qualification headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
      (origin : CallableIndexedOwnedPreparedPrincipalLambdaSupport.SourceOrigin support history)
      (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
      (qualified : qualification.principal code support)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Association qualification headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

/-- Only captures and runtime typing change under actual map/world growth. -/
def Association.extend
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association qualification headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  cases association with
  | ordinary owner captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    exact .ordinary owner (captured.extend maps worlds) code history support origin prepared qualified
      prefixContext globals referenceIndex (typed.weaken worlds)
  | principal owner captured code history support origin prepared qualified globals leading referenceIndex typed =>
    exact .principal owner (captured.extend maps worlds) code history support origin prepared qualified
      globals leading referenceIndex (typed.weaken worlds)

theorem Association.source_binders
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) = function.parameters.map (fun binder => binder.scheme.body) := by
  cases association with
  | ordinary _ captured code history support origin prepared qualified prefixContext globals referenceIndex typed =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ captured code history support origin prepared qualified globals leading referenceIndex typed =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.scheme.body))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.source_ids
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.id) = function.parameters.map (fun binder => binder.id) := by
  cases association with
  | ordinary _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.id))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm
  | principal _ _ code _ _ _ _ _ _ _ _ _ =>
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map (fun binder : TypedBinder => binder.id))
        (CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code)).symm

theorem Association.result_core
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project function.resultType = .ok result := by
  cases association with
  | ordinary _ _ _ _ support _ _ _ _ _ _ _ => exact support.body.projection
  | principal _ _ _ _ support _ _ _ _ _ _ _ => exact support.body.projection

/-- The elementary lambda representation retains captures, Code and history;
it has no body or diagnostic field. This is a constructive forward projection. -/
theorem Association.lambda_represents
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) := by
  cases association with
  | ordinary _ captured code history _ _ _ _ _ _ _ typed => exact .lambda captured code history typed
  | principal _ captured code history _ _ _ _ _ _ _ typed => exact .lambda captured code history typed

theorem Association.native_type
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    native.type = CallableContract.functionType parameter result := by
  cases association with
  | ordinary _ _ _ _ _ _ _ _ _ _ _ typed => exact typed.type_eq
  | principal _ _ _ _ _ _ _ _ _ _ _ typed => exact typed.type_eq

/-- The literal Site binder policy and its real Source extension determine the
binder projections; the old diagnostic-bearing support is never built. -/
theorem Association.projected_bindings
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases association with
  | ordinary _ _ _ _ _ _ prepared _ _ _ _ _ =>
    cases prepared with
    | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy environment =>
      exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended
  | principal _ _ _ _ _ _ prepared _ _ _ _ _ =>
    cases prepared with
    | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy environment =>
      exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

theorem Association.parameter_core
    (association : Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  have projected := association.projected_bindings
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile projected support.body.projection
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    exact CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile projected support.body.projection

end Members

abbrev StaticMember
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameter result : Ty) : Prop :=
  Nonempty (Association qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)

section Members
variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}

theorem StaticMember.extend
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember qualification headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameter result := by
  obtain ⟨association⟩ := member
  exact ⟨association.extend maps worlds⟩

theorem StaticMember.source_binders
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.scheme.body) = function.parameters.map (fun binder => binder.scheme.body) := by
  obtain ⟨association⟩ := member
  exact association.source_binders

theorem StaticMember.source_ids
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    bindings.map (fun binding => binding.1.id) = function.parameters.map (fun binder => binder.id) := by
  obtain ⟨association⟩ := member
  exact association.source_ids

theorem StaticMember.result_core
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    compiled.compatible.checked.catalog.project function.resultType = .ok result := by
  obtain ⟨association⟩ := member
  exact association.result_core

theorem StaticMember.native_type
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    native.type = CallableContract.functionType parameter result := by
  obtain ⟨association⟩ := member
  exact association.native_type

theorem StaticMember.projected_bindings
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    ∀ binding ∈ bindings, compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  obtain ⟨association⟩ := member
  exact association.projected_bindings

theorem StaticMember.parameter_core
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    parameter = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) := by
  obtain ⟨association⟩ := member
  exact association.parameter_core profile

end Members

inductive FunctionOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | closure {function : Dynamic.Closure} {native : Value}
      {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
      (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world
        (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result)
  | global {function : Dynamic.GlobalFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.global function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType (.global function) native type
  | builtin {function : Dynamic.BuiltinFunction} {sourceType : TypeSystem.Ty} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys bodyRegistry faults
        mapping world sourceType (.builtin function) native type) :
      FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType (.builtin function) native type

/-- Closure facts are proved from the retained Code and runtime receipt. The
receiving registry remains independent; no legacy closure model is projected. -/
def functions
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => FunctionOrigins qualification headers keys bodyRegistry faults mapping world
  projection := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure member =>
      obtain ⟨association⟩ := member
      cases association with
      | ordinary _ _ code _ _ _ _ _ _ _ _ _ => exact code.projection
      | principal _ _ code _ _ _ _ _ _ _ _ _ => exact code.projection
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).projection (registry := bodyRegistry) related
  runtime_hasType := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure member =>
      obtain ⟨association⟩ := member
      cases association with
      | ordinary _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
      | principal _ _ _ _ _ _ _ _ _ _ _ typed => exact typed
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType (registry := bodyRegistry) related
  source_function := by
    intro registry mapping world sourceType source native type origin
    cases origin with
    | closure => exact .closure _
    | global related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) related
    | builtin related => exact (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).source_function (registry := bodyRegistry) related
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type origin registries maps worlds
    cases origin with
    | closure member => exact .closure (member.extend maps worlds)
    | global related => exact .global ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)
    | builtin related => exact .builtin ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend related registries maps worlds)

theorem FunctionOrigins.lambda_represents
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {native : Value} {type : Ty}
    (origin : FunctionOrigins qualification headers keys bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases origin with
  | closure member =>
    obtain ⟨association⟩ := member
    exact association.lambda_represents
  | global related => exact related.forget
  | builtin related => exact related.forget

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
    origin.lambda_represents

theorem runtime_views (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (functions qualification headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type origin
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry)
    origin.lambda_represents

abbrev PayloadOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  ValueRep compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

abbrev CellOrigins
    (qualification : Facet compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile)

section Outputs
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem payload_static_member {function : Dynamic.Closure}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result) :
    PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function) native (CallableContract.functionType parameter result) :=
  .function (.closure member)

theorem closure_member
    (origin : PayloadOrigins qualification headers keys bodyRegistry registry faults profile mapping world sourceType source native type) :
    ∀ function, source = .closure function →
      ∃ bindings parameter result,
        StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result ∧
        type = CallableContract.functionType parameter result := by
  induction origin using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | closure member => intro function same; cases same; exact ⟨_, _, _, member, rfl⟩
    | global related => intro function impossible; cases impossible
    | builtin related => intro function impossible; cases impossible
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

end Outputs

/-- The original reached state retains direct cells and the represented result.
No additional body or completion premise is installed in this postcondition. -/
structure Post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (context : SourceSemantics.Context) (qualification : Facet compiled)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (sourceType : TypeSystem.Ty) (type : Ty) (outcome : Dynamic.ExpressionOutcome) (value : Value)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  admission : PostAdmission bridge context sourceType outcome reached
  cells : CellOrigins qualification headers keys bodyRegistry registry faults profile index.mapping index.world index.heap index.store
  result : FunctionCalls.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (functions qualification headers keys bodyRegistry faults profile))
    index.mapping index.world sourceType type faults outcome value

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
