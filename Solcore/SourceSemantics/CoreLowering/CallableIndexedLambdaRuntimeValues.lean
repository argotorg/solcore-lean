import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration

/-! Runtime lambda values retain the actual compiler code, captures and history
with a static body receipt for one fixed program, registry and fault relation.
The value model uses that same registry when consumed by runtime meaning. Its
ordinary ghost registry parameter does not change the stored body receipt.
No body execution law or registry transport is part of this representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues

variable {values : SourceCoreCompatibleValues.Context} (prepared : SourceCoreCallableIndexedPrograms.Prepared values.checked)
  (program : Program) (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)

/-- A support family retains static receipts for this exact Code. -/
abbrev SupportFamily :=
  {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} → {administrative : Core.Context} →
    Code prepared function scope administrative → Type

/-- Static capture and origin conditions are indexed by the actual captures,
Code and History. Catalog authority is supplied separately at invocation. -/
abbrev SupportCondition (support : SupportFamily prepared) :=
  {mapping : LocationMap} → {world : StoreTyping} → {function : Dynamic.Closure} →
    {scope : SourceCoreLocalCell.Scope} → {actual : Core.Environment} →
    (captured : Captures prepared mapping world scope function.captured actual) →
    (code : Code prepared function scope captured.administrative) →
    History code → support code → Prop

/-- Static ordered capture observations compose with any same-Code/History
origin receipt. Authority is deliberately absent from this condition. -/
def captureCondition (support : SupportFamily prepared)
    (origin : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → (code : Code prepared function scope administrative) → History code → Prop)
    {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
    {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
    (callerPrefix : Nat) : SupportCondition prepared support :=
  fun {_mapping _world _function scope _actual} captured code history _ =>
    origin code history ∧ ∃ location,
      CallableIndexedLambdaCatalogEntries.CaptureGlobals headers locations callerPrefix scope captured.canonical location

theorem captureCondition_stable (support : SupportFamily prepared)
    (origin : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → (code : Code prepared function scope administrative) → History code → Prop)
    {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
    {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
    (callerPrefix : Nat) {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code) (body : support code)
    (supported : captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix captured code history body)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    captureCondition prepared program support origin (headers := headers) (locations := locations)
      callerPrefix (captured.extend maps worlds) code history body := supported

inductive RepresentsWith (support : SupportFamily prepared) (P : SupportCondition prepared support)
    (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | retained {sourceType source native type}
      (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
      RepresentsWith support P mapping world sourceType source native type
  | lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code)
      (body : support code) (supported : P captured code history body)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) prepared.layouts.definitions) :
      RepresentsWith support P mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

theorem RepresentsWith.forget {support : SupportFamily prepared} {P : SupportCondition prepared support}
    {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (related : RepresentsWith prepared support P mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents prepared mapping world sourceType source native type := by
  cases related with
  | retained prior => exact .retained prior
  | lambda captured code history _ _ typed => exact .lambda captured code history typed

/-- Extension transports only the supplied static predicate, without changing
Code, its support receipt, the full actual environment or captured history. -/
def modelWith (support : SupportFamily prepared) (P : SupportCondition prepared support)
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      P (captured.extend maps worlds) code history body)
    (profile : values.checked.catalog.callableContracts = true) :
    FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ mapping world => RepresentsWith prepared support P mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    exact (CallableIndexedLambdaValues.model prepared profile).projection (registry := registry)
      (RepresentsWith.forget prepared related)
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    exact (CallableIndexedLambdaValues.model prepared profile).runtime_hasType (registry := registry)
      (RepresentsWith.forget prepared related)
  source_function := by
    intro registry mapping world sourceType source native type related
    exact (CallableIndexedLambdaValues.model prepared profile).source_function (registry := registry)
      (RepresentsWith.forget prepared related)
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | retained prior => exact .retained ((CallableIndexedRetainedNamedValues.model prepared profile).extend prior registries maps worlds)
    | lambda captured code history body supported typed =>
      exact .lambda (captured.extend maps worlds) code history body
        (stable captured code history body supported maps worlds) (typed.weaken worlds)

theorem observationsWith (support : SupportFamily prepared) (P : SupportCondition prepared support)
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      P (captured.extend maps worlds) code history body)
    (profile : values.checked.catalog.callableContracts = true) :
    FunctionObservations values.checked.catalog (modelWith prepared support P stable profile) (Identity prepared) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations prepared profile (registry := registry)
    (RepresentsWith.forget prepared related)

theorem runtimeViewsWith (support : SupportFamily prepared) (P : SupportCondition prepared support)
    (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body →
      ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
      P (captured.extend maps worlds) code history body)
    (profile : values.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (modelWith prepared support P stable profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views prepared profile (registry := registry)
    (RepresentsWith.forget prepared related)

inductive Represents (mapping : LocationMap) (world : StoreTyping) :
    TypeSystem.Ty → Dynamic.Value → Core.Value → Core.Ty → Prop where
  | retained {sourceType source native type}
      (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
      Represents mapping world sourceType source native type
  | lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Core.Environment}
      (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code)
      (body : CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) prepared.layouts.definitions) :
      Represents mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

abbrev legacySupport : SupportFamily prepared :=
  fun {_ _ _} code => CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults

abbrev legacyCondition : SupportCondition prepared (legacySupport prepared program bodyRegistry faults) :=
  fun _ _ _ _ => True

theorem Represents.toWith {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (related : Represents prepared program bodyRegistry faults mapping world sourceType source native type) :
    RepresentsWith prepared (legacySupport prepared program bodyRegistry faults)
      (legacyCondition prepared program bodyRegistry faults) mapping world sourceType source native type := by
  cases related with
  | retained prior => exact .retained prior
  | lambda captured code history body typed => exact .lambda captured code history body True.intro typed

theorem Represents.fromWith {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (related : RepresentsWith prepared (legacySupport prepared program bodyRegistry faults)
      (legacyCondition prepared program bodyRegistry faults) mapping world sourceType source native type) :
    Represents prepared program bodyRegistry faults mapping world sourceType source native type := by
  cases related with
  | retained prior => exact .retained prior
  | lambda captured code history body _ typed => exact .lambda captured code history body typed

theorem Represents.forget {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (related : Represents prepared program bodyRegistry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents prepared mapping world sourceType source native type := by
  cases related with
  | retained prior => exact .retained prior
  | lambda captured code history _ typed => exact .lambda captured code history typed

/-- Registry extension leaves the model's fixed body registry unchanged. The
same code and static body survive extensions of captures and native typing. -/
def model (profile : values.checked.catalog.callableContracts = true) :
    FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ mapping world => Represents prepared program bodyRegistry faults mapping world
  projection := by
    intro registry mapping world sourceType source native type related
    exact (modelWith prepared (legacySupport prepared program bodyRegistry faults)
      (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile).projection
      (registry := registry) (Represents.toWith prepared program bodyRegistry faults related)
  runtime_hasType := by
    intro registry mapping world sourceType source native type related
    exact (modelWith prepared (legacySupport prepared program bodyRegistry faults)
      (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile).runtime_hasType
      (registry := registry) (Represents.toWith prepared program bodyRegistry faults related)
  source_function := by
    intro registry mapping world sourceType source native type related
    exact (modelWith prepared (legacySupport prepared program bodyRegistry faults)
      (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile).source_function
      (registry := registry) (Represents.toWith prepared program bodyRegistry faults related)
  extend := by
    intro registry futureRegistry mapping futureMapping world futureWorld sourceType source native type related registries maps worlds
    exact Represents.fromWith prepared program bodyRegistry faults
      ((modelWith prepared (legacySupport prepared program bodyRegistry faults)
        (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile).extend
        (Represents.toWith prepared program bodyRegistry faults related) registries maps worlds)

theorem observations (profile : values.checked.catalog.callableContracts = true) :
    FunctionObservations values.checked.catalog (model prepared program bodyRegistry faults profile) (Identity prepared) := by
  intro registry mapping world sourceType source native type related
  exact observationsWith prepared (legacySupport prepared program bodyRegistry faults)
    (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile
    (registry := registry) (Represents.toWith prepared program bodyRegistry faults related)

theorem runtime_views (profile : values.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model prepared program bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact runtimeViewsWith prepared (legacySupport prepared program bodyRegistry faults)
    (legacyCondition prepared program bodyRegistry faults) (fun _ _ _ _ _ _ _ => True.intro) profile
    (registry := registry) (Represents.toWith prepared program bodyRegistry faults related)

private theorem retained_not_closure {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (related : CallableIndexedRetainedNamedValues.Represents prepared world sourceType source native type) :
    ∀ function, source ≠ .closure function := by
  cases related with
  | retained canonical => cases canonical with
    | builtin builtin => cases builtin; intro function impossible; cases impossible
    | named => intro function impossible; cases impossible

/-- The generic model returns the exact same Code, History, support receipt
and static capture/origin condition that were stored at formation. -/
theorem RepresentsWith.closure_inv {support : SupportFamily prepared} {P : SupportCondition prepared support}
    {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Core.Value} {type : Core.Ty}
    (related : RepresentsWith prepared support P mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code) (body : support code),
      P captured code history body ∧ sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  cases related with
  | retained prior => exact False.elim (retained_not_closure prepared prior function rfl)
  | lambda captured code history body supported _ => exact ⟨_, _, captured, code, history, body, supported, rfl, rfl, rfl⟩

section FormationWith
variable {support : SupportFamily prepared} {P : SupportCondition prepared support}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
  (captured : Captures prepared mapping world scope function.captured actual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (body : support code) (supported : P captured code history body)
  (profile : values.checked.catalog.callableContracts = true)
  {store : Store} {location : Location}
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native))

include body supported profile stored reference read in
theorem formation_represents_with :
    RepresentsWith prepared support P mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  have prior := CallableIndexedLambdaValues.formation_represents captured code history stored reference read
  have typed := (CallableIndexedLambdaValues.model prepared profile).runtime_hasType (registry := values.registry) prior
  exact .lambda captured code history body supported typed

include body supported profile stored reference read in
theorem formation_with (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    RepresentsWith prepared support P mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  ⟨CallableIndexedLambdaValues.source_formation code program heap ordinary coercions,
    CallableIndexedLambdaValues.formation_evaluates captured code history reference read,
    formation_represents_with prepared captured code history body supported profile stored reference read⟩

include body supported profile stored reference read in
theorem reflects_with (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename captured.embedding) result after) :
    result = .inRight .word (value code captured.embedding history.native actual) ∧ after = store ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    RepresentsWith prepared support P mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨sameResult, sameStore, source, _⟩ := CallableIndexedLambdaValues.reflects captured code history program heap
    ordinary coercions stored reference read completed
  exact ⟨sameResult, sameStore, source,
    formation_represents_with prepared captured code history body supported profile stored reference read⟩
end FormationWith

/-- The same emitted code supplies the body receipt, rather than a body chosen
only by source closure type or by a decoded native descriptor. -/
theorem Represents.closure_inv {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Core.Value} {type : Core.Ty}
    (related : Represents prepared program bodyRegistry faults mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures prepared mapping world scope function.captured actual)
      (code : Code prepared function scope captured.administrative) (history : History code),
      Nonempty (CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults) ∧
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  cases related with
  | retained prior => exact False.elim (retained_not_closure prepared prior function rfl)
  | lambda captured code history body _ => exact ⟨_, _, captured, code, history, ⟨body⟩, rfl, rfl, rfl⟩

/-- Closure provenance is obtained from the stored source body frame, never
from native closure typing or a weakened value relation. -/
theorem Represents.closure_frame {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Core.Value} {type : Core.Ty}
    (related : Represents prepared program bodyRegistry faults mapping world sourceType (.closure function) native type) :
    Dynamic.ClosureFrame program function := by
  obtain ⟨_, _, _, _, _, ⟨body⟩, _⟩ := Represents.closure_inv prepared program bodyRegistry faults related
  exact body.frame

section Formation
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}
  (captured : Captures prepared mapping world scope function.captured actual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (body : CallableIndexedLambdaRuntimeBody.Body code program bodyRegistry faults)
  (profile : values.checked.catalog.callableContracts = true)
  {store : Store} {location : Location}
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native))

include body profile stored reference read in
/-- The original formation proof supplies the exact native result typing. The
new representation stores the independently constructed same-code body. -/
theorem formation_represents :
    Represents prepared program bodyRegistry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  Represents.fromWith prepared program bodyRegistry faults
    (formation_represents_with prepared captured code history body True.intro profile stored reference read)

include body profile stored reference read in
theorem formation (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    Represents prepared program bodyRegistry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  by
    obtain ⟨source, evaluated, related⟩ := formation_with prepared program
      (support := legacySupport prepared program bodyRegistry faults)
      (P := legacyCondition prepared program bodyRegistry faults) captured code history body
      True.intro profile stored reference read heap ordinary coercions
    exact ⟨source, evaluated, Represents.fromWith prepared program bodyRegistry faults related⟩

include body profile stored reference read in
/-- Reflection consumes the original native completion. Determinism identifies
the actual formed closure; no body computation is run during formation. -/
theorem reflects (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename captured.embedding) result after) :
    result = .inRight .word (value code captured.embedding history.native actual) ∧ after = store ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Represents prepared program bodyRegistry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨sameResult, sameStore, source, related⟩ := reflects_with prepared program
    (support := legacySupport prepared program bodyRegistry faults)
    (P := legacyCondition prepared program bodyRegistry faults) captured code history body
    True.intro profile stored reference read heap ordinary coercions completed
  exact ⟨sameResult, sameStore, source, Represents.fromWith prepared program bodyRegistry faults related⟩

end Formation

section ActualSite
open CallableIndexedLambdaGeneration

variable {named : CallableIndexedNamedGeneration.Named} {parameters : List TypedBinder} {resultType : TypeSystem.Ty}
  {statements : List StatementId} {sourceContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {capturedSource : Dynamic.Environment}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {actual : Core.Environment}
  (captured : Captures prepared mapping world scope capturedSource actual)
  (site : Site prepared named parameters resultType statements sourceContext evidence capturedSource scope captured.administrative)
  (body : CallableIndexedLambdaRuntimeBody.Body site.code program bodyRegistry faults)
  (profile : values.checked.catalog.callableContracts = true)
  {origin : Word}
  (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
  (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
  (heap : Dynamic.Heap)
  (ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions [])
  (coercions : site.code.sourceNode.coercions = [])
  {entryStore store : Store} {location : Location} {saved : Core.Value} {entryMap : LocationMap}
  (entryRead : entryStore.read? location = some saved) (unmapped : location ∉ entryMap)
  (preserved : AdministrativePreserved entryMap
    (entryStore.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) mapping store)
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
  (reference : captured.canonical[site.code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))

include body profile selected record ordinary coercions entryRead unmapped preserved stored reference in
/-- The accepted named callback fixes the actual lambda Code and its history.
The same-code static body is stored at formation after the original prefix. -/
theorem accepted_site_formation :
    Dynamic.ExpressionEvaluates program sourceContext evidence (CallableIndexedNamedGeneration.source named) capturedSource heap site.code.id
      (.closure (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource)) heap ∧
    Evaluates actual store (site.code.lowered.expression.rename captured.embedding)
      (.inRight .word (value site.code captured.embedding
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)) store ∧
    Represents prepared program bodyRegistry faults mapping world
      (FunctionValues.sourceType (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource))
      (.closure (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource))
      (value site.code captured.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)
      (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := CallableIndexedLambdaGeneration.installed_after_prefix selected record entryRead unmapped preserved
  exact formation (values := values)
    (function := CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource)
    prepared program bodyRegistry faults captured site.code (site.historyAt selected record) body profile
    stored reference cell.read heap ordinary coercions

include body profile selected record ordinary coercions entryRead unmapped preserved stored reference in
/-- Completed formation reflection keeps the same accepted site and body. -/
theorem accepted_site_reflection {output : Core.Value} {after : Store}
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    output = .inRight .word (value site.code captured.embedding
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual) ∧ after = store ∧
    Dynamic.ExpressionEvaluates program sourceContext evidence (CallableIndexedNamedGeneration.source named) capturedSource heap site.code.id
      (.closure (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource)) heap ∧
    Represents prepared program bodyRegistry faults mapping world
      (FunctionValues.sourceType (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource))
      (.closure (CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource))
      (value site.code captured.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) actual)
      (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := CallableIndexedLambdaGeneration.installed_after_prefix selected record entryRead unmapped preserved
  exact reflects (values := values)
    (function := CallableIndexedLambdaGeneration.closure named parameters resultType statements sourceContext evidence capturedSource)
    prepared program bodyRegistry faults captured site.code (site.historyAt selected record) body profile
    stored reference cell.read heap ordinary coercions completed
end ActualSite
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues
