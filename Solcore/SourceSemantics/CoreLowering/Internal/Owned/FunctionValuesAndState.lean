import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins

/-!
# Owned callables: function values and state

`CallableIndexedOwnedFunctionValues`, immutable keys and headers, and `CallableIndexedOwnedFunctionState`, the reached pool as a protected state, with function entries, allocation, body restoration and physical globals.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
/-! Function values carry immutable keys in one fixed ordered domain. Live
catalogue authority remains in the reached pool. Named and lambda constructors
retain full source evidence and captures; no unrestricted retained constructor
or body execution law is part of this store-independent model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues

abbrev Header (compiled : SourceCoreUnifiedCompilation.Compiled) (program : Program) :=
  RecursiveNamedCatalog.Header compiled.indexed.ancestry (.initial compiled.compatible.checked)
    compiled.indexed.layouts.definitions program
abbrev Key (compiled : SourceCoreUnifiedCompilation.Compiled) (program : Program) :=
  CallableIndexedAuthorityPool.Key compiled.indexed.ancestry (.initial compiled.compatible.checked)
    compiled.indexed.layouts.definitions program

/-- The position certifies membership in this execution's fixed domain. The
immutable key is the selected value, independent of any reached store. -/
structure OwnedKey {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (keys : List (Key compiled program)) where
  position : Fin keys.length

def OwnedKey.key {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    {keys : List (Key compiled program)} (owner : OwnedKey keys) : Key compiled program :=
  keys[owner.position.val]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)}

/-- Every static field is projected from the actual full capture. Its live
read, locals and administrative disjointness remain separate reached facts. -/
structure NamedCapture (headers : List (Header compiled program)) (key : Key compiled program)
    (header : Header compiled program) (mapping : LocationMap) (world : StoreTyping) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative [] [] canonical compiled.indexed.layouts.definitions
  layout : EnvironmentsAgree embedding canonical captured
  typed : RuntimeEnvironmentHasTypes world captured capturedContext compiled.indexed.layouts.definitions
  reference : canonical[header.globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type key.frameLocation)
  capturedReference : captured[embedding compiled.indexed.base.globals.length]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type key.frameLocation)
  coherent : ∀ target, target ∈ headers → canonical[key.capturePrefix + target.slot]? = some
    (.cellRef (OptionalCell.cellType target.named.signature.functionType) (key.locations target))

def NamedCapture.of_capture {key : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (program := program)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers key.locations key.capturePrefix key.frameLocation
      header mapping world heap store) : NamedCapture headers key header mapping world :=
  ⟨capture.administrative, capture.canonical, capture.captured, capture.capturedContext,
    capture.embedding, capture.environments, capture.layout, capture.typed, capture.reference,
    capture.capturedReference, capture.coherent⟩

def NamedCapture.extend {key : Key compiled program} {header : Header compiled program}
    {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    (capture : NamedCapture headers key header mapping world)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    NamedCapture headers key header futureMap futureWorld :=
  { capture with
    environments := capture.environments.extend maps worlds
    typed := capture.typed.weaken worlds }

/-- Retained source order and canonical header order share the exact body and
ordered dictionary, through an explicit static instantiation transport. -/
structure NamedSourceAt (header : Header compiled program)
    (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment) (source : Dynamic.GlobalFunction) : Prop where
  row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature header.named.specialized rawD
  retained : source = CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized rawD)
  dictionary : header.function.evidence = source.evidence
  frame : NamedCalls.SourceFrame program source.instantiation header.sourceBody header.function
  sourceOrigin : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
    header.named.signature.key [] header.function.source
  unique : NodeOccurrencesUnique header.function.source

theorem NamedSourceAt.of_canonical_header {header : Header compiled program}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature header.named.specialized rawD)
    (canonical : header.instantiation = CallableNamedMetadata.instantiation header.named.specialized)
    (dictionary : header.function.evidence = (CallableNamedMetadata.global header.named.specialized rawD).evidence) :
    NamedSourceAt header rawD (CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized rawD)) := by
  have original := header.frame.instantiated
  rw [canonical] at original
  exact ⟨row, rfl, dictionary,
    { header.frame with instantiated := RecursiveNamedRetainedSubstitutionFacts.instantiates_reverse original },
    (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1, header.unique⟩

theorem NamedSourceAt.of_retained_header {header : Header compiled program}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature header.named.specialized rawD)
    (retained : header.instantiation = CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized))
    (dictionary : header.function.evidence = (CallableNamedMetadata.global header.named.specialized rawD).evidence) :
    NamedSourceAt header rawD (CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized rawD)) := by
  refine ⟨row, rfl, dictionary, ?_, (CallableIndexedActualNamedSourceReceipts.header_source compiled header).1, header.unique⟩
  simpa only [retained, CallableNamedReversal.global, CallableNamedMetadata.global] using header.frame

def NamedInstalledCode {key : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} (capture : NamedCapture headers key header mapping world) : Prop :=
  ∃ template, compiled.indexed.secondPass.closures[header.slot]? = some template ∧
    SourceCoreCompatibleOutputs.installedTemplate header.slot template =
      .lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift)

abbrev StaticSupport (headers : List (Header compiled program))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    CallableIndexedLambdaRuntimeValues.SupportFamily (values := .initial compiled.compatible.checked) compiled.indexed :=
  fun {_ _ _} code => CallableIndexedLambdaNestedRuntimeCertificates.Support
    (values := .initial compiled.compatible.checked) headers registry faults code

structure ActualSourceOrigin {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (code : Code compiled.indexed function scope administrative) (history : History code)
    (body : StaticSupport headers registry faults code) : Prop where
  historyMetadata : history.metadata = CallableIndexedNamedGeneration.state body.1.named
  source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
    code.compilation.owner code.active function.source
  unique : NodeOccurrencesUnique function.source

theorem ActualSourceOrigin.of_support {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative} (history : History code)
    (body : StaticSupport headers registry faults code)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state body.1.named) :
    ActualSourceOrigin code history body :=
  ⟨metadata, (CallableIndexedLambdaNestedStageOrigins.support_provenance compiled body).1,
    (CallableIndexedLambdaNestedStageOrigins.support_provenance compiled body).2⟩

/-- Recapture keeps the static support of the same code. -/
def StaticSupport.recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative}
    (body : StaticSupport headers registry faults code) (environment : Dynamic.Environment) :
    StaticSupport headers registry faults (code.recapture environment) :=
  ⟨body.1, body.2.1, body.2.2.recapture environment⟩

/-- Recapture keeps the origin: the same history metadata, preparation and
source. -/
theorem ActualSourceOrigin.recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {code : Code compiled.indexed function scope administrative} {history : History code}
    {body : StaticSupport headers registry faults code}
    (origin : ActualSourceOrigin code history body) (environment : Dynamic.Environment) :
    ActualSourceOrigin (code.recapture environment) (history.recapture environment) (body.recapture environment) :=
  ⟨origin.historyMetadata, origin.source, origin.unique⟩

inductive Represents (headers : List (Header compiled program)) (keys : List (Key compiled program))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {sourceType source native type}
      (related : CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | named {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
      {source : Dynamic.GlobalFunction} {identity : Word}
      (owner : OwnedKey keys) (member : header ∈ headers)
      (sourceAt : NamedSourceAt header rawD source)
      (capture : NamedCapture headers owner.key header mapping world) (installed : NamedInstalledCode capture)
      (number : Word.ofNat? (header.slot + 1) = some identity)
      (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
        (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table (.named header.named.signature.key))
      (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
        header.named.signature.functionType compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world header.named.specialized.function.type (.global source)
        (.pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured))
          (.word descriptor.id)) (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  | lambda {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment} {callerPrefix : Nat}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : StaticSupport headers registry faults code) (origin : ActualSourceOrigin code history body)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := program) headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

theorem Represents.forget {keys : List (Key compiled program)} {registry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | builtin prior =>
    cases prior
    exact .retained (.retained (.builtin (.builtin ‹_› ‹_› ‹_› ‹_›)))
  | named owner member sourceAt capture installed number projection descriptor typed =>
    rw [sourceAt.retained]
    exact .retained (.retained (.named sourceAt.row number projection descriptor ⟨installed, typed⟩))
  | lambda owner captured code history body origin globals referenceIndex typed =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled program)) (keys : List (Key compiled program))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection (registry := bodyRegistry) (Represents.forget related)
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType (registry := bodyRegistry) (Represents.forget related)
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function (registry := bodyRegistry) (Represents.forget related)
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | builtin prior => exact .builtin ((CallableIndexedBuiltinValues.model compiled.indexed profile).extend prior registries maps worlds)
    | named owner member sourceAt capture installed number projection descriptor typed =>
      exact .named owner member sourceAt (capture.extend maps worlds) installed number projection descriptor (typed.weaken worlds)
    | lambda owner captured code history body origin globals referenceIndex typed =>
      exact .lambda owner (captured.extend maps worlds) code history body origin globals referenceIndex (typed.weaken worlds)

theorem observations (keys : List (Key compiled program)) (bodyRegistry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) (Represents.forget related)

theorem runtime_views (keys : List (Key compiled program)) (bodyRegistry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) (Represents.forget related)

/-- Domain changes are explicit and preserve the entire immutable key. -/
structure KeyEmbedding (keys futureKeys : List (Key compiled program)) where
  map : OwnedKey keys → OwnedKey futureKeys
  same : ∀ owner, (map owner).key = owner.key

def NamedCapture.rekey {key other : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} (capture : NamedCapture headers key header mapping world)
    (same : other = key) : NamedCapture headers other header mapping world := same ▸ capture

theorem NamedCapture.rekey_embedding {key other : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} (capture : NamedCapture headers key header mapping world)
    (same : other = key) : (capture.rekey same).embedding = capture.embedding := by cases same; rfl

theorem NamedCapture.rekey_captured {key other : Key compiled program} {header : Header compiled program}
    {mapping : LocationMap} {world : StoreTyping} (capture : NamedCapture headers key header mapping world)
    (same : other = key) : (capture.rekey same).captured = capture.captured := by cases same; rfl

theorem Represents.map_keys {keys futureKeys : List (Key compiled program)}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {native : Value} {type : Ty}
    (embedding : KeyEmbedding keys futureKeys)
    (related : Represents headers keys bodyRegistry faults mapping world sourceType source native type) :
    Represents headers futureKeys bodyRegistry faults mapping world sourceType source native type := by
  cases related with
  | builtin prior => exact .builtin prior
  | @named header rawD source identity owner member sourceAt capture installed number projection descriptor typed =>
    have same := embedding.same owner
    let changed := capture.rekey same
    have installed' : NamedInstalledCode changed := by
      simpa only [NamedInstalledCode, changed, NamedCapture.rekey_embedding] using installed
    have typed' : RuntimeValueHasType world (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) (header.code.rename changed.embedding.lift) changed.captured)
        header.named.signature.functionType compiled.indexed.layouts.definitions := by
      simpa only [changed, NamedCapture.rekey_embedding, NamedCapture.rekey_captured] using typed
    have built := Represents.named (registry := bodyRegistry) (faults := faults)
      (embedding.map owner) member sourceAt changed installed' number projection descriptor typed'
    simpa only [changed, NamedCapture.rekey_embedding, NamedCapture.rekey_captured] using built
  | @lambda function scope actual callerPrefix owner captured code history body origin globals referenceIndex typed =>
    have globals' : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := program) headers
        (embedding.map owner).key.locations callerPrefix scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]; exact globals
    exact .lambda (embedding.map owner) captured code history body origin globals' referenceIndex typed

theorem includes {keys futureKeys : List (Key compiled program)} (embedding : KeyEmbedding keys futureKeys)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (model headers keys bodyRegistry faults profile).Includes (model headers futureKeys bodyRegistry faults profile) :=
  fun related => Represents.map_keys embedding related

def KeyEmbedding.append (keys extra : List (Key compiled program)) : KeyEmbedding keys (keys ++ extra) where
  map owner := ⟨⟨owner.position.val, by have h := owner.position.isLt; simp only [List.length_append]; omega⟩⟩
  same owner := by simp only [OwnedKey.key, List.getElem_append_left owner.position.isLt]

/-- Inversion exposes the same owned token and source-dictionary receipt. -/
theorem Represents.named_inv {keys : List (Key compiled program)} {bodyRegistry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}
    (related : Represents headers keys bodyRegistry faults mapping world sourceType (.global source) native type) :
    ∃ owner : OwnedKey keys, ∃ header : Header compiled program, ∃ rawD,
      ∃ capture : NamedCapture headers owner.key header mapping world,
        header ∈ headers ∧ NamedSourceAt header rawD source ∧ NamedInstalledCode capture := by
  cases related with
  | builtin prior => cases prior
  | named owner member sourceAt capture installed number projection descriptor typed =>
    exact ⟨owner, _, _, capture, member, sourceAt, installed⟩

theorem Represents.closure_inv {keys : List (Key compiled program)} {bodyRegistry : SourceCoreRawMetadata.Registry}
    {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : Represents headers keys bodyRegistry faults mapping world sourceType (.closure function) native type) :
    ∃ owner : OwnedKey keys, ∃ scope actual callerPrefix,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative) (history : History code)
        (body : StaticSupport headers bodyRegistry faults code),
        ActualSourceOrigin code history body ∧
        CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := program) headers owner.key.locations callerPrefix
          scope captured.canonical owner.key.frameLocation ∧
        code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length ∧
        sourceType = FunctionValues.sourceType function ∧ native = value code captured.embedding history.native actual ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  cases related with
  | builtin prior => cases prior
  | lambda owner captured code history body origin globals referenceIndex typed =>
    exact ⟨owner, _, _, _, captured, code, history, body, origin, globals, referenceIndex, rfl, rfl, rfl⟩

/-- The call adapter can recover the complete native carrier from the same
owner and capture, without selecting a second representation witness. -/
theorem Represents.named_payload_inv {keys : List (Key compiled program)}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.GlobalFunction} {native : Value} {type : Ty}
    (related : Represents headers keys bodyRegistry faults mapping world sourceType (.global source) native type) :
    ∃ owner : OwnedKey keys, ∃ header : Header compiled program, ∃ rawD identity,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
          (.named header.named.signature.key),
        header ∈ headers ∧ NamedSourceAt header rawD source ∧ NamedInstalledCode capture ∧
        Word.ofNat? (header.slot + 1) = some identity ∧
        compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
          (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
        RuntimeValueHasType world (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)
          header.named.signature.functionType compiled.indexed.layouts.definitions ∧
        sourceType = header.named.specialized.function.type ∧
        native = .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id) ∧
        type = CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType := by
  cases related with
  | builtin prior => cases prior
  | named owner member sourceAt capture installed number projection descriptor typed =>
    exact ⟨owner, _, _, _, capture, descriptor, member, sourceAt, installed, number,
      projection, typed, rfl, rfl, rfl⟩

section Producers
variable {keys : List (Key compiled program)} {bodyRegistry : SourceCoreRawMetadata.Registry}
  {faults : FunctionCalls.FaultRep} {mapping : LocationMap} {world : StoreTyping}
  {header : Header compiled program} {heap : Dynamic.Heap} {store : Store}

theorem NamedInstalledCode.of_cached {key : Key compiled program}
    (capture : NamedCapture headers key header mapping world)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot) :
    NamedInstalledCode capture := by
  refine ⟨_, cached, ?_⟩
  change SourceCoreLambdaTemplates.installedTemplate header.slot _ = _
  rw [RecursiveGlobalInitializationMeaning.installed_template]
  simp only [RecursiveGlobalInitializationMeaning.shifted, Expr.rename, embedding]

/-- The original bootstrap read identifies the entire installed closure.
The arbitrary capture embedding is not treated as installed-code evidence. -/
theorem NamedInstalledCode.of_bootstrap {key : Key compiled program}
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers key.locations key.capturePrefix key.frameLocation header mapping world heap
      (RecursiveNamedCatalogPreparedInitialization.store compiled))
    (location : key.locations header = RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)) :
    NamedInstalledCode (NamedCapture.of_capture capture) := by
  obtain ⟨row, _, same, originalRead⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached
  cases row with
  | mk parameter result body =>
    change Expr.lambda _ _ _ = Expr.lambda parameter result body at same
    cases same
    have actualRead := capture.read
    rw [location] at actualRead
    have payload := Option.some.inj (actualRead.symm.trans originalRead)
    have bodyEq := congrArg (fun v : Value => match v with
      | .inRight _ (.closure _ _ code _) => code
      | _ => Expr.unit) payload
    change header.code.rename capture.embedding.lift =
      header.code.rename (RecursiveGlobalInitializationMeaning.shift header.slot).lift at bodyEq
    refine ⟨_, cached, ?_⟩
    change SourceCoreLambdaTemplates.installedTemplate header.slot _ = _
    rw [RecursiveGlobalInitializationMeaning.installed_template]
    simpa only [RecursiveGlobalInitializationMeaning.shifted, Expr.rename, NamedCapture.of_capture] using congrArg
      (Expr.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)) bodyEq.symm

/-- Decorated named reads use the actual location and complete closure payload.
The source receipt and installed-code receipt are independent static inputs. -/
theorem named_of_read {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    {identity internalReason : Word} {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
    {canonical actual : Environment} {xi : Renaming}
    (owner : OwnedKey keys) (member : header ∈ headers)
    (entry : RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix callerPrefix scope mapping world heap store canonical)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation header mapping world heap store)
    (agrees : EnvironmentsAgree xi canonical actual) (sourceAt : NamedSourceAt header rawD source)
    (installed : NamedInstalledCode (NamedCapture.of_capture capture))
    (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table (.named header.named.signature.key))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions) :
    let carrier := .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
    let expression := LanguageResult.bind (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (SourceCoreFunctions.namedReference header.named.signature (xi (scope.length + callerPrefix + header.slot)) identity internalReason)
      (LanguageResult.success (descriptor.wrap (.var 0)))
    Evaluates actual store expression (.inRight .word carrier) store ∧
    Represents headers keys bodyRegistry faults mapping world header.named.specialized.function.type (.global source) carrier
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    (∀ result finalStore, Evaluates actual store expression result finalStore → result = .inRight .word carrier ∧ finalStore = store) := by
  dsimp only
  have evaluation := NamedCalls.native_reference (identity := identity) (internalReason := internalReason)
    descriptor (entry.reindex agrees header member) capture.read
  exact ⟨evaluation, .named owner member sourceAt (NamedCapture.of_capture capture) installed number projection descriptor typed,
    fun _ _ completed => Core.evaluation_deterministic completed evaluation⟩

/-- Literal formation reuses its registered lexical key; no physical frame or
new key is created. The value copies its captured cells, and the copies keep
the catalog slots and the frame cell. -/
theorem lambda_of_formation {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {actual : Environment} {callerPrefix : Nat}
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : StaticSupport headers bodyRegistry faults code) (origin : ActualSourceOrigin code history body)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program) headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (_ghost : (pool.rows owner.position).authority.ghost = history.ghost)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
        code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      Represents headers keys bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
          finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]; exact globals.reference
  have read : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (pool.rows owner.position).authority.frame.read
    rw [(pool.rows owner.position).frame_eq, current] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history copied referenceIndex heaps reference read
  obtain ⟨sourceTrace, nativeTrace, strong⟩ := CallableIndexedLambdaRuntimeValues.formation_with
    (values := .initial compiled.compatible.checked) (program := program) compiled.indexed
    (P := fun _ _ _ _ => True) formed (body.recapture formed.captured) True.intro profile heaps.runtime_hasTypes
    ordinary coercions
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType (registry := bodyRegistry)
    (CallableIndexedLambdaRuntimeValues.RepresentsWith.forget (values := .initial compiled.compatible.checked) compiled.indexed strong)
  exact ⟨formed, sourceTrace, nativeTrace,
    .lambda (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (body.recapture formed.captured) (origin.recapture formed.captured) (globals.of_slots formed.slots)
      referenceIndex typed,
    fun _ _ completed => Core.evaluation_deterministic completed nativeTrace⟩

/-- This accepted-policy branch is explicitly ordinary (empty source evidence).
Qualified references use the full-dictionary read producer above; no weak model
is converted into the owned model. -/
theorem named_of_accepted_ordinary
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {metadata : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {identity : Word}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {actual : Environment}
    (owner : OwnedKey keys) (member : header ∈ headers)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation header mapping world heap store)
    (sourceAt : NamedSourceAt header [] ⟨metadata, []⟩)
    (installed : NamedInstalledCode (NamedCapture.of_capture capture))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions)
    (owned : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (readNode : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration metadata))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node metadata true =
      .ok (header.slot, header.named.signature))
    (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some compiled.indexed.ancestry.graph.inputs.callable) active)
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table (.named header.named.signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) = .ok descriptor)
    (coercions : node.coercions = []) (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context metadata)
    (globalReference : actual[scope.length + compilation.administrativePrefix + header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header))) :
    let carrier := .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨metadata, []⟩) heap ∧
    Evaluates actual store lowered.expression (.inRight .word carrier) store ∧
    Represents headers keys bodyRegistry faults mapping world metadata.type (.global ⟨metadata, []⟩) carrier
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    (∀ result finalStore, Evaluates actual store lowered.expression result finalStore → result = .inRight .word carrier ∧ finalStore = store) := by
  dsimp only
  obtain ⟨_, _, matched, assumptions, _⟩ := CallableNamedMetadata.metadata_of_selected_signature selection
  have noPredicates : metadata.predicates = [] := matched.predicates.symm.trans assumptions
  have traces := NamedCalls.accepted_named_reference (program := program) (evidence := evidence)
    (sourceEnvironment := sourceEnvironment) (heap := heap) compiled.indexed.ancestry.graph.inputs.callable active
    owned found readNode form special accepted selection number callables descriptor descriptorAccepted
    coercions requirements valid (by rw [noPredicates]; exact .nil) globalReference capture.read
  have sameType : metadata.type = header.named.specialized.function.type :=
    congrArg (fun global => global.instantiation.type) sourceAt.retained
  refine ⟨traces.2.2.1, traces.2.2.2.1, ?_, traces.2.2.2.2⟩
  rw [sameType]
  exact .named owner member sourceAt (NamedCapture.of_capture capture) installed number projection descriptor typed

/-- Concrete nested receipts establish the source origin for the exact
recaptured Code and History. Their full dictionary is unchanged. -/
theorem ActualSourceOrigin.of_nested
    {caller : Header compiled program} {rank : Nat} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {locations : RecursiveNamedCatalog.Locations (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := program)} {canonical : Environment}
    (head : CallableIndexedLambdaNestedRuntimeBodyMeaning.LambdaAt
      (values := .initial compiled.compatible.checked) headers caller bodyRegistry faults rank source context evidence scope id lowered)
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked)
      caller headers locations 0 1 scope mapping world heap store canonical)
    (environment : Dynamic.Environment) :
    ActualSourceOrigin (CallableIndexedLambdaNestedRuntimeBodyMeaning.actualCode head environment)
      (CallableIndexedLambdaNestedRuntimeBodyMeaning.historyAt head entry environment)
      (CallableIndexedLambdaNestedRuntimeBodyMeaning.actualSupport head environment) :=
  ActualSourceOrigin.of_support _ _ rfl

end Producers

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries
/-! Owned function values use actual selected pool rows as call-time catalogue
authority. Parameter prefixes retain all rows, complete captures and records.
Restoration installs the saved current into the reached pool, retaining records
accumulated in the body. No callable-body execution law is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog CallableIndexedAuthorityPool

section PoolAdapters

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {keys : List (Key prepared values ambient.definitions program)}
  {mapping futureMap finalMap : LocationMap} {world futureWorld finalWorld : StoreTyping}
  {heap after finalHeap : Dynamic.Heap} {store futureStore finalStore : Store}

/-- The immutable key position selects a live authority in this reached store. -/
def reached_authority (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    Authority headers keys[selected.val].locations keys[selected.val].capturePrefix
      mapping world heap store :=
  (pool.rows selected).authority

theorem reached_frame_eq (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    (reached_authority pool selected).frameLocation = keys[selected.val].frameLocation :=
  (pool.rows selected).frame_eq

theorem reached_frame_read (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) :
    store.read? keys[selected.val].frameLocation =
      some (encode prepared.layout.frame (pool.rows selected).authority.current) := by
  simpa only [(pool.rows selected).frame_eq] using (pool.rows selected).authority.frame.read

/-- Body records remain in the corresponding row; membership need not be
unique and the key domain is neither sorted nor deduplicated. -/
def RecordsExtend (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore) : Prop :=
  ∀ (i : Fin keys.length) record,
    record ∈ (saved.rows i).authority.records →
    record ∈ (reached.rows i).authority.records

theorem RecordsExtend.refl (pool : Pool headers keys mapping world heap store) :
    RecordsExtend pool pool := by
  intro i record member
  exact member

theorem RecordsExtend.trans
    {first : Pool headers keys mapping world heap store}
    {middle : Pool headers keys futureMap futureWorld after futureStore}
    {last : Pool headers keys finalMap finalWorld finalHeap finalStore}
    (left : RecordsExtend first middle) (right : RecordsExtend middle last) :
    RecordsExtend first last := by
  intro i record member
  exact right i record (left i record member)

theorem extend_records (pool : Pool headers keys mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) (i : Fin keys.length) :
    ((pool.extend maps worlds frame metadata).rows i).authority.records =
      (pool.rows i).authority.records := rfl

theorem RecordsExtend.extend (pool : Pool headers keys mapping world heap store)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    RecordsExtend pool (pool.extend maps worlds frame metadata) := by
  intro i record member
  simpa only [extend_records] using member

theorem RecordsExtend.install (pool : Pool headers keys mapping world heap store)
    (selected : Fin keys.length) {next : NativeFrame} {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecordsExtend pool (pool.install selected history) := by
  intro i record member
  simpa only [Pool.install_records] using member

/-- The saved history is reinstalled in every reached row sharing this frame.
The reached rows, including their complete body records, remain the base pool. -/
def restored_pool (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) :
    Pool headers keys futureMap futureWorld after
      (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) :=
  reached.install selected (saved.rows selected).authority.frame.history

theorem restored_records (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.records =
      (reached.rows i).authority.records :=
  Pool.install_records reached selected i (saved.rows selected).authority.frame.history

theorem RecordsExtend.restored
    (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) (retained : RecordsExtend saved reached) :
    RecordsExtend saved (restored_pool saved reached selected) := by
  intro i record member
  simpa only [restored_records] using retained i record member

theorem restored_current (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.current =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation
      then (saved.rows selected).authority.current else (reached.rows i).authority.current :=
  Pool.install_current reached selected i (saved.rows selected).authority.frame.history

theorem restored_ghost (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) :
    ((restored_pool saved reached selected).rows i).authority.ghost =
      if keys[i.val].frameLocation = keys[selected.val].frameLocation
      then (saved.rows selected).authority.ghost else (reached.rows i).authority.ghost :=
  Pool.install_ghost reached selected i (saved.rows selected).authority.frame.history

theorem restored_selected (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) :
    ((restored_pool saved reached selected).rows selected).authority.current =
      (saved.rows selected).authority.current ∧
    ((restored_pool saved reached selected).rows selected).authority.ghost =
      (saved.rows selected).authority.ghost := by
  constructor
  · simpa using restored_current saved reached selected selected
  · simpa using restored_ghost saved reached selected selected

theorem restored_same_frame (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length)
    (same : keys[i.val].frameLocation = keys[selected.val].frameLocation) :
    ((restored_pool saved reached selected).rows i).authority.current =
      (saved.rows selected).authority.current ∧
    ((restored_pool saved reached selected).rows i).authority.ghost =
      (saved.rows selected).authority.ghost := by
  constructor
  · simpa only [if_pos same] using restored_current saved reached selected i
  · simpa only [if_pos same] using restored_ghost saved reached selected i

theorem restored_other_frame (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length)
    (different : keys[i.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((restored_pool saved reached selected).rows i).authority.current =
      (reached.rows i).authority.current ∧
    ((restored_pool saved reached selected).rows i).authority.ghost =
      (reached.rows i).authority.ghost := by
  constructor
  · simpa only [if_neg different] using restored_current saved reached selected i
  · simpa only [if_neg different] using restored_ghost saved reached selected i

/-- Every reached record retains its actual snapshot read, administrative
separation and carried metadata after restoration. -/
theorem restored_snapshot (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ (reached.rows i).authority.records) :
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame
      futureMap (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) record := by
  apply ((restored_pool saved reached selected).rows i).authority.snapshots record
  simpa only [restored_records] using member

theorem restored_registered (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) {record : CallableIndexedSnapshots.Record} :
    (restored_pool saved reached selected).Registered record ↔ reached.Registered record := by
  constructor
  · rintro ⟨i, member⟩
    exact ⟨i, by simpa only [restored_records] using member⟩
  · rintro ⟨i, member⟩
    exact ⟨i, by simpa only [restored_records] using member⟩

/-- The complete original capture, including any unused suffix, survives the
write at the selected frame. Different key location functions are permitted. -/
theorem restored_capture_read (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected i : Fin keys.length) {header : Header prepared values ambient.definitions program}
    (member : header ∈ headers)
    (capture : Capture headers keys[i.val].locations keys[i.val].capturePrefix
      (reached.rows i).authority.frameLocation header futureMap futureWorld after futureStore) :
    Store.read?
      (futureStore.set keys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current))
      (keys[i.val].locations header) =
      some (.inRight .unit (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  Pool.install_capture_read reached selected i member capture

/-- Restore the actual saved cell once, then retain the reached pool by
installing the saved current/history into that pool. The returned cell uses
the key's physical location explicitly; no caller/callee frame equality is
introduced. All reached record lists and full capture reads are retained. -/
theorem restore_reached_pool
    (saved : Pool headers keys mapping world heap store)
    (reached : Pool headers keys futureMap futureWorld after futureStore)
    (selected : Fin keys.length) {next : NativeFrame}
    {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions
      futureMap futureWorld after futureStore)
    (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next))
      futureMap futureStore) :
    ∃ finalPool : Pool headers keys futureMap futureWorld after
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)),
      finalPool = restored_pool saved reached selected ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions
        futureMap futureWorld after
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      AdministrativePreserved mapping store futureMap
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame
        keys[selected.val].frameLocation (saved.rows selected).authority.current
        (saved.rows selected).authority.ghost
        (futureStore.set keys[selected.val].frameLocation
          (encode prepared.layout.frame (saved.rows selected).authority.current)) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.records = (reached.rows i).authority.records) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.current =
          if keys[i.val].frameLocation = keys[selected.val].frameLocation
          then (saved.rows selected).authority.current else (reached.rows i).authority.current) ∧
      (∀ i : Fin keys.length,
        (finalPool.rows i).authority.ghost =
          if keys[i.val].frameLocation = keys[selected.val].frameLocation
          then (saved.rows selected).authority.ghost else (reached.rows i).authority.ghost) ∧
      (∀ (i : Fin keys.length) (header : Header prepared values ambient.definitions program),
        header ∈ headers →
        ∀ capture : Capture headers keys[i.val].locations keys[i.val].capturePrefix
          (reached.rows i).authority.frameLocation header futureMap futureWorld after futureStore,
        Store.read?
          (futureStore.set keys[selected.val].frameLocation
            (encode prepared.layout.frame (saved.rows selected).authority.current))
          (keys[i.val].locations header) =
          some (.inRight .unit (.closure header.named.signature.parameterType
            (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured))) := by
  let row := saved.rows selected
  obtain ⟨finalHeaps, restored, cell⟩ :=
    CallableIndexedBodyFrames.restore registered row.authority.unmapped row.authority.typed
      row.authority.frame heaps worlds (by simpa only [row.frame_eq] using frame)
  rw [row.frame_eq] at finalHeaps restored cell
  refine ⟨restored_pool saved reached selected, rfl, finalHeaps, restored, cell, ?_, ?_, ?_, ?_⟩
  · exact fun i => restored_records saved reached selected i
  · exact fun i => restored_current saved reached selected i
  · exact fun i => restored_ghost saved reached selected i
  · exact fun i header member capture => restored_capture_read saved reached selected i member capture

end PoolAdapters

open CallableIndexedOwnedFunctionValues (OwnedKey NamedCapture)

/-- The fixed owned-key domain uses the same prepared compilation and full
initial values context as the owned function relation. -/
abbrev OwnedPool {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) :=
  Pool (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers keys mapping world heap store

section OwnedCaptures

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- The immutable owner selects an actual full capture in this reached pool.
Its physical frame is transported through the row's explicit equality. -/
theorem capture_from_pool (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) :
    Nonempty (Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation
      header mapping world heap store) := by
  obtain ⟨capture⟩ := (pool.rows owner.position).authority.captures header member
  have same := (pool.rows owner.position).frame_eq
  change (pool.rows owner.position).authority.frameLocation = owner.key.frameLocation at same
  rw [same] at capture
  exact ⟨capture⟩

/-- Store-independent named evidence becomes a live capture only with the
exact closure read. Local agreement and administrative separation are taken
from the actual same-header row, retaining all captured values. -/
def named_capture_reached (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation
      header mapping world heap store := by
  have live : Dynamic.EnvironmentAgrees heap header.function.context.locals [] ∧
      owner.key.locations header ∉ mapping ∧ owner.key.locations header ≠ owner.key.frameLocation := by
    obtain ⟨original⟩ := capture_from_pool pool owner member
    exact ⟨original.locals, original.unmapped, original.distinct⟩
  exact {
    administrative := capture.administrative
    canonical := capture.canonical
    captured := capture.captured
    capturedContext := capture.capturedContext
    embedding := capture.embedding
    environments := capture.environments
    locals := live.1
    layout := capture.layout
    typed := capture.typed
    reference := capture.reference
    capturedReference := capture.capturedReference
    coherent := capture.coherent
    unmapped := live.2.1
    distinct := live.2.2
    read := read }

theorem named_capture_reached_embedding
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    (named_capture_reached pool owner member capture read).embedding = capture.embedding := by
  unfold named_capture_reached
  rfl

theorem named_capture_reached_captured
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (read : store.read? (owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured))) :
    (named_capture_reached pool owner member capture read).captured = capture.captured := by
  unfold named_capture_reached
  rfl

variable {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}

/-- Actual canonical global/frame observations select the same owner row.
The key's complete capture prefix is retained without requiring an empty
catalogue or equality to another caller's physical frame. -/
def initial_catalog (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope canonical owner.key.frameLocation) :
    RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix callerPrefix scope
      mapping world heap store canonical :=
  globals.catalog (pool.rows owner.position).authority

theorem initial_catalog_frame_eq (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope canonical owner.key.frameLocation) :
    (initial_catalog pool owner globals).authority.frameLocation = owner.key.frameLocation :=
  (pool.rows owner.position).frame_eq

end OwnedCaptures

section NamedParameters

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {payloads : List Value}
  {actual : Environment} {actualContext : Core.Context} {xi : Renaming}

/-- Named parameter allocation uses the represented value's original full
canonical layout. Independent live authority supplies only its actual frame
and source local agreement; no different catalogue payload is substituted. -/
theorem named_parameters (pool : OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
      registry functions mapping world heap store)
    (agrees : EnvironmentsAgree xi (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions) :
    Nonempty (RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi owner.key.frameLocation
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost) := by
  have locals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := capture_from_pool pool owner member
    exact original.locals
  have physical : (pool.rows owner.position).authority.frameLocation = owner.key.frameLocation :=
    (pool.rows owner.position).frame_eq
  have reference : capture.canonical[header.globals]? = some
      (.cellRef compiled.indexed.ancestry.layout.frame.type (pool.rows owner.position).authority.frameLocation) := by
    exact capture.reference.trans (congrArg
      (fun location => some (Value.cellRef compiled.indexed.ancestry.layout.frame.type location)) physical.symm)
  have produced := RecursiveNamedCatalog.parameters_of_layout (pool.rows owner.position).authority
    capture.environments locals reference capture.coherent represented heaps agrees actualTyped
  exact Eq.mp (congrArg (fun location =>
    Nonempty (RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi location
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)) physical) produced

variable (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (capture : NamedCapture headers owner.key header mapping world)
  (entry : RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
    capture.administrative actualContext actual xi owner.key.frameLocation
    (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)

/-- The actual parameter prefix transports every pool row and its complete
records through its certified maps, worlds, frame and source metadata. -/
def named_parameter_pool : OwnedPool headers keys entry.mapping entry.world entry.heap entry.store :=
  pool.extend entry.maps entry.worlds entry.frame entry.metadata

theorem named_parameter_pool_records (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.records =
      (pool.rows i).authority.records := rfl

theorem named_parameter_pool_current (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.current =
      (pool.rows i).authority.current := rfl

theorem named_parameter_pool_ghost (i : Fin keys.length) :
    ((named_parameter_pool pool owner capture entry).rows i).authority.ghost =
      (pool.rows i).authority.ghost := rfl

theorem named_parameter_catalog_current :
    entry.catalog.authority.current =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.current :=
  entry.catalog_current

theorem named_parameter_catalog_ghost :
    entry.catalog.authority.ghost =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.ghost :=
  entry.catalog_ghost

theorem named_parameter_catalog_frame_eq :
    entry.catalog.authority.frameLocation = owner.key.frameLocation :=
  entry.catalog_frame

/-- The actual prefix's observed global slots can be paired with the selected
reached pool authority. This entry retains the pool's exact records rather
than asserting equality for an arbitrary ParameterEntry's catalogue. -/
def named_parameter_catalog :
    RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix (owner.key.capturePrefix + 1)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical :=
  ⟨((named_parameter_pool pool owner capture entry).rows owner.position).authority, entry.catalog.globals⟩

theorem named_parameter_catalog_records :
    (named_parameter_catalog pool owner capture entry).authority.records =
      ((named_parameter_pool pool owner capture entry).rows owner.position).authority.records := rfl

theorem named_parameter_catalog_owner_frame :
    (named_parameter_catalog pool owner capture entry).authority.frameLocation = owner.key.frameLocation :=
  ((named_parameter_pool pool owner capture entry).rows owner.position).frame_eq

end NamedParameters

section OrdinaryPrefix

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured capturedActual}
  {code : CallableIndexedLambdaValues.Code compiled.indexed function scope captured.administrative}
  {history : CallableIndexedLambdaValues.History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments nativeArguments heap store owner.key.frameLocation
    (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost)

/-- The actual ordinary prefix installs its stable lambda history in all
rows sharing the physical frame, then transports the complete pool through
its real allocation effects. The function model remains arbitrary. -/
def ordinary_pool : OwnedPool headers keys entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store :=
  (pool.install owner.position (Current.stable entry.nextHistory)).extend
    entry.entry.maps entry.entry.worlds entry.entry.frame entry.entry.metadata

theorem ordinary_pool_records (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.records = (pool.rows i).authority.records :=
  Pool.install_records pool owner.position i (Current.stable entry.nextHistory)

theorem ordinary_pool_current (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.current =
      if keys[i.val].frameLocation = owner.key.frameLocation then entry.next
      else (pool.rows i).authority.current :=
  Pool.install_current pool owner.position i (Current.stable entry.nextHistory)

theorem ordinary_pool_ghost (i : Fin keys.length) :
    ((ordinary_pool pool owner entry).rows i).authority.ghost =
      if keys[i.val].frameLocation = owner.key.frameLocation then .lambda code.descriptor.id history.ghost
      else (pool.rows i).authority.ghost :=
  Pool.install_ghost pool owner.position i (Current.stable entry.nextHistory)

variable {callerPrefix : Nat}
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
  {added copied : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ copied)
  (slots : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)

/-- The source entry comes from the same unsized prefix and its retained
ordered spine. The lambda ghost and full carried metadata are unchanged. -/
def ordinary_source_entry :
    CallableIndexedLambdaCatalogEntries.SourceEntry (values := .initial compiled.compatible.checked)
      code history headers owner.key.locations owner.key.capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  CallableIndexedLambdaCatalogEntries.source_entry entry (initial_catalog pool owner globals)
    (initial_catalog_frame_eq pool owner globals) length spine slots

theorem ordinary_source_entry_frame_eq :
    (ordinary_source_entry pool owner entry globals length spine slots).catalog.authority.frameLocation =
      owner.key.frameLocation :=
  initial_catalog_frame_eq pool owner globals

/-- The selected source-entry row and the transported pool retain the exact
same record list. This comparison concerns authority data, not proof terms. -/
theorem ordinary_source_entry_records :
    (ordinary_source_entry pool owner entry globals length spine slots).catalog.authority.records =
      ((ordinary_pool pool owner entry).rows owner.position).authority.records :=
  (ordinary_pool_records pool owner entry owner.position).symm

theorem ordinary_source_entry_current :
    (ordinary_source_entry pool owner entry globals length spine slots).catalog.authority.current =
      ((ordinary_pool pool owner entry).rows owner.position).authority.current := by
  change entry.next = ((ordinary_pool pool owner entry).rows owner.position).authority.current
  have same := ordinary_pool_current pool owner entry owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

theorem ordinary_source_entry_ghost :
    (ordinary_source_entry pool owner entry globals length spine slots).catalog.authority.ghost =
      ((ordinary_pool pool owner entry).rows owner.position).authority.ghost := by
  change (SourceCoreCallablePairedFrames.Frame.lambda code.descriptor.id history.ghost) =
    ((ordinary_pool pool owner entry).rows owner.position).authority.ghost
  have same := ordinary_pool_ghost pool owner entry owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

end OrdinaryPrefix

section OrdinarySizedPrefix

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {capturedActual : Environment}
  {captured : CallableIndexedLambdaValues.Captures compiled.indexed mapping world scope function.captured capturedActual}
  {code : CallableIndexedLambdaValues.Code compiled.indexed function scope captured.administrative}
  {history : CallableIndexedLambdaValues.History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
  (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
    captured code history inputs functions registry arguments heap store owner.key.frameLocation
    (pool.rows owner.position).authority.current)

/-- Reflection uses the actual sized prefix's effects and history. Original
Core body grades remain in that prefix and are not manufactured here. -/
def ordinary_pool_sized : OwnedPool headers keys reached.mapping reached.world reached.heap reached.store :=
  (pool.install owner.position (Current.stable reached.nextHistory)).extend
    reached.maps reached.worlds reached.frame reached.metadata

theorem ordinary_pool_sized_records (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.records = (pool.rows i).authority.records :=
  Pool.install_records pool owner.position i (Current.stable reached.nextHistory)

theorem ordinary_pool_sized_current (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.current =
      if keys[i.val].frameLocation = owner.key.frameLocation then reached.next
      else (pool.rows i).authority.current :=
  Pool.install_current pool owner.position i (Current.stable reached.nextHistory)

theorem ordinary_pool_sized_ghost (i : Fin keys.length) :
    ((ordinary_pool_sized pool owner reached).rows i).authority.ghost =
      if keys[i.val].frameLocation = owner.key.frameLocation then .lambda code.descriptor.id history.ghost
      else (pool.rows i).authority.ghost :=
  Pool.install_ghost pool owner.position i (Current.stable reached.nextHistory)

variable {callerPrefix : Nat}
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)

def ordinary_source_entry_sized :
    CallableIndexedLambdaCatalogEntries.SourceEntry (values := .initial compiled.compatible.checked)
      code history headers owner.key.locations owner.key.capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      reached.mapping reached.world reached.heap reached.store reached.canonical :=
  CallableIndexedLambdaCatalogEntries.source_entry_sized reached (initial_catalog pool owner globals)
    (initial_catalog_frame_eq pool owner globals)

theorem ordinary_source_entry_sized_frame_eq :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.frameLocation =
      owner.key.frameLocation :=
  initial_catalog_frame_eq pool owner globals

theorem ordinary_source_entry_sized_records :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.records =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records :=
  (ordinary_pool_sized_records pool owner reached owner.position).symm

theorem ordinary_source_entry_sized_current :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.current =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.current := by
  change reached.next = ((ordinary_pool_sized pool owner reached).rows owner.position).authority.current
  have same := ordinary_pool_sized_current pool owner reached owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

theorem ordinary_source_entry_sized_ghost :
    (ordinary_source_entry_sized pool owner reached globals).catalog.authority.ghost =
      ((ordinary_pool_sized pool owner reached).rows owner.position).authority.ghost := by
  change (SourceCoreCallablePairedFrames.Frame.lambda code.descriptor.id history.ghost) =
    ((ordinary_pool_sized pool owner reached).rows owner.position).authority.ghost
  have same := ordinary_pool_sized_ghost pool owner reached owner.position
  simpa [CallableIndexedOwnedFunctionValues.OwnedKey.key] using same.symm

end OrdinarySizedPrefix

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
/-! Actual owned pools provide protected state witnesses. The observation is
the complete ordered record list in every ordered key row. Related witnesses
append to each row, preserving its original order and multiplicity. Actual
allocation produces records; administrative transport and frame restoration
retain the reached lists exactly. No body execution law is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedAuthorityPool CallableIndexedOwnedFunctionEntries

abbrev Records {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :=
  Fin keys.length → List CallableIndexedSnapshots.Record

abbrev State {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (index : ProtectedStateTransition.Index) :=
  OwnedPool headers keys index.mapping index.world index.heap index.store

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def records {index : ProtectedStateTransition.Index} (state : State headers keys index) : Records keys :=
  fun i => (state.rows i).authority.records

/-- Prefix equality retains every original position, including duplicates. -/
def RecordPrefix (initial reached : List CallableIndexedSnapshots.Record) : Prop :=
  ∃ suffix, reached = initial ++ suffix

theorem RecordPrefix.refl (items : List CallableIndexedSnapshots.Record) : RecordPrefix items items :=
  ⟨[], (List.append_nil items).symm⟩

theorem RecordPrefix.trans {initial middle reached : List CallableIndexedSnapshots.Record}
    (left : RecordPrefix initial middle) (right : RecordPrefix middle reached) :
    RecordPrefix initial reached := by
  obtain ⟨first, firstEq⟩ := left
  obtain ⟨last, lastEq⟩ := right
  exact ⟨first ++ last, by rw [lastEq, firstEq, List.append_assoc]⟩

theorem RecordPrefix.mem {initial reached : List CallableIndexedSnapshots.Record}
    (retained : RecordPrefix initial reached) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ initial) : record ∈ reached := by
  obtain ⟨suffix, same⟩ := retained
  rw [same]
  exact List.mem_append_left suffix member

def Relates {initial reached : ProtectedStateTransition.Index}
    (before : State headers keys initial) (after : State headers keys reached) : Prop :=
  ∀ i : Fin keys.length, RecordPrefix (records before i) (records after i)

theorem Relates.refl {index : ProtectedStateTransition.Index} (state : State headers keys index) :
    Relates state state :=
  fun i => RecordPrefix.refl (records state i)

theorem Relates.trans {initial middle reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {during : State headers keys middle} {after : State headers keys reached}
    (first : Relates before during) (last : Relates during after) : Relates before after :=
  fun i => RecordPrefix.trans (first i) (last i)

theorem Relates.of_records_eq {initial reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {after : State headers keys reached}
    (same : records after = records before) : Relates before after := by
  intro i
  rw [same]
  exact RecordPrefix.refl (records before i)

theorem Relates.mem {initial reached : ProtectedStateTransition.Index}
    {before : State headers keys initial} {after : State headers keys reached}
    (related : Relates before after) (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records before i) : record ∈ records after i :=
  RecordPrefix.mem (related i) member

def protocol (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Protocol (Records keys) where
  State := State headers keys
  records := records
  Relates := Relates
  refl := Relates.refl
  trans := Relates.trans

/-- Ordinary administrative effects keep the exact observation, including
the order and multiplicity of all rows and their full record lists. -/
def administrativeTransport (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.AdministrativeTransport (protocol headers keys) where
  extend := fun {_initial} state {_mapping _world _heap _store} maps worlds frame metadata =>
    state.extend maps worlds frame metadata
  related := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata =>
    Relates.of_records_eq rfl
  records_eq := fun {_initial} _state {_mapping _world _heap _store} _maps _worlds _frame _metadata => rfl

/-- The pool does not observe the canonical environment, so rebinding the
scope's slots to a closure's copies keeps it exactly. -/
theorem rebinds (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Rebinds (protocol headers keys) :=
  fun state _canonical _slots => ⟨state, Relates.refl state⟩

theorem administrative_records {index : ProtectedStateTransition.Index} (state : State headers keys index)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (maps : LocationMap.Extends index.mapping mapping) (worlds : WorldExtends index.world world)
    (frame : AdministrativePreserved index.mapping index.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend index.heap heap) :
    records ((administrativeTransport headers keys).extend state maps worlds frame metadata) = records state := rfl

theorem record_snapshot {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record} (member : record ∈ records state i) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame index.mapping index.store record :=
  (state.rows i).authority.snapshots record member

theorem record_location_lt {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record} (member : record ∈ records state i) :
    record.location < index.store.length :=
  (List.getElem?_eq_some_iff.mp (record_snapshot state i member).read).1

theorem fresh_record_absent {index : ProtectedStateTransition.Index} (state : State headers keys index)
    (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (fresh : record.location = index.store.length) : record ∉ records state i := by
  intro member
  have bound := record_location_lt state i member
  rw [fresh] at bound
  exact Nat.lt_irrefl _ bound

section Allocation
variable {index : ProtectedStateTransition.Index} (state : State headers keys index) (selected : Fin keys.length)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {globals : Nat}
  {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  {environment : Environment} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
  {metadata : Option MetadataState} {payload : Option Value}
  (reference : environment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
  (read : index.store.read? location = some (encode compiled.indexed.ancestry.layout.frame native))
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
  (bounded : ∀ target ∈ index.mapping, target < index.store.length)
  (slots : ∀ position binding, request.scope[position]? = some binding → ∃ target,
    environment[request.references position]? = some (.cellRef (OptionalCell.cellType binding.2) target))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request environment payload)
  {world : StoreTyping} {heap : Dynamic.Heap}
  (worlds : WorldExtends index.world world) (sourceMetadata : Dynamic.HeapMetadataExtend index.heap heap)

include same reference read history bounded slots payloadAt worlds sourceMetadata

/-- The actual three-cell evaluation adds one snapshot to the selected row.
All other rows keep their complete lists; the returned pool is the actual
post-witness used by subsequent transitions. -/
theorem completed_snapshot :
    ∃ captured,
      Evaluates environment index.store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (index.store.length + 2))
        (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys (index.extend (index.mapping ++ [index.store.length + 2]) world heap
          (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])),
        Relates state final ∧
        records final selected = records state selected ++ [⟨index.store.length, native, ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records state i) ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame (index.mapping ++ [index.store.length + 2])
          (index.store ++ [encode compiled.indexed.ancestry.layout.frame native,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])
          ⟨index.store.length, native, ghost, metadata⟩ := by
  obtain ⟨captured, evaluated, final, appended, unchanged⟩ := state.completed_snapshot selected
    allocation annotation same reference read history bounded slots payloadAt worlds sourceMetadata
  refine ⟨captured, evaluated, final, ?_, appended, unchanged, ?_⟩
  · intro i
    by_cases selectedRow : i = selected
    · subst i
      exact ⟨[⟨index.store.length, native, ghost, metadata⟩], appended⟩
    · exact ⟨[], by simpa only [records, List.append_nil] using unchanged i selectedRow⟩
  · apply (final.rows selected).authority.snapshots
    rw [appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)

end Allocation

section FrameUpdates
variable {index : ProtectedStateTransition.Index} (state : State headers keys index) (selected : Fin keys.length)
  {next : NativeFrame} {nextGhost : GhostFrame}
  (history : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost)

include history

def install : State headers keys (index.extend index.mapping index.world index.heap
    (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))) :=
  state.install selected history

theorem install_records : records (install state selected history) = records state := by
  funext i
  exact Pool.install_records state selected i history

theorem install_related : Relates state (install state selected history) :=
  Relates.of_records_eq (install_records state selected history)

theorem install_transition : ProtectedStateTransition.Transition (protocol headers keys) state
    (index.extend index.mapping index.world index.heap
      (index.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))) :=
  ⟨install state selected history, install_related state selected history⟩

end FrameUpdates

section Restoration
variable {initial reached : ProtectedStateTransition.Index}
  (saved : State headers keys initial) (after : State headers keys reached) (selected : Fin keys.length)

/-- Restoration uses the reached pool as its baseline. Any records created
between the saved and reached points remain in their exact original order. -/
def restored : State headers keys (reached.extend reached.mapping reached.world reached.heap
    (reached.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))) :=
  restored_pool saved after selected

theorem restored_records : records (restored saved after selected) = records after := by
  funext i
  exact CallableIndexedOwnedFunctionEntries.restored_records saved after selected i

theorem restored_related : Relates after (restored saved after selected) :=
  Relates.of_records_eq (restored_records saved after selected)

theorem restored_transition : ProtectedStateTransition.Transition (protocol headers keys) after
    (reached.extend reached.mapping reached.world reached.heap
      (reached.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))) :=
  ⟨restored saved after selected, restored_related saved after selected⟩

theorem restored_from_saved (retained : Relates saved after) : Relates saved (restored saved after selected) :=
  Relates.trans retained (restored_related saved after selected)

theorem restored_same_frame (i : Fin keys.length)
    (same : keys[i.val].frameLocation = keys[selected.val].frameLocation) :
    ((restored saved after selected).rows i).authority.current = (saved.rows selected).authority.current ∧
    ((restored saved after selected).rows i).authority.ghost = (saved.rows selected).authority.ghost :=
  CallableIndexedOwnedFunctionEntries.restored_same_frame saved after selected i same

theorem restored_other_frame (i : Fin keys.length)
    (different : keys[i.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((restored saved after selected).rows i).authority.current = (after.rows i).authority.current ∧
    ((restored saved after selected).rows i).authority.ghost = (after.rows i).authority.ghost :=
  CallableIndexedOwnedFunctionEntries.restored_other_frame saved after selected i different

theorem restored_snapshot (i : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records after i) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame reached.mapping
      (reached.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) record :=
  CallableIndexedOwnedFunctionEntries.restored_snapshot saved after selected i member

theorem restored_capture_read (i : Fin keys.length)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[i.val].locations keys[i.val].capturePrefix (after.rows i).authority.frameLocation
      header reached.mapping reached.world reached.heap reached.store) :
    Store.read? (reached.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))
      (keys[i.val].locations header) = some (.inRight .unit
        (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) :=
  CallableIndexedOwnedFunctionEntries.restored_capture_read saved after selected i member capture

/-- Restore the saved physical cell once through the actual completed frame,
returning the reached pool with unchanged full records and the same function
model's final heap correspondence. -/
theorem restore_reached {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      reached.mapping reached.world reached.heap reached.store)
    (worlds : WorldExtends initial.world reached.world)
    (frame : AdministrativePreserved initial.mapping
      (initial.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      reached.mapping reached.store) :
    ∃ final : State headers keys (reached.extend reached.mapping reached.world reached.heap
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current))),
      final = restored saved after selected ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        reached.mapping reached.world reached.heap
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      AdministrativePreserved initial.mapping initial.store reached.mapping
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
        (saved.rows selected).authority.current (saved.rows selected).authority.ghost
        (reached.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) ∧
      Relates after final ∧ records final = records after := by
  obtain ⟨final, finalEq, finalHeaps, preserved, cell, _, _, _, _⟩ :=
    restore_reached_pool saved after selected registered heaps worlds frame
  exact ⟨final, finalEq, finalHeaps, preserved, cell,
    by rw [finalEq]; exact restored_related saved after selected,
    by rw [finalEq]; exact restored_records saved after selected⟩

end Restoration

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
/-! Ordinary source allocation produces the actual heap correspondence and
registered catalogue post-state together. The payload alone becomes a source
binder. Its preceding snapshot is appended to the selected ordered row, and
lexical restoration retains that reached row's complete record list. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedAuthorityPool
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

/-- The pool is indexed by the actual heap and store. Canonical lexical
binders change neither its physical cells nor its ordered records. -/
def bindings (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Bindings (protocol headers keys) where
  prepend state _ _ _ := state
  prepend_related state _ _ _ := Relates.refl state
  prepend_records _ _ _ _ := rfl
  restore state := state
  restore_related state := Relates.refl state
  restore_records _ := rfl

section Allocation
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {sourceType : TypeSystem.Ty} {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope
    sourceEnvironment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree request.references canonical actual)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
  (cell : GenericHeap.CellRepresents model mapping world
    ⟨sourceType, sourceValue, none⟩
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
  (allocated : Dynamic.Heap.Allocates before sourceType sourceValue sourceLocation after)

include same registered history environments agrees heaps reference payloadAt cell allocated in
/-- One actual allocation producer supplies capture selection, execution,
source/native heap correspondence and the live pool's registered snapshot.
No evaluation, new-record separation or post-state law is assumed. -/
theorem completed_bind_for_type :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) after
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) sourceLocation (store.length + 2) request.payloadType ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, sourceLocation) :: sourceEnvironment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical)
        compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
          ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
              OptionalCell.cellType request.payloadType], after,
            store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
            .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial selected
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped, frame⟩ :=
    CallableIndexedOrdinaryAllocation.preserves_with_captures_for_type allocation annotation same rfl registered
      environments agrees heaps reference read payloadAt cell allocated
  have bound : ∀ target ∈ mapping, target < store.length := by
    intro target member
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    exact heaps.target_lt found
  let record : CallableIndexedSnapshots.Record :=
    ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
  have holds := CallableIndexedSnapshots.completed (layout := compiled.indexed.ancestry.layout.frame) history bound
    (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload)
  have separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation := by
    intro i
    have earlier := (List.getElem?_eq_some_iff.mp (initial.rows i).authority.frame.read).1
    rw [(initial.rows i).frame_eq] at earlier
    exact Nat.ne_of_gt earlier
  let extended := initial.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
      OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
    frame (Dynamic.HeapMetadataExtend.of_allocation allocated)
  let final := extended.record_snapshot selected record holds separate
  refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped,
    CallableIndexedOrdinaryAllocation.bind_environment environments mapped, frame, final, ?_, ?_, ?_⟩
  · intro i
    by_cases chosen : i = selected
    · subst i
      exact ⟨[record], Pool.record_snapshot_selected extended selected record holds separate⟩
    · refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact Pool.record_snapshot_other extended selected record holds separate i chosen
  · exact Pool.record_snapshot_selected extended selected record holds separate
  · intro i different
    exact Pool.record_snapshot_other extended selected record holds separate i different

end Allocation

section Allocation
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope
    sourceEnvironment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree request.references canonical actual)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
  (cell : GenericHeap.CellRepresents model mapping world
    ⟨request.binder.scheme.body, sourceValue, none⟩
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
  (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after)


include same registered history environments agrees heaps reference payloadAt cell allocated in
theorem completed_bind :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) after
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) sourceLocation (store.length + 2) request.payloadType ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, sourceLocation) :: sourceEnvironment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical)
        compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
          ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
              OptionalCell.cellType request.payloadType], after,
            store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
            .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) := by
  exact completed_bind_for_type allocation annotation same registered initial selected history
    environments agrees heaps reference payloadAt cell allocated

end Allocation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
/-! The generic lexical allocation interface is implemented by the actual
owned-pool producer. A readiness receipt identifies its exact ordered row,
physical frame and authenticated stable history. No capture is substituted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def Ready {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (location : Location) (native : NativeFrame) : Prop :=
  ∃ selected : Fin keys.length, ∃ metadata,
    keys[selected.val].frameLocation = location ∧
    (initial.rows selected).authority.current = native ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata

theorem ready_selected {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (selected : Fin keys.length) {metadata : Option MetadataState}
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata) :
    Ready initial keys[selected.val].frameLocation (initial.rows selected).authority.current :=
  ⟨selected, metadata, rfl, rfl, history⟩

private theorem current_history_of_stable {native : NativeFrame} {savedGhost reachedGhost : GhostFrame}
    {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native savedGhost metadata)
    (current : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native reachedGhost) :
    ∃ reachedMetadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native reachedGhost reachedMetadata := by
  cases stable with
  | empty => cases current with | stable carried => exact ⟨_, carried⟩
  | state stored history => cases current with | stable carried => exact ⟨_, carried⟩

/-- A retained stable frame read rules out a transient read-view history in
the reached selected row. Authentication comes from that actual row's Current
receipt, preserving its own ghost witness. -/
theorem ready_of_stable_read {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (selected : Fin keys.length) {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (read : index.store.read? keys[selected.val].frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata) :
    Ready initial keys[selected.val].frameLocation native := by
  have encoded := Option.some.inj ((CallableIndexedOwnedFunctionEntries.reached_frame_read initial selected).symm.trans read)
  have current : (initial.rows selected).authority.current = native := by
    have decoded := congrArg (SourceCoreCallableIndexedFrames.decode compiled.indexed.ancestry.layout.frame) encoded
    simpa only [SourceCoreCallableIndexedFrames.decode_encode, Option.some.injEq] using decoded
  have actualHistory := (initial.rows selected).authority.frame.history
  rw [current] at actualHistory
  obtain ⟨reachedMetadata, carried⟩ := current_history_of_stable stable actualHistory
  refine ⟨selected, reachedMetadata, rfl, current, ?_⟩
  simpa only [current] using carried

def producer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.OrdinaryAllocation.Producer (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native payload sourceValue sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
/-! A live authority row supplies the actual marked allocation even when its
independent source cell keeps a type erased by the compiler's marker binder.
The selected row registers the same captured snapshot before the payload. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAllocationProducer (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

def producer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program))
    (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions) :
    ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      compiled.indexed.layouts compiled.indexed.ancestry.layout.frame model where
  Ready := Ready
  complete := by
    intro owner active request globals allocate allocation annotation same _definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native sourceType payload sourceValue sourceLocation
      environments agrees heaps reference _read payloadAt cell allocated initial ready
    obtain ⟨selected, metadata, physicalOwner, current, history⟩ := ready
    subst contextLocation
    subst native
    obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, _boundEnvironment,
      frame, final, related, _selectedRecords, _otherRecords⟩ :=
      CallableIndexedOwnedOrdinaryAllocation.completed_bind_for_type allocation annotation same registered initial selected
        history environments agrees heaps reference payloadAt cell allocated
    exact ⟨captured, captures, capturedTyped, evaluated, finalHeaps, finalReference, frame, final, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
/-! Returning from an actual body restores the saved physical caller cell in
its reached pool. Scope and canonical values then return to the caller while
all reached ordered record lists and full capture receipts remain retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}
  (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)

/-- The actual final map, world, heap and store come from the completed body.
Only the saved caller's source scope and canonical spine return. -/
def finalIndex : ProtectedStateTransition.Index :=
  ⟨caller.scope, body.mapping, body.world, body.heap,
    body.store.set keys[selected.val].frameLocation
      (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current),
    caller.canonical⟩

/-- Owned pools are independent of the source spine, so this is the same
restored reached pool, with no new rows or capture reconstruction. -/
def returned : State headers keys (finalIndex (body := body) saved selected) :=
  CallableIndexedOwnedFunctionState.restored saved reached selected

theorem returned_records : records (returned saved reached selected) = records reached :=
  CallableIndexedOwnedFunctionState.restored_records saved reached selected

theorem returned_registered {record : CallableIndexedSnapshots.Record} :
    (returned saved reached selected).Registered record ↔ reached.Registered record := by
  constructor
  · intro registered
    obtain ⟨row, member⟩ := registered
    refine ⟨row, ?_⟩
    change record ∈ records (returned saved reached selected) row at member
    change record ∈ records reached row
    rw [← returned_records saved reached selected]
    exact member
  · intro registered
    obtain ⟨row, member⟩ := registered
    refine ⟨row, ?_⟩
    change record ∈ records reached row at member
    change record ∈ records (returned saved reached selected) row
    rw [returned_records saved reached selected]
    exact member

theorem returned_related : Relates reached (returned saved reached selected) :=
  Relates.of_records_eq (returned_records saved reached selected)

theorem returned_from_saved (related : Relates saved reached) :
    Relates saved (returned saved reached selected) :=
  related.trans (returned_related saved reached selected)

theorem returned_same_frame (row : Fin keys.length)
    (same : keys[row.val].frameLocation = keys[selected.val].frameLocation) :
    ((returned saved reached selected).rows row).authority.current = (saved.rows selected).authority.current ∧
    ((returned saved reached selected).rows row).authority.ghost = (saved.rows selected).authority.ghost :=
  CallableIndexedOwnedFunctionState.restored_same_frame saved reached selected row same

theorem returned_other_frame (row : Fin keys.length)
    (different : keys[row.val].frameLocation ≠ keys[selected.val].frameLocation) :
    ((returned saved reached selected).rows row).authority.current = (reached.rows row).authority.current ∧
    ((returned saved reached selected).rows row).authority.ghost = (reached.rows row).authority.ghost :=
  CallableIndexedOwnedFunctionState.restored_other_frame saved reached selected row different

theorem returned_snapshot (row : Fin keys.length) {record : CallableIndexedSnapshots.Record}
    (member : record ∈ records reached row) :
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame body.mapping (finalIndex (body := body) saved selected).store record :=
  CallableIndexedOwnedFunctionState.restored_snapshot saved reached selected row member

theorem returned_capture_read (row : Fin keys.length)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[row.val].locations keys[row.val].capturePrefix (reached.rows row).authority.frameLocation
      header body.mapping body.world body.heap body.store) :
    (finalIndex (body := body) saved selected).store.read? (keys[row.val].locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  CallableIndexedOwnedFunctionState.restored_capture_read saved reached selected row member capture

/-- The one actual restore producer retains the completed body's full heap,
records and captures. Its related receipt comes from the actual invocation
chain; administrative effects alone do not supply that receipt. -/
theorem restore_return {next : NativeFrame}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      body.mapping body.store)
    (related : Relates saved reached) :
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap (finalIndex (body := body) saved selected).store ∧
    AdministrativePreserved caller.mapping caller.store body.mapping (finalIndex (body := body) saved selected).store ∧
    CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost (finalIndex (body := body) saved selected).store ∧
    Relates reached (returned saved reached selected) ∧
    Relates saved (returned saved reached selected) ∧
    records (returned saved reached selected) = records reached ∧
    ProtectedStateTransition.Transition (protocol headers keys) saved (finalIndex (body := body) saved selected) := by
  obtain ⟨final, same, finalHeaps, finalFrame, finalCell, _related, _records⟩ :=
    CallableIndexedOwnedFunctionState.restore_reached saved reached selected registered heaps worlds frame
  exact ⟨finalHeaps, finalFrame, finalCell, returned_related saved reached selected,
    returned_from_saved saved reached selected related, returned_records saved reached selected,
    returned saved reached selected, returned_from_saved saved reached selected related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestoration
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
/-! An actual named body post remains at its completed body store. The caller
restoration is a separate receipt at that same body state and selected frame. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState

abbrev BodyFaultPost := Program → Dynamic.Closure → SourceSemantics.Context →
  Dynamic.Environment → Dynamic.Heap → Environment → Store → Expr →
  Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

/-- Successful bodies impose no primitive fault attribution. -/
def OutcomePost (post : BodyFaultPost) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (actual : Environment) (initialStore : Store) (body : Expr) (type : Ty)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .value _ => True
  | .fault reason => ∃ token, value = .inLeft type (.word token) ∧
      post program function context environment before actual initialStore body reason after token mapping world store

def Trivial : BodyFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

theorem trivial_of_result {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {actual : Environment} {initialStore store : Store} {body : Expr} {type : Ty}
    {mapping : LocationMap} {world : StoreTyping} {faults : FunctionCalls.FaultRep}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (result : FunctionCalls.ResultRepresents model mapping world function.resultType type faults outcome value) :
    OutcomePost Trivial program function context environment before actual initialStore body type
      outcome after value mapping world store := by
  cases result with
  | value represented => trivial
  | @fault reason token represented => exact ⟨token, rfl, trivial⟩

/-- Reflection retains the measured parameter prefix and its actual body child.
Preservation does not invent a native grade. -/
def Measured (budget : Option Nat) (actual : Environment) (initialStore : Store) (parameters : Expr)
    (bodyActual : Environment) (bodyInitial : Store) (body : Expr) (value : Value) (bodyStore : Store) : Prop :=
  match budget with
  | none => ContinuationAgreement actual initialStore parameters bodyActual bodyInitial body
  | some bound => ∃ prefixSize child,
      EvaluationSize prefixSize actual initialStore parameters value bodyStore ∧
      EvaluationSize child bodyActual bodyInitial body value bodyStore ∧
      child ≤ prefixSize ∧ prefixSize < bound

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {canonical : Environment}

/-- The selected invocation keeps the one actual parameter entry, body trace,
body post, and original restore producer. Its post is at bodyStore throughout. -/
def ReturnedAt (post : BodyFaultPost) (sourceParent : Nat) (nativeBudget : Option Nat)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (arguments : List Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ origin index metadata administrative actualContext actual ξ,
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
      (store.set (caller.rows owner.position).authority.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ (caller.rows owner.position).authority.frameLocation
      (.state index) (.named origin),
    ∃ parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    ∃ sourceSize bodyStore,
    ∃ bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode ∧
      Relates caller parameterState ∧ Relates parameterState bodyState ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      sourceSize < sourceParent ∧
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      OutcomePost post program header.function header.context entry.environment entry.heap
        entry.actualBody entry.store (header.body.rename entry.embedding) header.output
        outcome after value finalMap finalWorld bodyStore ∧
      Measured nativeBudget actual
        (store.set (caller.rows owner.position).authority.frameLocation
          (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      Relates caller bodyState ∧
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[owner.position.val].frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost finalStore ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState

/-- A retained body fact is indexed by the original parameter entry and its
same two actual pools. It is independent of the meaning of that fact, and its
seed locations and capture prefix remain arbitrary. -/
abbrev BodyExtra :=
  ∀ {locations : Locations} {capturePrefix : Nat}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping}
    {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
    (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost) →
    (parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) →
    (outcome : Dynamic.ExpressionOutcome) → (after : Dynamic.Heap) → (value : Value) →
    (finalMap : LocationMap) → (finalWorld : StoreTyping) → (bodyStore : Store) →
    (bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩) → Prop

/-- Legacy body callbacks can retain the same witness with no additional fact. -/
def TrivialExtra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
    (keys := keys) (functions := functions) (registry := registry) (header := header) :=
  fun {_locations} {_capturePrefix} {_arguments} {_before} {_initialStore} {_initialMap} {_initialWorld}
    {_administrative} {_actualContext} {_actual} {_ξ} {_frameLocation} {_current} {_ghost}
    _entry _parameterState _outcome _after _value _finalMap _finalWorld _bodyStore _bodyState => True

/-- The extra and the actual restored frame share the entire original causal
spine. The body entry, parameter pool and completed body pool are bound once. -/
def ReturnedAtWithExtra (post : BodyFaultPost)
    (extra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
      (keys := keys) (functions := functions) (registry := registry) (header := header))
    (sourceParent : Nat) (nativeBudget : Option Nat)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (arguments : List Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalMap : LocationMap) (finalWorld : StoreTyping) (finalStore : Store) : Prop :=
  ∃ origin index metadata administrative actualContext actual ξ,
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap
      (store.set (caller.rows owner.position).authority.frameLocation
        (encode compiled.indexed.ancestry.layout.frame (.state index))) mapping world
      administrative actualContext actual ξ (caller.rows owner.position).authority.frameLocation
      (.state index) (.named origin),
    ∃ parameterState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    ∃ sourceSize bodyStore,
    ∃ bodyState : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
      compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named header.named.signature.key) = some origin ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        (.state index) (.named origin) (some metadata) ∧
      header.code = withFrame (.var (compiled.indexed.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)) header.parameterCode ∧
      Relates caller parameterState ∧ Relates parameterState bodyState ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context
        entry.environment entry.heap outcome after ∧
      sourceSize < sourceParent ∧
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      OutcomePost post program header.function header.context entry.environment entry.heap
        entry.actualBody entry.store (header.body.rename entry.embedding) header.output
        outcome after value finalMap finalWorld bodyStore ∧
      Measured nativeBudget actual
        (store.set (caller.rows owner.position).authority.frameLocation
          (encode compiled.indexed.ancestry.layout.frame (.state index)))
        (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) value bodyStore ∧
      Relates caller bodyState ∧
      finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store ∧
      CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame keys[owner.position.val].frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost finalStore ∧
      Relates bodyState (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      Relates caller (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) ∧
      records (CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position) = records bodyState ∧
      extra entry parameterState outcome after value finalMap finalWorld bodyStore bodyState ∧
      AdministrativePreserved mapping store finalMap
        (CallableIndexedOwnedBodyRestoration.finalIndex caller owner.position
          (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, bodyStore, entry.canonical⟩)).store

/-- Forget only the extra fact and restored-frame proof from the same witnesses. -/
theorem ReturnedAtWithExtra.forget {post : BodyFaultPost}
    {extra : BodyExtra (compiled := compiled) (program := program) (headers := headers)
      (keys := keys) (functions := functions) (registry := registry) (header := header)}
    {sourceParent : Nat} {nativeBudget : Option Nat}
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalMap : LocationMap} {finalWorld : StoreTyping} {finalStore : Store}
    (receipt : ReturnedAtWithExtra post extra sourceParent nativeBudget owner caller arguments
      outcome after value finalMap finalWorld finalStore) :
    ReturnedAt (functions := functions) (registry := registry) (header := header) post sourceParent nativeBudget
      owner caller arguments outcome after value finalMap finalWorld finalStore := by
  obtain ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, owned, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords, _extra, _restoredFrame⟩ := receipt
  exact ⟨origin, index, metadata, administrative, actualContext, actual, ξ,
    entry, parameterState, sourceSize, bodyStore, bodyState, owned, history, emitted,
    parameterRelated, bodyRelated, trace, smaller, evaluated, bodyPost, measured,
    related, sameStore, restoredCell, fromBody, fromCaller, sameRecords⟩

end Solcore.SourceSemantics.CoreLowering.NamedInvocationFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
/-! The complete physical cache is independent of ordinary Source headers.
Every row keeps its actual installed code, captured environment and unmapped
cell through Source effects and actual frame writes. Method Source authority
is supplied separately by its selected implementation receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveGlobalInitializationMeaning CallableIndexedHistory SourceCoreCallableIndexedFrames

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

abbrev location (compiled : SourceCoreUnifiedCompilation.Compiled) (slot : Nat) : Location :=
  RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals slot

abbrev environment (compiled : SourceCoreUnifiedCompilation.Compiled) : Environment :=
  SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed

/-- Canonical physical references range over actual signatures, including
method signatures. They do not identify a Source callable. -/
def Slots (compiled : SourceCoreUnifiedCompilation.Compiled) (callerPrefix : Nat)
    (scope : SourceCoreLocalCell.Scope) (canonical : Environment) : Prop :=
  ∀ slot signature, compiled.indexed.base.globals[slot]? = some signature →
    canonical[scope.length + callerPrefix + slot]? = some
      (.cellRef (OptionalCell.cellType signature.functionType) (location compiled slot))

/-- Global slots lie past the scope, so a canonical environment that keeps every
slot past the scope, such as the copies a closure makes, keeps them. -/
theorem Slots.of_slots {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical copied : Environment}
    (slots : Slots compiled callerPrefix scope canonical)
    (kept : ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    Slots compiled callerPrefix scope copied :=
  fun slot signature found => (kept _ (by omega)).trans (slots slot signature found)

theorem environment_slots (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Slots compiled 0 [] (environment compiled) := by
  intro slot signature found
  have reference := RecursiveNamedCatalogInitialization.global_reference compiled.indexed.base.globals
    compiled.indexed.ancestry.layout.frame found
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[slot]? = _ at reference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
  simpa only [List.length_nil, Nat.zero_add, environment, location] using reference

theorem Slots.prepend {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    (slots : Slots compiled callerPrefix scope canonical) (id : Resolved.LocalId) (type : Ty) (value : Value) :
    Slots compiled callerPrefix ((id, type) :: scope) (value :: canonical) := by
  intro slot signature found
  have offset : ((id, type) :: scope).length + callerPrefix + slot = scope.length + callerPrefix + slot + 1 := by simp; omega
  rw [offset]
  exact slots slot signature found

theorem Slots.restore {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {id : Resolved.LocalId} {type : Ty} {value : Value}
    (slots : Slots compiled callerPrefix ((id, type) :: scope) (value :: canonical)) :
    Slots compiled callerPrefix scope canonical := by
  intro slot signature found
  have reference := slots slot signature found
  have offset : ((id, type) :: scope).length + callerPrefix + slot = scope.length + callerPrefix + slot + 1 := by simp; omega
  rw [offset] at reference
  exact reference

/-- The actual parameter allocation spine preserves every physical global
reference below the local cells and the single packed-argument slot. -/
theorem Slots.parameters {canonical added : Environment} {scope : SourceCoreLocalCell.Scope}
    (slots : Slots compiled 0 [] canonical) (packed : Value)
    (length : added.length = scope.length) :
    Slots compiled 1 scope (added ++ packed :: canonical) := by
  intro slot signature found
  have offset : scope.length + 1 + slot = added.length + (slot + 1) := by omega
  rw [offset, List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using slots slot signature found

/-- Actual physical rows include ordinary functions and selected methods. -/
structure Authority (compiled : SourceCoreUnifiedCompilation.Compiled)
    (mapping : LocationMap) (store : Store) : Prop where
  cells : ∀ slot row, (RecursiveNamedCachedRows.rows compiled)[slot]? = some row →
    location compiled slot ∉ mapping ∧
      store.read? (location compiled slot) =
        some (.inRight .unit (installedValue (environment compiled) slot row))

variable {mapping futureMap : LocationMap} {store futureStore : Store}

theorem Authority.extend (authority : Authority compiled mapping store)
    (frame : AdministrativePreserved mapping store futureMap futureStore) :
    Authority compiled futureMap futureStore := by
  constructor
  intro slot row found
  obtain ⟨unmapped, read⟩ := authority.cells slot row found
  obtain ⟨futureUnmapped, same⟩ := frame _ unmapped (List.getElem?_eq_some_iff.mp read).1
  exact ⟨futureUnmapped, same.trans read⟩

/-- Successful cache extraction retains the whole installed lambda. -/
theorem Authority.cached (authority : Authority compiled mapping store)
    {slot : Nat} {parameter result : Ty} {body : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some (.lambda parameter result body)) :
    location compiled slot ∉ mapping ∧
      store.read? (location compiled slot) = some (.inRight .unit
        (.closure parameter result (body.rename (shift slot).lift)
          (List.replicate slot .unit ++ environment compiled))) := by
  obtain ⟨row, found, same, _⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached
  rcases row with ⟨actualParameter, actualResult, actualBody⟩
  change Expr.lambda parameter result body = Expr.lambda actualParameter actualResult actualBody at same
  cases same
  exact authority.cells slot _ found

/-- A stored lambda cannot be a mutable history frame. -/
theorem Authority.ne_frame (authority : Authority compiled mapping store)
    {slot : Nat} {row : LambdaRow} (found : (RecursiveNamedCachedRows.rows compiled)[slot]? = some row)
    {frameLocation : Location} {native : NativeFrame}
    (frameRead : store.read? frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    location compiled slot ≠ frameLocation := by
  intro same
  obtain ⟨_, read⟩ := authority.cells slot row found
  rw [← same, read] at frameRead
  cases native <;> simp [encode, installedValue] at frameRead

/-- Replacing the genuine frame preserves every exact cache cell. -/
theorem Authority.install (authority : Authority compiled mapping store)
    {frameLocation : Location} {native : NativeFrame}
    (frameRead : store.read? frameLocation = some (encode compiled.indexed.ancestry.layout.frame native))
    (next : NativeFrame) :
    Authority compiled mapping (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame next)) := by
  have written : store.write? frameLocation (encode compiled.indexed.ancestry.layout.frame next) =
      some (store.set frameLocation (encode compiled.indexed.ancestry.layout.frame next)) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp frameRead).1, rfl⟩
  constructor
  intro slot row found
  obtain ⟨unmapped, read⟩ := authority.cells slot row found
  exact ⟨unmapped, (Store.write?_preserves_other written (authority.ne_frame found frameRead)).trans read⟩

/-- The real initial store installs all rows, without a semantic Header for
method rows and without assuming a Source body execution. -/
theorem initial (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Authority compiled [] (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
  constructor
  intro slot row found
  have cached : compiled.indexed.secondPass.closures[slot]? = some row.expression := by
    rw [RecursiveNamedCachedRows.exact_cache, List.getElem?_map, found]
    rfl
  obtain ⟨actual, actualFound, _, read⟩ := RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached
  have same : actual = row := Option.some.inj (actualFound.symm.trans found)
  subst actual
  exact ⟨by simp, read⟩

/-- Successful bootstrap fixes the native store before physical authority is
introduced. This proof does not need an ordinary inventory to cover methods. -/
theorem of_completed {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    Authority compiled [] finalStore := by
  have same := (RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed).2
  rw [same]
  exact initial compiled

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalGlobals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocation
/-! Mixed-cell allocation retains the same live authority pool. The exact
snapshot is registered in the selected row before the new payload becomes a
Source binder; unrelated rows retain their complete histories. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedAuthorityPool
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

section Allocation
variable {catalog : SourceCoreDataCatalog.Catalog}
  {model : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {sourceCell : Dynamic.Cell} {payload : Option Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope
    sourceEnvironment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree request.references canonical actual)
  (heaps : GenericHeap.CellHeapRepresents model mapping world before store)
  (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
  (cell : model.Represents mapping world sourceCell
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
  (allocated : CallableIndexedCellAllocation.SourceStep before sourceCell sourceLocation after)

include same registered history environments agrees heaps reference payloadAt cell allocated in
/-- One actual allocation producer supplies capture selection, execution,
source/native heap correspondence and the live pool's registered snapshot.
No evaluation, new-record separation or post-state law is assumed. -/
theorem completed_bind :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.CellHeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) after
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ReferenceRepresents (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) sourceLocation (store.length + 2) request.payloadType ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
          OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, sourceLocation) :: sourceEnvironment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical)
        compiled.indexed.layouts.definitions ∧
      AdministrativePreserved mapping store (mapping ++ [store.length + 2])
        (store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
          ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
              OptionalCell.cellType request.payloadType], after,
            store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
            .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) := by
  have read := CallableIndexedOwnedFunctionEntries.reached_frame_read initial selected
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped, frame⟩ :=
    CallableIndexedCellAllocation.preserves_with_captures allocation annotation same rfl registered
      environments agrees heaps reference read payloadAt cell allocated
  have bound : ∀ target ∈ mapping, target < store.length := by
    intro target member
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    exact heaps.target_lt found
  let record : CallableIndexedSnapshots.Record :=
    ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
  have holds := CallableIndexedSnapshots.completed (layout := compiled.indexed.ancestry.layout.frame) history bound
    (SourceCoreHeapMarkers.markerValue allocation.entry.layout captured)
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload)
  have separate : ∀ i : Fin keys.length, record.location ≠ keys[i.val].frameLocation := by
    intro i
    have earlier := (List.getElem?_eq_some_iff.mp (initial.rows i).authority.frame.read).1
    rw [(initial.rows i).frame_eq] at earlier
    exact Nat.ne_of_gt earlier
  let extended := initial.extend (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
    (show WorldExtends world (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
      OptionalCell.cellType request.payloadType]) from ⟨_, rfl⟩)
    frame allocated.metadata
  let final := extended.record_snapshot selected record holds separate
  refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped,
    CallableIndexedOrdinaryAllocation.bind_environment environments mapped, frame, final, ?_, ?_, ?_⟩
  · intro i
    by_cases chosen : i = selected
    · subst i
      exact ⟨[record], Pool.record_snapshot_selected extended selected record holds separate⟩
    · refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact Pool.record_snapshot_other extended selected record holds separate i chosen
  · exact Pool.record_snapshot_selected extended selected record holds separate
  · intro i different
    exact Pool.record_snapshot_other extended selected record holds separate i different

end Allocation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCellAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
/-! Builtin expression correspondence uses only a certified read's actual
uninitialized cell and an index header's actual unavailable mapping witness.
The original tree, literal sites, compiler tokens and finite traces remain
unchanged. Unrelated expression IDs and metadata rows need no fault law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionBuiltins CompatibleExpressionIndices

private theorem reached_terminal {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (reasonAt : ExpressionId → Word) {faults : FunctionCalls.FaultRep}
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults) :
    IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence reasonAt (fun _ => True) faults ExpressionFailurePostContracts.TrivialExpressionPost := by
  intro id base key node baseNode keyNode layout comparison first second header sourceType profile
    mapping world baseSource keySource baseValue keyValue baseRep keyRep environment nativeContext heap store
    actualTyped heaps sourceEnvironment before middle keyFound form baseTrace keyTrace
  obtain ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional, _trace, _post⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes baseRep keyRep actualTyped heaps keyFound form baseTrace keyTrace (reasonAt id) (missing header keyFound form baseTrace keyTrace)
  exact ⟨outcome, result, finalStore, futureWorld, terminal, represented, lookup, finalHeaps, worlds, frame, functional,
    index_intro header.metadata form (terminal.trace baseTrace keyTrace), ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel values source context reasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults)

include extension faithful functionLeaves functionTypes unique reads missing in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (CompatibleExpressionBuiltins.preserves_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (ExpressionFailurePostContracts.Preserves.forget
          (ReachedLoweredReadOutcomePorts.lowered_read_preserves_with_post functions extension program context evidence reasonAt reads unique)))
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionProxies.preserves functions extension program context evidence unique faults))
      (reached_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes unique reads missing in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (CompatibleExpressionBuiltins.reflects_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (ExpressionFailurePostContracts.Reflects.forget
          (ReachedLoweredReadOutcomePorts.lowered_read_reflects_with_post functions extension program context evidence reasonAt reads unique)))
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionProxies.reflects functions extension program context evidence faults))
      (reached_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedExpressionDiagnosticBounds
end
