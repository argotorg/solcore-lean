import Solcore.SourceSemantics.CoreLowering.CallableIndexedAuthorityPool
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals

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
new key is created by capturing the current value. -/
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
    (ghost : (pool.rows owner.position).authority.ghost = history.ghost)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    Represents headers keys bodyRegistry faults mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding history.native actual) ∧ finalStore = store) := by
  have reference : captured.canonical[code.referenceIndex]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]; exact globals.reference
  have read : store.read? owner.key.frameLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (pool.rows owner.position).authority.frame.read
    rw [(pool.rows owner.position).frame_eq, current] at actualRead
    exact actualRead
  have sameHistory : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table history.native history.ghost := by
    simpa only [current, ghost] using (pool.rows owner.position).authority.frame.history
  obtain ⟨sourceTrace, nativeTrace, strong⟩ := CallableIndexedLambdaRuntimeValues.formation_with
    (values := .initial compiled.compatible.checked) (program := program) compiled.indexed
    (P := fun _ _ _ _ => True) captured code history body True.intro profile stored reference read heap ordinary coercions
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType (registry := bodyRegistry)
    (CallableIndexedLambdaRuntimeValues.RepresentsWith.forget (values := .initial compiled.compatible.checked) compiled.indexed strong)
  exact ⟨sourceTrace, nativeTrace, .lambda owner captured code history body origin globals referenceIndex typed,
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
