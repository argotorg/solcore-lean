import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CoreContinuationSize

/-! The original completion of an actual indexed lambda exposes its frame,
manifest and marked parameter prefix. Every sized body witness is a child of
that original completion. The reached source/native state is existential;
identity with an arbitrary older Entry is not asserted. Source body meaning,
source grades and reflection remain independent of this native prefix result.
No unsized continuation agreement is converted back into a size bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames SourceCoreLambdaTemplates

private theorem manifest_rename (fields : List (Word × Ty)) (ξ : Renaming) :
    (scopeManifest fields).rename ξ = scopeManifest fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp [scopeManifest, Expr.rename, ih]

private theorem captures_rename (scope : SourceCoreLocalCell.Scope) (references ξ : Renaming) :
    (SourceCoreSourceCells.captures references scope).rename ξ =
      SourceCoreSourceCells.captures (Renaming.comp ξ references) scope := by
  induction scope generalizing references with
  | nil => rfl
  | cons head rest ih => cases rest with
    | nil => rfl
    | cons next tail => simp only [SourceCoreSourceCells.captures, Expr.rename, ih]; rfl

private theorem fields_typed {world : StoreTyping} {definitions : DataEnvironment}
    (fields : List (Word × Ty)) :
    RuntimeValueHasType world (scopeManifestValue fields) (scopeManifestType fields) definitions := by
  induction fields with
  | nil => exact .unit
  | cons head rest ih => exact .pair (.pair .word (.inLeft .unit)) ih

/-- Only the actual manifest let is stripped. Its captures remain the values
selected by the real lexical references in the full actual environment. -/
theorem manifest_prefix {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {canonical actual : Environment}
    {argument : Value} {ξ : Renaming}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope source canonical definitions)
    (agrees : EnvironmentsAgree ξ (argument :: canonical) actual)
    (descriptor : Word) (fields : List (Word × Ty)) (body : Expr) (store : Store) :
    ∃ manifest,
      RuntimeValueHasType world manifest
        (.product .word (.product (scopeManifestType fields) (SourceCoreSourceCells.captureType scope))) definitions ∧
      ContinuationSize true actual store
        ((manifestBody descriptor fields (SourceCoreSourceCells.captures id scope) body).rename ξ)
        (manifest :: actual) store (body.rename (Renaming.comp (Renaming.insertion 0) ξ)) := by
  have capturesAgree : EnvironmentsAgree (fun index => ξ (index + 1)) canonical actual := by
    intro index value found
    exact agrees (index := index + 1) found
  obtain ⟨captured, selected, typed⟩ := CallableIndexedOrdinaryAllocation.captures_typed related capturesAgree
  refine ⟨.pair (.word descriptor) (.pair (scopeManifestValue fields) captured),
    .pair .word (.pair (fields_typed fields) typed), ?_⟩
  simp only [manifestBody, Expr.rename, manifest_rename]
  have renamed : (body.weakenAt 0).rename ξ.lift =
      body.rename (Renaming.comp (Renaming.insertion 0) ξ) := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
    rfl
  rw [renamed]
  apply ContinuationSize.letE
  apply Evaluates.pair .word (Evaluates.pair (scopeManifest_evaluates fields actual store) ?_)
  rw [← Expr.rename_insertion, Expr.rename_comp, captures_rename]
  exact selected.evaluates store

private theorem body_rename (body : Expr) (ξ : Renaming) :
    (((body.weakenAt 1).rename ξ.lift.lift).weakenAt 0).weakenAt 0 =
      body.rename (CallableIndexedLambdaEntryPrefix.bodyEmbedding ξ) := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, CallableIndexedLambdaEntryPrefix.bodyEmbedding]
  congr 1
  funext index
  cases index <;> rfl

private theorem body_agrees {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (argument lexical saved : Value) :
    EnvironmentsAgree (CallableIndexedLambdaEntryPrefix.bodyEmbedding ξ) (argument :: canonical)
      (.unit :: saved :: argument :: lexical :: actual) := by
  intro index value found
  cases index with
  | zero => exact found
  | succ index => exact agrees found

private theorem reference_typed {definitions : DataEnvironment} {world : StoreTyping} {environment : Environment}
    {context : Core.Context} {index location : Nat} {type : Ty}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some (.cellRef type location)) : world[location]? = some type := by
  have atType : context[index]? = some (.cell type) := by
    rw [← typed.type_tags]
    simp [List.getElem?_map, found, Value.type]
  obtain ⟨value, selected, related⟩ := typed.lookup atType
  have same := Option.some.inj (selected.symm.trans found)
  subst value
  cases related with | cellRef typed => exact typed

private theorem liftMany_insertion (count cutoff : Nat) :
    DataMatchCoreAllocation.liftMany count (Renaming.insertion cutoff) = Renaming.insertion (cutoff + count) := by
  induction count generalizing cutoff with
  | zero => rfl
  | succ count ih =>
    simp only [DataMatchCoreAllocation.liftMany, Renaming.lift_insertion, ih]
    congr 1
    omega

/-- The actual reached state retains the supplied function model in its full
heap. Sizes come from the original completion, independently of these fields. -/
structure PrefixFor {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {capturedActual : Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared initialMap initialWorld scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)) (registry : SourceCoreRawMetadata.Registry)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store) (location : Location)
    (current : NativeFrame) where
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actual : Environment
  actualContext : Core.Context
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    captured.administrative
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    environment canonical prepared.layouts.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap inputs.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap (initialStore.set location (encode prepared.ancestry.layout.frame next)) mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  spine : ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
    canonical = added ++ captured.canonical
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions
  reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type location)
  read : store.read? location = some (encode prepared.ancestry.layout.frame next)
  unmapped : location ∉ mapping

structure Prefix {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {capturedActual : Environment}
    (captured : CallableIndexedLambdaValues.Captures prepared initialMap initialWorld scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (profile : values.checked.catalog.callableContracts = true) (registry : SourceCoreRawMetadata.Registry)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store) (location : Location)
    (current : NativeFrame) where
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actual : Environment
  actualContext : Core.Context
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    captured.administrative
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    environment canonical prepared.layouts.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap inputs.context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap (initialStore.set location (encode prepared.ancestry.layout.frame next)) mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  spine : ∃ added : Environment, added.length = code.receipt.loweredParameters.length ∧
    canonical = added ++ captured.canonical
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions
  reference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type location)
  read : store.read? location = some (encode prepared.ancestry.layout.frame next)
  unmapped : location ∉ mapping

/-- This fieldwise adapter retains the exact legacy function model. It does
not strengthen a heap or recover a size from an unsized entry. -/
def Prefix.toFor {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {capturedActual : Environment}
    {captured : CallableIndexedLambdaValues.Captures prepared initialMap initialWorld scope function.captured capturedActual}
    {code : Code prepared function scope captured.administrative} {history : History code}
    {inputs : CallableIndexedLambdaEntryPrefix.Context code}
    {profile : values.checked.catalog.callableContracts = true} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store} {location : Location}
    {current : NativeFrame}
    (reached : Prefix captured code history inputs profile registry arguments before initialStore location current) :
    PrefixFor captured code history inputs (model prepared profile) registry arguments before initialStore location current :=
  ⟨reached.next, reached.nextHistory, reached.environment, reached.heap, reached.canonical, reached.actual,
    reached.actualContext, reached.store, reached.mapping, reached.world, reached.embedding, reached.allocation,
    reached.environments, reached.heaps, reached.locals, reached.maps, reached.worlds,
    reached.frame, reached.metadata, reached.spine, reached.lookups, reached.actualTyped,
    reached.reference, reached.read, reached.unmapped⟩

/-- Only the exact legacy specialization is converted back. -/
def PrefixFor.toLegacy {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {initialMap : LocationMap} {initialWorld : StoreTyping}
    {capturedActual : Environment}
    {captured : CallableIndexedLambdaValues.Captures prepared initialMap initialWorld scope function.captured capturedActual}
    {code : Code prepared function scope captured.administrative} {history : History code}
    {inputs : CallableIndexedLambdaEntryPrefix.Context code}
    {profile : values.checked.catalog.callableContracts = true} {registry : SourceCoreRawMetadata.Registry}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store} {location : Location}
    {current : NativeFrame}
    (reached : PrefixFor captured code history inputs (model prepared profile) registry arguments before initialStore location current) :
    Prefix captured code history inputs profile registry arguments before initialStore location current :=
  ⟨reached.next, reached.nextHistory, reached.environment, reached.heap, reached.canonical, reached.actual,
    reached.actualContext, reached.store, reached.mapping, reached.world, reached.embedding, reached.allocation,
    reached.environments, reached.heaps, reached.locals, reached.maps, reached.worlds,
    reached.frame, reached.metadata, reached.spine, reached.lookups, reached.actualTyped,
    reached.reference, reached.read, reached.unmapped⟩


section GenericEntry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- Frame and manifest steps are strict even for an empty parameter prefix.
The final body witness comes only from the supplied original completion. -/
theorem body_prefix_for {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  let layout := prepared.ancestry.layout.frame
  let argument := DataPatternValues.packValues nativeArguments
  let saved := encode layout current
  let lexical := encode layout history.native
  let next := SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current
  have registered := CallableIndexedAmbient.frame_registered prepared
  have caller : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table layout location current currentGhost store :=
    ⟨read, .stable currentCarried⟩
  have nextHistory := ordinary_complete prepared.ancestry.graph history.carried currentCarried allowed
  have refTyped := reference_typed captured.represented.runtime_hasTypes reference
  obtain ⟨installedHeaps, installedCurrent⟩ := CallableIndexedBodyFrames.install registered heaps unmapped refTyped caller (.stable nextHistory)
  have hook := code.receipt.bodyHook
  rw [code.manifest] at hook
  obtain ⟨descriptor, fields, emitted⟩ := CallableIndexedLambdaManifest.of_hook hook
  let actual := .unit :: saved :: argument :: lexical :: capturedActual
  have actualLayout : EnvironmentsAgree (CallableIndexedLambdaEntryPrefix.bodyEmbedding captured.embedding)
      (argument :: captured.canonical) actual := body_agrees captured.agrees argument lexical saved
  have actualTyped : RuntimeEnvironmentHasTypes world actual
      (.unit :: layout.type :: SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :: layout.type :: captured.actualContext)
      prepared.layouts.definitions :=
    .cons .unit (.cons (encode_runtime_typed world registered current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented)
        (.cons (encode_runtime_typed world registered history.native) captured.typed)))
  have selectedReference : (argument :: lexical :: capturedActual)[captured.embedding code.referenceIndex + 2]? =
      some (.cellRef layout.type location) := by simpa using captured.agrees reference
  have selected : DataEquality.Selects (argument :: lexical :: capturedActual)
      (.var (captured.embedding code.referenceIndex + 2)) (.cellRef layout.type location) := .var selectedReference
  have nextEvaluation : Evaluates (saved :: argument :: lexical :: capturedActual) store
      ((SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
        (.loadCell (.var (captured.embedding code.referenceIndex + 2)))).weakenAt 0)
      (encode layout next) store := by
    obtain ⟨position, nativeEq, _⟩ := history.carried.state_shape
    dsimp only [next, lexical]
    rw [nativeEq, CallableIndexedRenaming.lambdaFrame_weaken]
    simpa only [Expr.weakenAt, Nat.zero_le, ↓reduceIte] using
      (CallableIndexedProtocol.lambdaFrame_load (layout := layout)
        (environment := saved :: argument :: encode layout (.state (Int.ofNat position)) :: capturedActual)
        (lexical := .var 2) (referenceIndex := captured.embedding code.referenceIndex + 3)
        prepared.ancestry.graph.table code.descriptor.id (.var rfl)
        (by simpa [Nat.add_assoc] using captured.agrees reference) read)
  have wrapper : code.body.rename captured.embedding.lift.lift =
      withFrame (.var (captured.embedding code.referenceIndex + 2))
        (SourceCoreCallableIndexedDispatch.lambdaFrame prepared.ancestry.graph.table layout code.descriptor.id (.var 1)
          (.loadCell (.var (captured.embedding code.referenceIndex + 2))))
        ((code.receipt.rawBody.weakenAt 1).rename captured.embedding.lift.lift) := by
    simp only [Code.body, NamedCalls.withFrame_rename, CallableIndexedRenaming.lambdaFrame, Expr.rename, Renaming.lift]
    rfl
  rw [wrapper] at completed
  obtain ⟨nextSize, rawSize, nextValue, nextStore, bodyStore, nextEval, rawEval, _, rawLess, restored⟩ :=
    RecursiveNamedCallBounds.with_frame selected read completed
  obtain ⟨nextValueEq, nextStoreEq⟩ := evaluation_deterministic nextEval.sound nextEvaluation
  rw [nextValueEq, nextStoreEq, body_rename, emitted] at rawEval
  obtain ⟨manifest, manifestTyped, manifestSize⟩ := manifest_prefix captured.represented actualLayout
    descriptor fields code.receipt.allocatedBody (store.set location (encode layout next))
  obtain ⟨parameterSize, parameterLess, parameterEval⟩ := manifestSize.remaining rawEval
  have tree := CallableIndexedParameterCertificates.of_accepted code.allocationError
    (CallableIndexedLambdaEntryPrefix.prefix_accepted code)
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) captured.canonical
      (argument :: captured.canonical) := by intro index value found; exact found
  have length : (code.receipt.loweredParameters.map Prod.snd).length = nativeArguments.length := by
    simpa using represented.length.2
  obtain ⟨environment, heap, canonical, logical, bodyActual, prefixStore, finalMap, finalWorld, embedding, child,
      allocated, environments, finalHeaps, maps, worlds, frame, sourceLayout, lookups, spine, finalTyped,
      bodyEval, childBound, _⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree rfl registered represented captured.represented installedHeaps
      sourceLayout (GenericExpressionMeaning.agree_prefix actualLayout manifest) (.cons manifestTyped actualTyped)
      (allTypes := code.receipt.loweredParameters.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by simpa only [← code.viewOfSource.inputs] using inputs.kinds)
      (by simpa [inputs.referenceIndex] using reference) installedCurrent.read unmapped parameterEval
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + prepared.base.globals.length]? =
      some (.cellRef layout.type location) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : code.receipt.loweredParameters.length + scope.length + 1 + prepared.base.globals.length =
        added.length + (scope.length + 1 + prepared.base.globals.length) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa [inputs.referenceIndex, layout] using reference
  have finalLookups : EnvironmentsAgree (Renaming.comp embedding (Renaming.insertion code.receipt.loweredParameters.length))
      canonical bodyActual := by
    intro index value found
    apply lookups
    have transported := sourceLayout found
    simpa only [liftMany_insertion, Nat.zero_add] using transported
  have bodyEq : (code.receipt.body.weakenAt code.receipt.loweredParameters.length).rename embedding =
      code.receipt.body.rename (Renaming.comp embedding (Renaming.insertion code.receipt.loweredParameters.length)) := by
    rw [← Expr.rename_insertion, Expr.rename_comp]
  rw [bodyEq] at bodyEval
  rw [← CallableIndexedLambdaEntryPrefix.parameters code] at allocated
  have mono := FunctionCallBody.mono_binders inputs.extended
  obtain ⟨finalUnmapped, unchanged⟩ := frame location unmapped
    (List.getElem?_eq_some_iff.mp installedCurrent.read).1
  refine ⟨⟨next, nextHistory, environment, heap, canonical, bodyActual, _, prefixStore, finalMap, finalWorld,
    Renaming.comp embedding (Renaming.insertion code.receipt.loweredParameters.length), allocated,
    by simpa [CallableIndexedParameters.scope_eq] using environments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 locals allocated,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocated,
    ⟨added, prefixLength, canonicalEq⟩, finalLookups, finalTyped,
    finalReference, unchanged.trans installedCurrent.read, finalUnmapped⟩,
    child, bodyStore, Nat.lt_trans (Nat.lt_of_le_of_lt childBound parameterLess) rawLess, bodyEval, restored⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
/-- The authenticated payload application adds its original strict body edge.
The argument and complete captured environment are exactly the stored values;
stage guards and the enclosing expression head are separate boundaries. -/
theorem application_prefix_for {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨reached, child, bodyStore, childLess, evaluated, restored⟩ :=
    body_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed applied
  exact ⟨reached, child, bodyStore, Nat.lt_trans childLess smaller, evaluated, restored⟩

end GenericEntry

section Entry
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : CallableIndexedLambdaValues.Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context code) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {location : Location}
  {current : NativeFrame} {currentGhost : GhostFrame} {currentMetadata : Option MetadataState}
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
  (read : store.read? location = some (encode prepared.ancestry.layout.frame current))
  (currentCarried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost currentMetadata)
  (unmapped : location ∉ mapping)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true)

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
theorem body_prefix {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    body_prefix_for captured code history inputs (model prepared profile)
      represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached.toLegacy (profile := profile), child, bodyStore, smaller, evaluated, restored⟩

include captured code history inputs profile represented heaps locals reference read currentCarried unmapped allowed in
theorem application_prefix {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments]
      store CallableIndexedLambdaCalls.applyPayload result finalStore) :
    ∃ reached : Prefix captured code history inputs profile registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored⟩ :=
    application_prefix_for captured code history inputs (model prepared profile)
      represented heaps locals reference read currentCarried unmapped allowed completed
  exact ⟨reached.toLegacy (profile := profile), child, bodyStore, smaller, evaluated, restored⟩

end Entry

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
