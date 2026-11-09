import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CaptureCopies

/-!
# Indexed callables: lambda entries

Entry of indexed lambdas: prefixes, bounds, catalog entries, semantic invocation and native typing.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
/-! The actual indexed lambda entry before body semantics.
Captures and carried caller/lexical histories construct the real frame update,
manifest and marked parameter fold. A source parameter context is retained;
neither a body compiler equation nor body execution is needed for this prefix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

/-- Static source parameter layout required by the real entry prefix.
Body syntax, compilation and execution are independent of these inputs. -/
structure Context {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) where
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  kinds : ∀ binding ∈ code.receipt.loweredParameters,
    function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false
  referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length

theorem parameters {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    function.parameters = code.receipt.loweredParameters.map Prod.fst :=
  (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).binders.symm

theorem prefix_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
        (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError))
      code.view scope code.receipt.loweredParameters code.receipt.resultCore SourceCoreFunctions.argumentProjection
      (code.receipt.body.weakenAt code.receipt.loweredParameters.length) = .ok code.receipt.allocatedBody := by
  have accepted := code.receipt.allocated
  simpa only [CallableIndexedLambdaCertificates.parameterBody, code.allocationProfile] using accepted

/-- The entry's copies of the captures, through the indexed marked allocator. -/
theorem copies_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    SourceCoreSourceCells.copyScope
      (some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
        (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError)))
      code.view scope (· + 1) code.receipt.allocatedBody = .ok code.receipt.copiedBody := by
  have copied := code.receipt.copied
  rw [code.allocationProfile] at copied
  exact copied

def bodyEmbedding (ξ : Renaming) : Renaming :=
  Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0)
    (Renaming.comp (Renaming.insertion 1) ξ.lift))

private theorem body_rename (body : Expr) (ξ : Renaming) :
    (((body.weakenAt 1).rename ξ.lift.lift).weakenAt 0).weakenAt 0 = body.rename (bodyEmbedding ξ) := by
  simp only [← Expr.rename_insertion, Expr.rename_comp, bodyEmbedding]
  congr 1
  funext index
  cases index <;> rfl

private theorem body_agrees {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (argument lexical saved : Value) :
    EnvironmentsAgree (bodyEmbedding ξ) (argument :: canonical) (.unit :: saved :: argument :: lexical :: actual) := by
  intro index value found
  cases index with
  | zero => exact found
  | succ index => exact agrees found

/-- After the manifest, the packed argument and the captured slots keep their
types through the body embedding. -/
theorem body_respects {ξ : Renaming} {context actualContext : Core.Context}
    (respects : Renaming.Respects ξ context actualContext) (manifestType frameType argumentType : Ty) :
    Renaming.Respects (Renaming.comp (Renaming.insertion 0) (bodyEmbedding ξ)) (argumentType :: context)
      (manifestType :: .unit :: frameType :: argumentType :: frameType :: actualContext) := by
  intro index type found
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst type
    rfl
  | succ index =>
    simpa [bodyEmbedding, Renaming.comp, Renaming.insertion, Renaming.lift] using respects (by simpa using found)

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

/-- The actual entry retains the supplied function relation in every allocated
cell and argument. Static body receipts may therefore travel in that relation
without being recovered from a weaker heap after the prefix. -/
structure EntryFor {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CallableIndexedLambdaViewPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values
    functions registry function inputs.context scope code.receipt.loweredParameters arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world captured.administrative
    actualContext actual embedding code.receipt.copiedBody code.receipt.body
  wrap : ∀ {result bodyStore}, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore →
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result (bodyStore.set location (encode prepared.ancestry.layout.frame current))
  unwrap : ∀ {result finalStore},
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore →
    ∃ bodyStore, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current)
  unmapped : location ∉ mapping
  referenceTyped : world[location]? = some prepared.ancestry.layout.frame.type
  currentHistory : Current prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost
  currentRead : store.read? location = some (encode prepared.ancestry.layout.frame current)

structure Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CallableIndexedLambdaViewPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values
    (model prepared profile) registry function inputs.context scope code.receipt.loweredParameters arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world captured.administrative
    actualContext actual embedding code.receipt.copiedBody code.receipt.body
  wrap : ∀ {result bodyStore}, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore →
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result (bodyStore.set location (encode prepared.ancestry.layout.frame current))
  unwrap : ∀ {result finalStore},
    Evaluates (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore →
    ∃ bodyStore, Evaluates entry.actualBody entry.store (code.receipt.body.rename entry.embedding) result bodyStore ∧
      finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current)
  unmapped : location ∉ mapping
  referenceTyped : world[location]? = some prepared.ancestry.layout.frame.type
  currentHistory : Current prepared.ancestry.graph.inputs prepared.ancestry.graph.table current currentGhost
  currentRead : store.read? location = some (encode prepared.ancestry.layout.frame current)

/-- The legacy receipt is the exact specialization of the generic entry. This
adapter keeps its original function relation and does not strengthen a heap. -/
def Entry.toFor {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    {captured : Captures prepared mapping world scope function.captured capturedActual}
    {code : Code prepared function scope captured.administrative} {history : History code}
    {inputs : Context code} {profile : values.checked.catalog.callableContracts = true}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
    (entry : Entry captured code history inputs profile registry arguments nativeArguments before store location current currentGhost) :
    EntryFor captured code history inputs (model prepared profile) registry arguments nativeArguments before store location current currentGhost :=
  ⟨entry.next, entry.nextHistory, entry.actual, entry.actualContext, entry.embedding,
    entry.entry, entry.wrap, entry.unwrap, entry.unmapped, entry.referenceTyped,
    entry.currentHistory, entry.currentRead⟩

namespace Stateful

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists_for_with_spine {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
    {registry : SourceCoreRawMetadata.Registry}
    {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol prepared.layouts prepared.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions))
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (rebinds : ProtectedStateTransition.Rebinds protocol) {arguments : List Dynamic.Value} {nativeArguments : List Value}
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
    (initial : protocol.State ⟨scope, mapping, world, before,
      store.set location (encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current)),
      captured.canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current)) :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩ := by
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
  have actualLayout : EnvironmentsAgree (bodyEmbedding captured.embedding) (argument :: captured.canonical) actual :=
    body_agrees captured.agrees argument lexical saved
  have actualTyped : RuntimeEnvironmentHasTypes world actual
      (.unit :: layout.type :: SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :: layout.type :: captured.actualContext)
      prepared.layouts.definitions :=
    .cons .unit (.cons (encode_runtime_typed world registered current)
      (.cons (CallableIndexedParameters.Arguments.pack_typed represented)
        (.cons (encode_runtime_typed world registered history.native) captured.typed)))
  obtain ⟨manifest, manifestTyped, manifestAgreement⟩ := CallableIndexedLambdaManifest.agreement
    captured.represented actualLayout descriptor fields code.receipt.copiedBody (store.set location (encode layout next))
  obtain ⟨entry, added, copiedCanonical, prefixLength, canonicalEq, slots, transition⟩ :=
    CallableIndexedLambdaViewPrefix.Stateful.entry_of_accepted_with_spine functions code.allocationError protocol producer
    transport rebinds code.viewOfSource (prefix_accepted code) (copies_accepted code) (parameters code) inputs.kinds
    inputs.extended rfl registered represented captured.represented installedHeaps locals
    (GenericExpressionMeaning.agree_prefix actualLayout manifest)
    (body_respects captured.respects _ layout.type _) (.cons manifestTyped actualTyped)
    (inputs.referenceIndex ▸ reference) installedCurrent.read unmapped initial readyAt
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
  have agreement : ContinuationAgreement actual (store.set location (encode layout next))
      (code.receipt.rawBody.rename (bodyEmbedding captured.embedding)) entry.actualBody entry.store
      (code.receipt.body.rename entry.embedding) := by
    rw [emitted]
    exact manifestAgreement.trans entry.agreement
  refine ⟨⟨next, nextHistory, _, _, _, entry, ?_, ?_, unmapped, refTyped, .stable currentCarried, read⟩,
    added, copiedCanonical, prefixLength, canonicalEq, slots, transition⟩
  · intro result bodyStore evaluated
    rw [wrapper]
    apply CallableContextFrames.withFrame_evaluates selected read nextEvaluation
    rw [body_rename]
    exact agreement.wrap evaluated
  · intro result finalStore evaluated
    rw [wrapper] at evaluated
    obtain ⟨nextValue, nextStore, bodyStore, nextEval, bodyEval, finalEq⟩ :=
      CallableContextFrames.withFrame_reflects selected read evaluated
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEval nextEvaluation
    rw [body_rename] at bodyEval
    exact ⟨bodyStore, agreement.unwrap bodyEval, finalEq⟩

end Stateful

theorem entry_exists_for_with_spine {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
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
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    ∃ entry : EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost,
      ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
        entry.entry.canonical = added ++ copied ∧
        (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?) := by
  obtain ⟨entry, added, copied, length, spine, slots, _transition⟩ :=
    Stateful.entry_exists_for_with_spine captured code history inputs functions
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer prepared.layouts prepared.ancestry.layout.frame
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      ProtectedStateTransition.OrdinaryAllocation.unitTransport ProtectedStateTransition.OrdinaryAllocation.unitRebinds
      represented heaps locals reference read currentCarried unmapped allowed () (by intro index state read; trivial)
  exact ⟨entry, added, copied, length, spine, slots⟩

/-- The original generic entry keeps the same model and forgets only the
canonical allocation prefix witness. -/
theorem entry_exists_for {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared))
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
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost) := by
  obtain ⟨entry, _⟩ := entry_exists_for_with_spine captured code history inputs functions
    represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨entry⟩

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (inputs : Context code) (profile : values.checked.catalog.callableContracts = true)
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
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history inputs profile registry arguments nativeArguments before store location current currentGhost) := by
  obtain ⟨entry⟩ := entry_exists_for captured code history inputs (model prepared profile)
    represented heaps locals reference read currentCarried unmapped allowed
  exact ⟨⟨entry.next, entry.nextHistory, entry.actual, entry.actualContext,
    entry.embedding, entry.entry, entry.wrap, entry.unwrap, entry.unmapped,
    entry.referenceTyped, entry.currentHistory, entry.currentRead⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
/-! The original completion of an actual indexed lambda exposes its frame,
manifest, the marked copies of its captures and its marked parameter prefix. Every sized body witness is a child of
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
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
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
  spine : ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
    canonical = added ++ copied ∧ (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
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
  copies : Dynamic.Environment
  copiedHeap : Dynamic.Heap
  copy : Dynamic.EnvironmentCopies function.source function.captured before copies copiedHeap
  allocation : Dynamic.BindersAllocate copies copiedHeap function.parameters arguments environment heap
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
  spine : ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
    canonical = added ++ copied ∧ (∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)
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
    reached.actualContext, reached.store, reached.mapping, reached.world, reached.embedding, reached.copies,
    reached.copiedHeap, reached.copy, reached.allocation,
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
    reached.actualContext, reached.store, reached.mapping, reached.world, reached.embedding, reached.copies,
    reached.copiedHeap, reached.copy, reached.allocation,
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

namespace Stateful
variable {Records : Type} (protocol : ProtectedStateTransition.Protocol Records)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol prepared.layouts prepared.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (rebinds : ProtectedStateTransition.Rebinds protocol)
  (initial : protocol.State ⟨scope, mapping, world, before,
    store.set location (encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current)),
    captured.canonical⟩)
  (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location
    (SourceCoreCallableIndexedDispatch.selectedFrame prepared.ancestry.graph.table code.descriptor.id history.native current))

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed protocol producer transport rebinds initial readyAt in
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
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
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
    descriptor fields code.receipt.copiedBody (store.set location (encode layout next))
  obtain ⟨parameterSize, parameterLess, parameterEval⟩ := manifestSize.remaining rawEval
  obtain ⟨copies, copiedHeap, copiedCanonical, copiedActual, copiedContext, copiedStore, copiedMap,
      copiedWorld, copiedEmbedding, copy, copiedEnvironments, slots, copiedHeaps, copiedMaps, copiedWorlds,
      copiedFrame, copiedRead, copiedLookups, _copiedTypes, copiedTyped, copyAgreement⟩ :=
    CaptureCopies.marked_copies_prefix (pre := [argument])
      (preContext := [SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd)])
      (CallableIndexedLambdaEntryPrefix.copies_accepted code) rfl registered captured.represented installedHeaps
      (GenericExpressionMeaning.agree_prefix actualLayout manifest) rfl
      (CallableIndexedLambdaEntryPrefix.body_respects captured.respects _ layout.type _)
      (.cons manifestTyped actualTyped) (by simpa [inputs.referenceIndex] using reference) installedCurrent.read
  have sourceCopy := copy.of_copiedBinder (LambdaMetadataViews.MetadataView.copiedBinder code.viewOfSource).symm
  obtain ⟨copiedSize, copiedLe, copiedEval⟩ := copyAgreement.unwrap parameterEval
  obtain ⟨copiedUnmapped, _⟩ := copiedFrame location unmapped
    (List.getElem?_eq_some_iff.mp installedCurrent.read).1
  obtain ⟨extendedState, extendedRelated⟩ := ProtectedStateTransition.AdministrativeTransport.transition protocol
    transport initial copiedMaps copiedWorlds copiedFrame sourceCopy.metadata_extends
  obtain ⟨reboundState, reboundRelated⟩ := rebinds extendedState copiedCanonical slots
  have copiedReference : copiedCanonical[scope.length + 1 + prepared.base.globals.length]? =
      some (.cellRef layout.type location) := by
    rw [slots _ (by omega)]
    simpa [inputs.referenceIndex] using reference
  have tree := CallableIndexedParameterCertificates.of_accepted code.allocationError
    (CallableIndexedLambdaEntryPrefix.prefix_accepted code)
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) copiedCanonical
      (argument :: copiedCanonical) := by intro index value found; exact found
  have length : (code.receipt.loweredParameters.map Prod.snd).length = nativeArguments.length := by
    simpa using represented.length.2
  obtain ⟨environment, heap, canonical, logical, bodyActual, prefixStore, finalMap, finalWorld, embedding, child,
      allocated, environments, finalHeaps, maps, worlds, frame, sourceLayout, lookups, spine, finalTyped,
      bodyEval, childBound, _, transition⟩ :=
    RecursiveNamedCallBounds.Stateful.parameter_prefix tree protocol producer rfl registered
      (represented.extend copiedMaps copiedWorlds) copiedEnvironments copiedHeaps
      sourceLayout copiedLookups copiedTyped
      (allTypes := code.receipt.loweredParameters.map Prod.snd) (named := false) rfl (by simp) length
      (fun {_ _} found => by simpa using found)
      (by simpa only [← code.viewOfSource.inputs] using inputs.kinds)
      (by simpa using copiedReference) copiedRead copiedUnmapped reboundState readyAt copiedEval
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have finalReference : canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length + 1 + prepared.base.globals.length]? =
      some (.cellRef layout.type location) := by
    rw [canonicalEq]
    simp only [List.length_append, List.length_map, List.length_reverse]
    have index : code.receipt.loweredParameters.length + scope.length + 1 + prepared.base.globals.length =
        added.length + (scope.length + 1 + prepared.base.globals.length) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using copiedReference
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
  obtain ⟨finalUnmapped, unchanged⟩ := frame location copiedUnmapped
    (List.getElem?_eq_some_iff.mp copiedRead).1
  have copiedLocals := Dynamic.EnvironmentCopies.agrees locals sourceCopy
  refine ⟨⟨next, nextHistory, environment, heap, canonical, bodyActual, _, prefixStore, finalMap, finalWorld,
    Renaming.comp embedding (Renaming.insertion code.receipt.loweredParameters.length), copies, copiedHeap,
    sourceCopy, allocated, by simpa [CallableIndexedParameters.scope_eq] using environments, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 copiedLocals allocated,
    copiedMaps.trans maps, copiedWorlds.trans worlds, copiedFrame.trans frame,
    sourceCopy.metadata_extends.trans (GenericLexicalContext.binders_metadata allocated),
    ⟨added, copiedCanonical, prefixLength, canonicalEq, slots⟩, finalLookups, finalTyped,
    finalReference, unchanged.trans copiedRead, finalUnmapped⟩,
    child, bodyStore, Nat.lt_trans (Nat.lt_of_le_of_lt childBound
      (Nat.lt_of_le_of_lt copiedLe parameterLess)) rawLess, bodyEval, restored, ?_⟩
  have composed : ProtectedStateTransition.Transition protocol initial
      ⟨code.receipt.loweredParameters.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope,
        finalMap, finalWorld, heap, prefixStore, canonical⟩ := by
    obtain ⟨reached, related⟩ := transition
    exact ⟨reached, protocol.trans (protocol.trans extendedRelated reboundRelated) related⟩
  simpa only [CallableIndexedParameters.scope_eq] using composed

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed protocol producer transport rebinds initial readyAt in
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
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) ∧
        ProtectedStateTransition.Transition protocol initial
          ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
            reached.mapping, reached.world, reached.heap, reached.store, reached.canonical⟩ := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨reached, child, bodyStore, childLess, evaluated, restored, transition⟩ :=
    body_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed
      protocol producer transport rebinds initial readyAt applied
  exact ⟨reached, child, bodyStore, Nat.lt_trans childLess smaller, evaluated, restored, transition⟩

end Stateful

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
theorem body_prefix_for {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode prepared.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) result finalStore) :
    ∃ reached : PrefixFor captured code history inputs functions registry arguments before store location current,
      ∃ child bodyStore,
        child < size ∧ EvaluationSize child reached.actual reached.store
          (code.receipt.body.rename reached.embedding) result bodyStore ∧
        finalStore = bodyStore.set location (encode prepared.ancestry.layout.frame current) := by
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored, _transition⟩ :=
    Stateful.body_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer prepared.layouts prepared.ancestry.layout.frame
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      ProtectedStateTransition.OrdinaryAllocation.unitTransport ProtectedStateTransition.OrdinaryAllocation.unitRebinds
      () (by intro index state read; trivial) completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored⟩

include captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed in
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
  obtain ⟨reached, child, bodyStore, smaller, evaluated, restored, _transition⟩ :=
    Stateful.application_prefix_for captured code history inputs functions represented heaps locals reference read currentCarried unmapped allowed
      ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer prepared.layouts prepared.ancestry.layout.frame
        (CompatibleAmbientHeap.payloadModel values.checked registry functions))
      ProtectedStateTransition.OrdinaryAllocation.unitTransport ProtectedStateTransition.OrdinaryAllocation.unitRebinds
      () (by intro index state read; trivial) completed
  exact ⟨reached, child, bodyStore, smaller, evaluated, restored⟩

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
/-! Actual lambda prefixes transport a separately observed finite catalog.
The unsized allocator receipt and the original sized completion use the same
installation and ordered-spine proof. Source entries retain the lambda ghost,
full carried metadata and physical frame reference; named source entries are
not substituted for them. Catalog authority and capture coherence remain
independent inputs. No lambda body correspondence is supplied here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)}
  {capturePrefix callerPrefix : Nat}

/-- These are observations of actual ordered captures and the shared physical
frame. They contain neither authority nor a runtime body law. -/
structure CaptureGlobals (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program))
    (callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope) (canonical : Environment) (location : Location) : Prop where
  globals : ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? = some
    (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header))
  reference : canonical[scope.length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type location)

def CaptureGlobals.catalog {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment} {location : Location}
    (observed : CaptureGlobals headers locations callerPrefix scope canonical location)
    (authority : RecursiveNamedCatalog.Authority headers locations capturePrefix mapping world heap store) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical :=
  ⟨authority, observed.globals⟩

/-- Global and frame slots lie past the scope, so a canonical environment that
keeps every slot past the scope, such as the copies a closure makes, keeps them. -/
theorem CaptureGlobals.of_slots {canonical copied : Environment} {location : Location}
    (observed : CaptureGlobals headers locations callerPrefix scope canonical location)
    (slots : ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    CaptureGlobals headers locations callerPrefix scope copied location :=
  ⟨fun header member => (slots _ (by omega)).trans (observed.globals header member),
    (slots _ (by omega)).trans observed.reference⟩

/-- Keeping a finite supported prefix preserves its observed global and frame
slots. Bounds are independent static evidence about those actual slots. -/
theorem CaptureGlobals.take {canonical : Environment} {location : Location}
    (observed : CaptureGlobals headers locations callerPrefix scope canonical location) {count : Nat}
    (globalBounds : ∀ header, header ∈ headers → scope.length + callerPrefix + header.slot < count)
    (frameBound : scope.length + 1 + prepared.base.globals.length < count) :
    CaptureGlobals headers locations callerPrefix scope (canonical.take count) location := by
  constructor
  · intro header member
    rw [List.getElem?_take, if_pos (globalBounds header member)]
    exact observed.globals header member
  · rw [List.getElem?_take, if_pos frameBound]
    exact observed.reference

section Prefix
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {canonical : Environment} {code : Code prepared function scope administrative} {history : History code}
  {location : Location} {next : NativeFrame} {futureMap : LocationMap} {futureWorld : StoreTyping}
  {after : Dynamic.Heap} {futureStore : Store} {futureCanonical : Environment}

/-- The sole catalog installation proof consumes original prefix effects and
the actual allocator's ordered additions. It does not execute a body. -/
def catalog_after_prefix
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
    (sameFrame : initial.authority.frameLocation = location)
    (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
      (.lambda code.descriptor.id history.ghost) (some history.metadata))
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping (store.set location (encode prepared.ancestry.layout.frame next)) futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after)
    (spine : ∃ added copied : Environment, added.length = code.receipt.loweredParameters.length ∧
      futureCanonical = added ++ copied ∧ ∀ slot, scope.length ≤ slot → copied[slot]? = canonical[slot]?) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      futureMap futureWorld after futureStore futureCanonical := by
  let installed := initial.authority.install (Current.stable history)
  have installedFrame : AdministrativePreserved mapping
      (store.set initial.authority.frameLocation (encode prepared.ancestry.layout.frame next)) futureMap futureStore := by
    simpa only [sameFrame] using frame
  refine ⟨installed.extend maps worlds installedFrame metadata, ?_⟩
  intro header member
  obtain ⟨added, copied, length, canonicalEq, kept⟩ := spine
  rw [canonicalEq]
  simp only [List.length_append, List.length_map, List.length_reverse]
  have index : code.receipt.loweredParameters.length + scope.length + callerPrefix + header.slot =
      added.length + (scope.length + callerPrefix + header.slot) := by omega
  rw [index, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    kept _ (by omega)]
  exact initial.globals header member

end Prefix

/-- This source entry has the actual lambda ghost and full original metadata.
Its frame reference and catalog authority are separate from native typing. -/
structure SourceEntry (code : Code prepared function scope administrative) (history : History code)
    (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix callerPrefix : Nat)
    (bodyScope : SourceCoreLocalCell.Scope) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical
  ghost : catalog.authority.ghost = .lambda code.descriptor.id history.ghost
  carried : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table catalog.authority.current
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  reference : canonical[bodyScope.length + 1 + prepared.base.globals.length]? =
    some (.cellRef prepared.ancestry.layout.frame.type catalog.authority.frameLocation)

variable {code : Code prepared function scope administrative} {history : History code}

def SourceEntry.extend {bodyScope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : SourceEntry code history headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    SourceEntry code history headers locations capturePrefix callerPrefix bodyScope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds frame metadata }

def protectedEntry (code : Code prepared function scope administrative) (history : History code)
    (headers : RecursiveNamedCatalog.Inventory prepared.ancestry values prepared.layouts.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values)
      (ambient := CallableIndexedAmbient.ambientDefinitions prepared) (program := program)) (capturePrefix callerPrefix : Nat) :
    ProtectedExpressionMeaning.Entry :=
  fun bodyScope mapping world heap store canonical =>
    Nonempty (SourceEntry code history headers locations capturePrefix callerPrefix bodyScope mapping world heap store canonical)

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry code history headers locations capturePrefix callerPrefix) := by
  constructor
  intro bodyScope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry code history headers locations capturePrefix callerPrefix) := by
  constructor
  · intro bodyScope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ catalog := ⟨entry.catalog.authority, ?_⟩
              ghost := entry.ghost, carried := entry.carried, reference := ?_ }⟩
    · intro header member
      have index : ((id, type) :: bodyScope).length + callerPrefix + header.slot =
          (bodyScope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.catalog.globals header member
    · have index : ((id, type) :: bodyScope).length + 1 + prepared.base.globals.length =
          (bodyScope.length + 1 + prepared.base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.reference
  · intro bodyScope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ catalog := ⟨entry.catalog.authority, ?_⟩
              ghost := entry.ghost, carried := entry.carried, reference := ?_ }⟩
    · intro header member
      have found := entry.catalog.globals header member
      have index : ((id, type) :: bodyScope).length + callerPrefix + header.slot =
          (bodyScope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using found
    · have found := entry.reference
      have index : ((id, type) :: bodyScope).length + 1 + prepared.base.globals.length =
          (bodyScope.length + 1 + prepared.base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using found

section ActualEntry
variable {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code}
  {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  (entry : CallableIndexedLambdaEntryPrefix.EntryFor captured code history inputs functions registry arguments nativeArguments before store location current currentGhost)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added copied : Environment} (length : added.length = code.receipt.loweredParameters.length)
  (spine : entry.entry.canonical = added ++ copied)
  (slots : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?)

/-- Unsized prefix construction retains its exact returned entry and spine.
No completion or grade is extracted from its continuation agreement. -/
def catalog_entry : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  catalog_after_prefix initial sameFrame entry.nextHistory entry.entry.maps entry.entry.worlds entry.entry.frame
    entry.entry.metadata ⟨added, copied, length, spine, slots⟩

def source_entry : SourceEntry code history headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    entry.entry.mapping entry.entry.world entry.entry.heap entry.entry.store entry.entry.canonical :=
  { catalog := catalog_entry entry initial sameFrame length spine slots
    ghost := rfl
    carried := entry.nextHistory
    reference := by
      change entry.entry.canonical[_]? = some (Value.cellRef prepared.ancestry.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using entry.entry.reference }

end ActualEntry

section SizedEntry
variable {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {inputs : CallableIndexedLambdaEntryPrefix.Context code}
  {functions : FunctionModel values.checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared)}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame}
  (reached : CallableIndexedLambdaEntryBounds.PrefixFor captured code history inputs functions registry arguments before store location current)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world before store captured.canonical)
  (sameFrame : initial.authority.frameLocation = location)

def catalog_entry_sized : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  catalog_after_prefix initial sameFrame reached.nextHistory reached.maps reached.worlds reached.frame reached.metadata reached.spine

def source_entry_sized : SourceEntry code history headers locations capturePrefix callerPrefix
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    reached.mapping reached.world reached.heap reached.store reached.canonical :=
  { catalog := catalog_entry_sized reached initial sameFrame
    ghost := rfl
    carried := reached.nextHistory
    reference := by
      change reached.canonical[_]? = some (Value.cellRef prepared.ancestry.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using reached.reference }

end SizedEntry
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCatalogEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
/-! Lambda body semantics at the canonical source retain the actual compiler
view separately. The real lambda callback and parameter fold provide the view
acceptance equation; no canonical body compiler equation is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    extends CallableIndexedLambdaEntryPrefix.Context code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  certificate : BuiltinNamedBody.SemanticReceipt prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError readFuel values
    function.source context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

abbrev parameters := @CallableIndexedLambdaEntryPrefix.parameters
abbrev prefix_accepted := @CallableIndexedLambdaEntryPrefix.prefix_accepted

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaEntryPrefix.Entry captured code history body.toContext profile registry arguments nativeArguments
    before store location current currentGhost

/-- The parameter scope is extracted from the real lambda binder action. -/
theorem body_scope {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) :
    code.receipt.bodyScope = code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  simpa only [List.map_reverse] using (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).scope

/-- Only the actual callback equation changes the compiler action into its
loop-body API; the accepted source argument remains the real view. -/
theorem loops_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {viewRelation : TypedSource → TypedSource → Prop}
    (code : Code prepared function scope administrative viewRelation) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy) :
    SourceCoreLoops.lowerStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := by
  have accepted := code.receipt.bodyCompiled
  rw [callback, body_scope code] at accepted
  exact accepted

structure ViewBody {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where private mk ::
  body : Body code program
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  actual : CallableLambdaViewSemanticReceipt.Receipt prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError body.readFuel values
    function.source code.view body.context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore policy code.fuel code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  semantic : body.certificate = actual.canonical

/-- Build canonical semantics from static syntax/Tree at the actually compiled
view, retaining that view's accepted equation and the exact callback identity. -/
theorem ViewBody.of_tree {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements inputs.context function.evidence)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    (syntaxTree : BuiltinLexicalStatements.Syntax code.view inputs.context true function.body function.resultType)
    {flow : Expr}
    (emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason)
    (tree : BuiltinLexicalStatements.Tree prepared.layouts code.compilation.owner code.active prepared.ancestry.layout.frame
      prepared.base.globals.length code.allocationError readFuel values code.view code.compilation.solvedRequirements code.reasonAt
      inputs.context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      true function.body function.resultType code.receipt.resultCore flow) :
    Nonempty (ViewBody code program) := by
  obtain ⟨actual⟩ := BuiltinNamedBody.of_tree (loops_accepted code policy callback) projection syntaxTree emitted tree
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := function.body) edited avoids unique actual
  exact ⟨⟨{ toContext := inputs, frame, readFuel, certificate := receipt.canonical, valid, unique },
    policy, callback, receipt, rfl⟩⟩

/-- Every native prefix step is derived from its actual compiler receipt.
The caller token and lexical token have independent carried histories. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
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
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost) := by
  exact CallableIndexedLambdaEntryPrefix.entry_exists captured code history body.toContext profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
/-! Same-code static body receipts are independent of their expression grammar.
The actual compiler view supplies flow acceptance and finish equality. Static
occurrence certificates return to the canonical source through the one finite
transport fold. Rank belongs only to nested lambda receipt tokens; named calls
retain arbitrary recursion through the catalog and acquire no rank condition.
This unit supplies no body execution law or call-time catalog authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open CallableLambdaViewEdits CallableLambdaBodyReachability

theorem context_valid {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements) :
    CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements inputs.context function.evidence := by
  exact (CompatibleRuntimeContextValidity.Valid.mk sameLedger frame.code.requirement_ledger frame.evidence_covers).mono inputs.extended

structure BodyWith
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate) {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    extends CallableIndexedLambdaEntryPrefix.Context code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  actualTree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
    (expressionSyntax code.view)
    (certificates readFuel code.view)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  actualSites : actualTree.CatalogSites .reachable registry faults
  tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function.source
    (expressionSyntax function.source)
    (certificates readFuel function.source)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source


theorem BodyWith.of_tree
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate} {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (syntaxTransport : ∀ id, Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      expressionSyntax code.view id → expressionSyntax function.source id)
    (expressions : ∀ context scope id lowered,
      Reaches function.source (function.body.map NodeId.statement) (.expression id) →
      certificates readFuel code.view context scope id lowered →
      certificates readFuel function.source context scope id lowered)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (expressionSyntax code.view)
      (certificates readFuel code.view)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : BodyWith expressionSyntax certificates code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧
      body.flow = flow ∧ HEq body.actualTree tree := by
  have reverse : LocalView code.view function.source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  obtain ⟨canonical, canonicalSites⟩ := CallableLambdaViewMatchRuntimeCertificates.transport_sites_with
    reverse (avoids.view edited.metadata) (edited.metadata.unique unique)
    (fun id reached receipt => syntaxTransport id (reached.metadata edited.metadata.symm) receipt)
    (fun context scope id lowered reached receipt => expressions context scope id lowered
      (reached.metadata edited.metadata.symm) receipt)
    sites (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact ⟨{
    toContext := inputs
    frame := frame
    readFuel := readFuel
    policy := policy
    callback := callback
    flow := flow
    generated := generated
    projection := projection
    emitted := Except.ok.inj accepted.symm
    actualTree := tree
    actualSites := sites
    tree := canonical
    sites := canonicalSites
    valid := context_valid code inputs frame sameLedger
    unique := unique }, rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- Acceptance is retained at the actual compiler view. The canonical Tree
needs no second lowering success. -/
theorem BodyWith.accepted
    {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : BodyWith expressionSyntax certificates code program registry faults) :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body :=
  CallableIndexedLambdaSemanticInvocation.loops_accepted code body.policy body.callback

/-- A family is indexed by actual Code. Its rank may restrict nested lambda
leaves without imposing an order on named catalog calls. -/
abbrev SupportAt
    (expressionSyntax : Nat → TypedSource → ExpressionId → Prop)
    (certificates : Nat → Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (rank : Nat) {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  BodyWith (expressionSyntax rank) (certificates rank) code program registry faults

/-- This token records a smaller static body only at a literal lambda site.
Its source, context, occurrence and emitted expression are explicit receipts. -/
structure NestedLambda
    {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked)
    (support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → Code prepared function scope administrative → Type)
    (rank : Nat) (source : TypedSource) (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  function : Dynamic.Closure
  administrative : Core.Context
  code : Code prepared function scope administrative
  sourceEq : function.source = source
  contextEq : function.context = context
  identifier : code.id = id
  emitted : code.lowered = lowered
  sourceType : code.sourceNode.type = FunctionValues.sourceType function
  requirements : code.sourceNode.requirements = []
  coercions : code.sourceNode.coercions = []
  childRank : Nat
  smaller : childRank < rank
  body : support childRank code

/-- Ordinary and authenticated named calls remain in the existing family.
Only literal lambda tokens contain a static rank comparison. -/
inductive CallsWith
    {values : SourceCoreCompatibleValues.Context} (prepared : Prepared values.checked)
    (support : Nat → {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
      {administrative : Core.Context} → Code prepared function scope administrative → Type)
    (rank : Nat) (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (source : TypedSource) (context : SourceSemantics.Context)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | existing {id lowered} (head : calls children scope id lowered) :
      CallsWith prepared support rank calls source context children scope id lowered
  | lambda {id lowered} (head : NestedLambda prepared support rank source context scope id lowered) :
      CallsWith prepared support rank calls source context children scope id lowered

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
/-! Static runtime body receipts retain the actual lambda callback and accepted
view. Full imperative/match trees return to the canonical source through local
edit reachability. Numeric leaf support comes from the concrete builtin family.
The complete runtime ledger and dictionary come from the actual source closure
frame. Named, indirect and method children, and a combined callable recursion
argument, remain separate boundaries. No body execution law is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev body_scope := @CallableIndexedLambdaSemanticInvocation.body_scope
abbrev loops_accepted := @CallableIndexedLambdaSemanticInvocation.loops_accepted

/-- The source frame carries runtime implementation rows and coverage of the
same complete context. Ordered parameter extension changes only lexical fields. -/
theorem context_valid {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements) :
    CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements inputs.context function.evidence :=
  CallableIndexedLambdaStaticBodySupport.context_valid code inputs frame sameLedger

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    extends CallableIndexedLambdaEntryPrefix.Context code where private mk ::
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy policy
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  actualTree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
    (CompatibleExpressionBuiltins.Syntax code.view)
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values code.view context
      code.compilation.solvedRequirements code.reasonAt)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  actualSites : actualTree.CatalogSites .reachable registry faults
  tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function.source
    (CompatibleExpressionBuiltins.Syntax function.source)
    (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context
      code.compilation.solvedRequirements code.reasonAt)
    prepared.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

def Body.toWith {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) :
    CallableIndexedLambdaStaticBodySupport.BodyWith CompatibleExpressionBuiltins.Syntax
      (fun fuel source context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context
        code.compilation.solvedRequirements code.reasonAt) code program registry faults :=
  { toContext := body.toContext, frame := body.frame, readFuel := body.readFuel, policy := body.policy,
    callback := body.callback, flow := body.flow, generated := body.generated, projection := body.projection,
    emitted := body.emitted, actualTree := body.actualTree, actualSites := body.actualSites,
    tree := body.tree, sites := body.sites, valid := body.valid, unique := body.unique }

def Body.fromWith {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith CompatibleExpressionBuiltins.Syntax
      (fun fuel source context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context
        code.compilation.solvedRequirements code.reasonAt) code program registry faults) :
    Body code program registry faults :=
  { toContext := body.toContext, frame := body.frame, readFuel := body.readFuel, policy := body.policy,
    callback := body.callback, flow := body.flow, generated := body.generated, projection := body.projection,
    emitted := body.emitted, actualTree := body.actualTree, actualSites := body.actualSites,
    tree := body.tree, sites := body.sites, valid := body.valid, unique := body.unique }

/-- The same static body receipt serves the closure over another captured
environment; no receipt mentions the captured locations. -/
def Body.recapture {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) (captured : Dynamic.Environment) :
    Body (code.recapture captured) program registry faults :=
  { body with
    toContext := { body.toContext with context := body.context }
    frame := { body.frame with code := { body.frame.code with occurrence := body.frame.code.occurrence } } }

/-- The actual compiler-view Tree, its indexed diagnostics and the real flow
acceptance construct the canonical receipt; canonical recompilation is absent. -/
theorem Body.of_tree {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) {program : Program}
    (inputs : CallableIndexedLambdaEntryPrefix.Context code)
    (frame : Dynamic.ClosureFrame program function) (readFuel : Nat) (policy : SourceCoreLoops.Policy)
    (callback : code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy policy)
    {changed : List ExpressionId}
    (edited : CallableLambdaViewEdits.LocalView function.source code.view changed)
    (avoids : CallableLambdaBodyReachability.Avoids function.source (function.body.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique function.source)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (projection : values.checked.catalog.project function.resultType = .ok code.receipt.resultCore)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow)
    {tree : GenericImperativeMatch.Tree prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values code.view
      (CompatibleExpressionBuiltins.Syntax code.view)
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values code.view context
        code.compilation.solvedRequirements code.reasonAt)
      prepared.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (sites : tree.CatalogSites .reachable registry faults) :
    ∃ body : Body code program registry faults,
      body.toContext = inputs ∧ body.readFuel = readFuel ∧ body.policy = policy ∧
      body.flow = flow ∧ HEq body.actualTree tree := by
  obtain ⟨body, sameContext, sameFuel, samePolicy, sameFlow, sameTree⟩ :=
    CallableIndexedLambdaStaticBodySupport.BodyWith.of_tree
      (expressionSyntax := CompatibleExpressionBuiltins.Syntax)
      (certificates := fun fuel source context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context
        code.compilation.solvedRequirements code.reasonAt) code inputs frame readFuel policy callback
      edited avoids unique sameLedger
      (fun _id reached syntaxTree => CallableLambdaViewSourceTyping.expression_syntax_original edited avoids unique syntaxTree reached)
      (fun _context _scope _id _lowered reached certificate =>
        CallableLambdaViewMatchRuntimeCertificates.builtin_original edited avoids certificate reached)
      projection generated sites
  exact ⟨Body.fromWith body, sameContext, sameFuel, samePolicy, sameFlow, sameTree⟩


theorem Body.accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) :
    SourceCoreLoops.lowerStatementsWithPolicy body.policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt code.compilation.internalReason code.compilation.internalReason =
      .ok code.receipt.body := body.toWith.accepted

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) (profile : values.checked.catalog.callableContracts = true)
    (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaEntryPrefix.Entry captured code history body.toContext profile registry arguments nativeArguments
    before store location current currentGhost

/-- Nonempty captures and ordered parameters use the existing real entry
construction. The body receipt contributes its source context, never a body law. -/
theorem entry_exists {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (body : Body code program registry faults) (profile : values.checked.catalog.callableContracts = true)
    {arguments : List Dynamic.Value} {nativeArguments : List Value}
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
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.ancestry.graph.inputs history.metadata code.descriptor.id = true) :
    Nonempty (Entry captured code history body profile arguments nativeArguments before store location current currentGhost) :=
  CallableIndexedLambdaEntryPrefix.entry_exists captured code history body.toContext profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues
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
  {environment : Dynamic.Environment} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (storageCatalog values.checked.catalog) projects prepared.layouts.definitions}
  {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}
  (formed : Formed model current code history heap store location)
  (body : support formed.closureCode)
  (supported : P (function := formed.closure) formed.captures formed.closureCode formed.closureHistory body)
  (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)

include body supported profile stored in
/-- The formed closure keeps the support receipt and condition of its code. -/
theorem formation_represents_with :
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  have prior := formed.represents stored
  have typed := (CallableIndexedLambdaValues.model prepared profile).runtime_hasType (registry := values.registry) prior
  exact RepresentsWith.lambda (function := formed.closure) formed.captures formed.closureCode formed.closureHistory
    body supported typed

include body supported profile stored in
theorem formation_with
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    Evaluates actual store (code.lowered.expression.rename current.embedding)
      (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  ⟨formed.source program ordinary coercions, formed.evaluated,
    formation_represents_with prepared formed body supported profile stored⟩

include body supported profile stored in
theorem reflects_with
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
    after = formed.finalStore ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    RepresentsWith prepared support P formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨sameResult, sameStore⟩ := formed.reflects completed
  exact ⟨sameResult, sameStore, formed.source program ordinary coercions,
    formation_represents_with prepared formed body supported profile stored⟩
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
  {environment : Dynamic.Environment} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (storageCatalog values.checked.catalog) projects prepared.layouts.definitions}
  {current : Captures prepared mapping world scope environment actual}
  {code : Code prepared function scope current.administrative} {history : History code}
  {heap : Dynamic.Heap} {store : Store} {location : Location}
  (formed : Formed model current code history heap store location)
  (body : CallableIndexedLambdaRuntimeBody.Body formed.closureCode program bodyRegistry faults)
  (profile : values.checked.catalog.callableContracts = true)
  (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)

include body profile stored in
/-- The original formation proof supplies the exact native result typing. The
new representation stores the independently constructed same-code body. -/
theorem formation_represents :
    Represents prepared program bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  Represents.fromWith prepared program bodyRegistry faults
    (formation_represents_with prepared (support := legacySupport prepared program bodyRegistry faults)
      (P := legacyCondition prepared program bodyRegistry faults) formed body True.intro profile stored)

include body profile stored in
theorem formation
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    Evaluates actual store (code.lowered.expression.rename current.embedding)
      (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
    Represents prepared program bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  ⟨formed.source program ordinary coercions, formed.evaluated,
    formation_represents prepared program bodyRegistry faults formed body profile stored⟩

include body profile stored in
/-- Reflection consumes the original native completion. Determinism identifies
the actual formed closure; no body computation is run during formation. -/
theorem reflects
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) {result : Core.Value} {after : Store}
    (completed : Evaluates actual store (code.lowered.expression.rename current.embedding) result after) :
    result = .inRight .word (value code formed.embedding history.native formed.closureActual) ∧
    after = formed.finalStore ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source environment heap
      code.id (.closure formed.closure) formed.finalHeap ∧
    Represents prepared program bodyRegistry faults formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure) (value code formed.embedding history.native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨sameResult, sameStore⟩ := formed.reflects completed
  exact ⟨sameResult, sameStore, formed.source program ordinary coercions,
    formation_represents prepared program bodyRegistry faults formed body profile stored⟩

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
Formation copies the captured environment after the original prefix; the
same-code static body is stored with the closure over the copies. -/
theorem accepted_site_formation {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (storageCatalog values.checked.catalog) projects prepared.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : site.code.policy.snapshotLambda site.code.id = true)
    (referenceIndex : site.code.referenceIndex = scope.length + 1 + prepared.base.globals.length) :
    ∃ formed : Formed model captured site.code (site.historyAt selected record) heap store location,
      Dynamic.ExpressionEvaluates program sourceContext evidence (CallableIndexedNamedGeneration.source named)
        capturedSource heap site.code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (site.code.lowered.expression.rename captured.embedding)
        (.inRight .word (value site.code formed.embedding
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) formed.closureActual))
        formed.finalStore ∧
      Represents prepared program bodyRegistry faults formed.finalMap formed.finalWorld
        (FunctionValues.sourceType (CallableIndexedLambdaGeneration.closure named parameters resultType statements
          sourceContext evidence capturedSource))
        (.closure formed.closure)
        (value site.code formed.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)
          formed.closureActual)
        (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := CallableIndexedLambdaGeneration.installed_after_prefix selected record entryRead unmapped preserved
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured site.code (site.historyAt selected record)
    copied referenceIndex heaps reference cell.read
  exact ⟨formed, formation (values := values) prepared program bodyRegistry faults formed
    (body.recapture formed.captured) profile stored ordinary coercions⟩

include body profile selected record ordinary coercions entryRead unmapped preserved stored reference in
/-- Completed formation reflection keeps the same accepted site and body. -/
theorem accepted_site_reflection {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (storageCatalog values.checked.catalog) projects prepared.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : site.code.policy.snapshotLambda site.code.id = true)
    (referenceIndex : site.code.referenceIndex = scope.length + 1 + prepared.base.globals.length)
    {output : Core.Value} {after : Store}
    (completed : Evaluates actual store (site.code.lowered.expression.rename captured.embedding) output after) :
    ∃ formed : Formed model captured site.code (site.historyAt selected record) heap store location,
      output = .inRight .word (value site.code formed.embedding
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) formed.closureActual) ∧
      after = formed.finalStore ∧
      Dynamic.ExpressionEvaluates program sourceContext evidence (CallableIndexedNamedGeneration.source named)
        capturedSource heap site.code.id (.closure formed.closure) formed.finalHeap ∧
      Represents prepared program bodyRegistry faults formed.finalMap formed.finalWorld
        (FunctionValues.sourceType (CallableIndexedLambdaGeneration.closure named parameters resultType statements
          sourceContext evidence capturedSource))
        (.closure formed.closure)
        (value site.code formed.embedding (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)
          formed.closureActual)
        (CallableContract.functionType site.code.receipt.parameterCore site.code.receipt.resultCore) := by
  obtain ⟨_, cell⟩ := CallableIndexedLambdaGeneration.installed_after_prefix selected record entryRead unmapped preserved
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured site.code (site.historyAt selected record)
    copied referenceIndex heaps reference cell.read
  exact ⟨formed, reflects (values := values) prepared program bodyRegistry faults formed
    (body.recapture formed.captured) profile stored ordinary coercions completed⟩
end ActualSite
end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
/-! Native typing is assembled before a lambda Code exists. Actual compiler
receipts retain the parameter fold, manifest, frame snapshot and descriptor.
The body profile is restricted to one scalar return or tail expression. Source
typing, ordinary admission and lexical frame placement remain static inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
open Core Frontend SourceInference
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapped_fields {α ε : Type} {items : List α} {fields : List (Word × Ty)}
    {action : α → Except ε (Word × Ty)} {definitions : DataEnvironment}
    (valid : ∀ item ∈ items, ∀ field, action item = .ok field → field.2.WellFormed definitions)
    (accepted : items.mapM action = .ok fields) :
    ∀ field ∈ fields, field.2.WellFormed definitions := by
  induction items generalizing fields with
  | nil => simp at accepted; subst fields; simp
  | cons item rest ih =>
    simp only [List.mapM_cons, bind, Except.bind] at accepted
    cases head : action item with
    | error error => simp [head] at accepted
    | ok field =>
      simp only [head] at accepted
      obtain ⟨tail, generated, same⟩ := bind_ok accepted
      cases same
      intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid item (by simp) _ head
      · exact ih (fun item h => valid item (List.mem_cons_of_mem _ h)) generated selected member

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {convert : ε → δ} {value : α}
    (accepted : action.mapError convert = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- All metadata annotations in the actual manifest are the supplied lexical
scope annotations. The successful hook's source/binder selection is retained. -/
theorem manifest_native {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {node : ExpressionNode} {parameter result : Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope node parameter result body = .ok emitted)
    {definitions : DataEnvironment} {context : Core.Context}
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed definitions)
    (references : ∀ (position : Nat) (binding : Resolved.LocalId × Ty), scope[position]? = some binding →
      context[position]? = some (OptionalCell.referenceType binding.2))
    (bodyTyped : HasType (parameter :: context) body (LanguageResult.resultType result) definitions) :
    HasType (parameter :: context) emitted (LanguageResult.resultType result) definitions := by
  simp only [SourceCoreLambdaTemplates.hook, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  rename_i _ template selected metadata header _ fields fieldsAccepted _ checkedScope scopeChecks
  cases accepted
  apply SourceCoreLambdaTemplates.manifestBody_hasType _ ?_
    (SourceCoreSourceCells.captures_hasType scope id references) bodyTyped
  have generated := mapError_ok fieldsAccepted
  change ((do
      unless (scope.map Prod.fst).Nodup do throw SourceCoreLambdaTemplates.Error.duplicateScope
      scope.mapM fun (binder, type) => do
        let row ← match template.context.bindingAt? binder with
          | some row => pure row
          | none => throw (SourceCoreLambdaTemplates.Error.scopeMismatch binder)
        pure (row.key, type)) : Except SourceCoreLambdaTemplates.Error (List (Word × Ty))) = .ok fields at generated
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at generated
  split at generated
  · apply mapped_fields (items := scope) ?_ generated
    intro binding member field emitted
    split at emitted
    · cases emitted; exact scopeWF binding member
    · cases emitted
  · cases generated

theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd))
    (parameterWF : ∀ binding ∈ receipt.loweredParameters, binding.2.WellFormed checked.catalog.definitions)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type))
    (bodyTyped : HasType (SourceCoreLocalCell.coreContext receipt.bodyScope ++ administrative)
      receipt.body (LanguageResult.resultType receipt.resultCore) prepared.layouts.definitions) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have extension := (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix
  have parameterTyped := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.parameterProjected)).extend_definitions extension
  have resultTyped := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.resultProjected)).extend_definitions extension
  have accepted := receipt.allocated
  simp only [parameterBody, allocation] at accepted
  have bodyScope := (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).scope
  rw [bodyScope, ← List.map_reverse] at bodyTyped
  have allocated := CallableIndexedParameterNativeTyping.of_accepted _ accepted
    (CallableIndexedAmbient.frame_registered prepared) resultTyped
    (fun binding member => (parameterWF binding member).extend_definitions extension)
    ordinary administrative current bodyTyped
  rw [← bundle] at allocated
  have copiedAccepted := receipt.copied
  rw [allocation] at copiedAccepted
  have copied := CaptureCopyTyping.copyScopeIndexed_hasType copiedAccepted rfl
    (CallableIndexedAmbient.frame_registered prepared)
    (by
      intro index id payload found
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [List.cons_append, List.getElem?_cons_succ]
      rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using bound)]
      simp [SourceCoreLocalCell.coreContext, found])
    (fun binding member => (scopeWF binding member).extend_definitions extension)
    (by simpa using current) allocated
  have raw := manifest_native (manifest ▸ receipt.bodyHook)
    (fun binding member => (scopeWF binding member).extend_definitions extension) (context := SourceCoreLocalCell.coreContext scope ++ administrative)
    (by
      intro position binding found
      rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
      simp [SourceCoreLocalCell.coreContext, found, OptionalCell.referenceType]) copied
  obtain ⟨origin, actualBody, _, rawEq, _, globals, _, emitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry (expressionHook ▸ receipt.expressionHook)
  have sameBody := (Expr.lambda.inj rawEq).2.2
  rw [← sameBody] at emitted
  have lambdaTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) receipt.rawLambda
      (.function receipt.parameterCore (LanguageResult.resultType receipt.resultCore)) prepared.layouts.definitions := by
    rw [emitted]
    exact SourceCoreCallableIndexedAncestry.snapshotLambda_hasType
      (CallableIndexedAmbient.frame_registered prepared) _ _ parameterTyped resultTyped
      (by simpa [SourceCoreCallableIndexedAncestry.creationReferenceIndex, administrativePrefix, globals] using current) raw
  have decorated := receipt.decoration
  rw [callables, ActualCallablePolicy.lambda_decoration _ [] compilation view node id receipt.parameterCore receipt.resultCore _ descriptor] at decorated
  have sameExpression := Except.ok.inj decorated
  have checkedType := receipt.checked
  rw [callables] at checkedType
  unfold SourceCoreBasic.ensureType at checkedType
  split at checkedType
  · rename_i sameType
    change reported = CallableContract.functionType receipt.parameterCore receipt.resultCore at sameType
    have typed := LanguageResult.success_hasType (descriptor.wrap_hasType (TaggedFunction.anonymous_hasType lambdaTyped))
    rw [sameExpression] at typed
    have snapshot := receipt.snapshot
    have snapshotTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) receipt.snapshotted
        (LanguageResult.resultType (CallableContract.functionType receipt.parameterCore receipt.resultCore))
        prepared.layouts.definitions := by
      split at snapshot
      · rw [allocation] at snapshot
        exact CaptureCopyTyping.copyScopeIndexed_hasType snapshot rfl (CallableIndexedAmbient.frame_registered prepared)
          (by
            intro index id payload found
            have bound := (List.getElem?_eq_some_iff.mp found).1
            show (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = _
            rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using bound)]
            simp [SourceCoreLocalCell.coreContext, found])
          (fun binding member => (scopeWF binding member).extend_definitions extension)
          (by simpa using current) typed
      · rw [← Except.ok.inj snapshot]
        exact typed
    simpa only [receipt.emitted, sameType] using snapshotTyped
  · cases checkedType

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at checked
  split at checked
  · assumption
  · cases checked

/-- Invert the actual single-return/tail compiler action. The output records
the real child callback and result-type check, including the finish wrapper. -/
theorem scalar_body_receipt {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode} {type : Ty}
    {expression : ExpressionId} {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code) :
    ∃ budget lowered,
      policy.lowerExpression budget source scope expression reasonAt = .ok lowered ∧
      lowered.type = result ∧
      code = LocalControl.finish result (LocalLoop.toControl result
        (LocalLoop.returnValue result lowered.expression) escaped)
        (if result = .unit then LanguageResult.success .unit else LanguageResult.failure result (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  cases fuel with
  | zero => cases generated
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, bind, Except.bind, pure, Except.pure] at generated
    rcases form with form | form
    all_goals
      simp only [form, Bool.not_false, Bool.true_and, List.isEmpty_nil, ↓reduceIte] at generated
    · obtain ⟨checkedUnit, _, generated⟩ := bind_ok generated
      cases checkedUnit
      obtain ⟨lowered, child, generated⟩ := bind_ok generated
      obtain ⟨checkedUnit, checked, generated⟩ := bind_ok generated
      cases checkedUnit
      cases generated
      exact ⟨fuel, lowered, child, (ensure_same checked).symm, rfl⟩
    · obtain ⟨lowered, child, generated⟩ := bind_ok generated
      obtain ⟨checkedUnit, _, generated⟩ := bind_ok generated
      cases checkedUnit
      obtain ⟨checkedUnit, checked, generated⟩ := bind_ok generated
      cases checkedUnit
      cases generated
      exact ⟨fuel, lowered, child, (ensure_same checked).symm, rfl⟩

theorem scalar_body_native {policy : SourceCoreLoops.Policy}
    {expressions : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionBudget : Nat} {compilation : SourceCoreFunctions.Context}
    {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode} {type : Ty}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (callback : policy.lowerExpression = FunctionCode.children expressions lowerBody expressionBudget compilation)
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ordinary : CompatibleExpressionConditionals.PolicyFor expressions compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, CompatibleExpressionConditionals.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    (syntaxTree : CompatibleExpressionConditionals.Syntax source expression)
    (found : source.lookupExpression? expression = some expressionNode)
    (sourceTyped : ExpressionHasType source sourceContext expression expressionNode.type)
    (scopeWF : CompatibleExpressionScalarNativeTyping.ScopeWellFormed values.checked.catalog.definitions scope)
    (extension : values.checked.catalog.definitions.Extends definitions)
    (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LanguageResult.resultType result) definitions := by
  obtain ⟨budget, lowered, generated, same, emitted⟩ := scalar_body_receipt read form accepted
  rw [callback] at generated
  have tree := CompatibleExpressionConditionals.tree_of_functions unique declarations ordinary coercions syntaxTree found sourceTyped generated
  obtain ⟨wellFormed, typed⟩ := CompatibleExpressionScalarNativeTyping.conditionals_native_at scopeWF administrative extension tree
  rw [same] at wellFormed typed
  rw [emitted]
  apply LocalControl.finish_hasType wellFormed (LocalLoop.toControl_hasType escaped wellFormed (LocalLoop.returnValue_hasType wellFormed typed))
  split
  · rename_i unitResult
    simpa only [unitResult] using
      (LanguageResult.success_hasType (HasType.unit (definitions := definitions)
        (context := SourceCoreLocalCell.coreContext scope ++ administrative)))
  · exact LanguageResult.failure_hasType wellFormed .word

private theorem scope_wellFormed {definitions : DataEnvironment} {scope : SourceCoreLocalCell.Scope}
    (all : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed definitions) :
    CompatibleExpressionScalarNativeTyping.ScopeWellFormed definitions scope := by
  induction scope with
  | nil => exact .empty _
  | cons head tail ih => exact (ih (fun binding member => all binding (List.mem_cons_of_mem _ member))).prepend head.1 (all head (by simp))

private theorem projected_parameters {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (packed (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := CompatibleExpressionReads.projectType_of_accepted (projected binding (by simp))
    cases rest with
    | nil => exact head
    | cons next tail =>
      have rest := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, rest]
      rfl

private theorem binder_projection {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerBinder checked source scope binder = .ok type) :
    SourceCoreCompatibleDataExpressions.projectType checked (.binder binder.id) binder.scheme.body = .ok type := by
  simp only [SourceCoreCompatibleDataExpressions.lowerBinder, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  exact accepted

/-- The actual contextual binder action supplies every checked projection.
Monomorphic admission is source metadata, not a fact recovered from native types. -/
theorem parameter_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {representation : SourceCoreGeneralFunctions.Representation} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} {policy : SourceCoreFunctions.Policy}
    {source : TypedSource} {scope finalScope : SourceCoreLocalCell.Scope}
    {parameters : List TypedBinder} {bindings : List CallableIndexedParameterCertificates.Binding}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (bindings, finalScope))
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals owner [])
    (ordinaryPolicy : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder checked)
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = []) :
    ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2 := by
  have tree := FunctionCode.Parameters.of_accepted accepted
  clear accepted
  induction tree with
  | nil => simp
  | @cons scope finalScope parameter parameters type bindings head tail ih =>
    rw [binderPolicy, SourceCoreGeneralFunctions.contextualBinder,
      monomorphic parameter (by simp), List.isEmpty_nil, if_pos rfl, ordinaryPolicy] at head
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact binder_projection head
    · exact ih (fun binder h => monomorphic binder (List.mem_cons_of_mem _ h)) binding member

/-- Static scalar source profile at the real body callback. Every expression
certificate is subsequently extracted from that callback's successful output;
no body or child native typing or execution field is stored here. -/
structure ScalarBody {checked : SourceCoreCompatibleCatalog.Checked}
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered) where
  loopPolicy : SourceCoreLoops.Policy
  callback : lowerBody (FunctionCode.children policy lowerBody fuel compilation) = SourceCoreLoops.lowerStatementsWithPolicy loopPolicy
  expressionCallback : loopPolicy.lowerExpression = FunctionCode.children policy lowerBody fuel compilation
  statement : StatementId
  statementNode : StatementNode
  statementType : Ty
  singleton : statements = [statement]
  expression : ExpressionId
  expressionNode : ExpressionNode
  read : loopPolicy.readStatement view statement = .ok (statementNode, statementType)
  form : statementNode.form = .returnStmt (some expression) ∨ statementNode.form = .expression expression false
  sourceContext : SourceSemantics.Context
  readFuel : Nat
  unique : NodeOccurrencesUnique view
  declarations : CompatibleExpressionReads.ScopeDeclarations view receipt.bodyScope sourceContext
  ordinary : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values view receipt.bodyScope reasonAt
  coercions : ∀ id node, CompatibleExpressionConditionals.Syntax view id → view.lookupExpression? id = some node → node.coercions = []
  syntaxTree : CompatibleExpressionConditionals.Syntax view expression
  found : view.lookupExpression? expression = some expressionNode
  sourceTyped : ExpressionHasType view sourceContext expression expressionNode.type

theorem scalar_certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (body : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (parameterProjections : ∀ binding ∈ receipt.loweredParameters, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have binderTree := FunctionCode.Parameters.of_accepted receipt.parametersCompiled
  have projected := projected_parameters receipt.loweredParameters parameterProjections
  have parameter := CompatibleExpressionReads.projectType_of_accepted (projector ▸ receipt.parameterProjected)
  have bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd) := by
    have sameTypes : receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        parameters.map (·.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binderTree.binders
    rw [sameTypes, receipt.parameterTypes] at projected
    exact Except.ok.inj (parameter.symm.trans projected)
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (parameterProjections binding member)
  have allBody : ∀ binding : Resolved.LocalId × Ty, binding ∈ receipt.bodyScope → binding.2.WellFormed checked.catalog.definitions := by
    rw [binderTree.scope]
    intro binding member
    rcases List.mem_append.mp member with fromParameters | fromScope
    · rcases List.mem_map.mp (List.mem_reverse.mp fromParameters) with ⟨parameter, parameterMember, sameBinding⟩
      rw [← sameBinding]
      exact parameterWF parameter parameterMember
    · exact scopeWF binding fromScope
  have accepted := receipt.bodyCompiled
  rw [body.callback] at accepted
  have accepted : SourceCoreLoops.lowerStatementsWithPolicy body.loopPolicy fuel view receipt.bodyScope
      [body.statement] receipt.resultCore reasonAt compilation.internalReason compilation.internalReason = .ok receipt.body :=
    by simpa only [body.singleton] using accepted
  have native := scalar_body_native body.expressionCallback body.read body.form accepted body.unique body.declarations
    body.ordinary body.coercions body.syntaxTree body.found body.sourceTyped
    (by simpa only [sameChecked] using scope_wellFormed allBody)
    (by simpa only [sameChecked] using (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix) administrative
  exact certificate_native prepared receipt projector allocation manifest expressionHook callables descriptor
    administrativePrefix bundle parameterWF ordinary scopeWF administrative current native



private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩


open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration

/-- The accepted contextual site is formed with native typing derived from its
actual scalar callback and parameter fold. The receipt below predates Code; it
contains compiler equations, not a native typing or body execution field.
Static callback profiles, source typing and frame placement remain explicit. -/
theorem of_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (scalar : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  have hook := receipt.expressionHook
  rw [expressionHook] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have projections := parameter_projections receipt.parametersCompiled binderPolicy (by rfl) monomorphic
  have ordinaryBindings : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    apply ordinaryParameters binding.1
    rw [← (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).binders]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have native := scalar_certificate_native prepared receipt values sameChecked scalar projector allocation manifest
    expressionHook callables descriptor rfl projections ordinaryBindings scopeWF administrative current
  exact CallableIndexedLambdaGeneration.of_contextual prepared compiled record sourceContext evidence captured profile
    viewOfSource sourceFound sourceForm found form owner requirements coercions ordinary read accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaImperativeNativeTyping
/-! General imperative lambda bodies use the actual statement compiler and
its native callback laws. The parameter fold, manifest, snapshot, descriptor
and generation history remain the production receipts. Concrete source and
callback admission, applied views and generalized parameters are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaImperativeNativeTyping
open Core Frontend SourceInference
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates CallableIndexedLambdaGeneration CallableIndexedNamedGeneration

/-- Static laws for the exact body callback and its actual entry scope. There
is no singleton/scalar restriction or whole-body typing/execution field. -/
structure BodyProfile {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (definitions : DataEnvironment) (administrative : Core.Context) where
  loops : SourceCoreLoops.Policy
  callback : lowerBody (FunctionCode.children policy lowerBody fuel compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy loops
  admitted : ImperativeNativePolicyTyping.Admission
  laws : ImperativeNativePolicyTyping.PolicyLaws definitions administrative admitted loops
  allowed : admitted view receipt.bodyScope

theorem body_native {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered}
    {definitions : DataEnvironment} {administrative : Core.Context}
    (profile : BodyProfile receipt definitions administrative)
    (wellFormed : receipt.resultCore.WellFormed definitions) :
    HasType (SourceCoreLocalCell.coreContext receipt.bodyScope ++ administrative) receipt.body
      (LanguageResult.resultType receipt.resultCore) definitions := by
  have accepted := receipt.bodyCompiled
  rw [profile.callback] at accepted
  exact ImperativeNativePolicyTyping.body_native profile.laws profile.allowed wellFormed accepted

private theorem projected_parameters {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (packed (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := CompatibleExpressionReads.projectType_of_accepted (projected binding (by simp))
    cases rest with
    | nil => exact head
    | cons next tail =>
      have rest := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, rest]
      rfl

theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (administrative : Core.Context) (profile : BodyProfile receipt prepared.layouts.definitions administrative)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (parameterProjections : ∀ binding ∈ receipt.loweredParameters, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have binderTree := FunctionCode.Parameters.of_accepted receipt.parametersCompiled
  have projected := projected_parameters receipt.loweredParameters parameterProjections
  have parameter := CompatibleExpressionReads.projectType_of_accepted (projector ▸ receipt.parameterProjected)
  have bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd) := by
    have sameTypes : receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        parameters.map (·.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binderTree.binders
    rw [sameTypes, receipt.parameterTypes] at projected
    exact Except.ok.inj (parameter.symm.trans projected)
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (parameterProjections binding member)
  have resultWF := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.resultProjected)).extend_definitions
    (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix
  exact CallableIndexedLambdaScalarNativeTyping.certificate_native prepared receipt projector allocation manifest expressionHook
    callables descriptor administrativePrefix bundle parameterWF ordinary scopeWF administrative current (body_native profile resultWF)

private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩

theorem of_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (contracts : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (profile : BodyProfile receipt prepared.layouts.definitions administrative)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  have hook := receipt.expressionHook
  rw [expressionHook] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ := CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have projections := CallableIndexedLambdaScalarNativeTyping.parameter_projections receipt.parametersCompiled binderPolicy (by rfl) monomorphic
  have ordinaryBindings : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    apply ordinaryParameters binding.1
    rw [← (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).binders]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have native := certificate_native prepared receipt administrative profile projector allocation manifest expressionHook
    callables descriptor rfl projections ordinaryBindings scopeWF current
  exact CallableIndexedLambdaGeneration.of_contextual prepared compiled record sourceContext evidence captured contracts
    viewOfSource sourceFound sourceForm found form owner requirements coercions ordinary read accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaImperativeNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticCalls
/-! Ordinary closure calls combine concrete lexical builtin bodies with the
actual indexed frame and marked parameter prefix. The lambda's generation
receipt and caller history remain semantic inputs. Completed native execution
constructs the independent source call; no body execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaSemanticInvocation
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

abbrev represented_closure := @CallableIndexedLambdaCalls.represented_closure
abbrev applyPayload := CallableIndexedLambdaCalls.applyPayload

variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment}
  (captured : Captures prepared mapping world scope function.captured capturedActual)
  (code : Code prepared function scope captured.administrative) (history : History code)
  {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
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
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (code.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((code.reasonAt id).add tag))

include extension uninitialized missing in
theorem Entry.preserves [FunctionCalls.FaultTokens faults]
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {copies environment : Dynamic.Environment} {copied bound after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (copy : Dynamic.EnvironmentCopies function.source function.captured before copies copied)
    (allocated : Dynamic.BindersAllocate copies copied function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function body.context environment bound outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy entry.entry.copy
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at trace
  have registered := CallableIndexedAmbient.frame_registered prepared
  obtain ⟨result, bodyStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    body.certificate.preserves (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
      (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile)
      entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
      entry.entry.reference entry.entry.read entry.entry.unmapped trace
  have maps := entry.entry.maps.trans maps
  have worlds := entry.entry.worlds.trans worlds
  have frame := entry.entry.frame.trans frame
  have metadata := entry.entry.metadata.trans metadata
  have bodyEval := entry.wrap evaluated
  have callEval : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result (bodyStore.set location (encode prepared.ancestry.layout.frame current)) :=
    .apply (.second (.first (.var rfl))) (.var rfl) bodyEval
  obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
    (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
      ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
  exact ⟨result, _, finalMap, finalWorld, callEval, related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include extension uninitialized missing in
theorem Entry.reflects [FunctionCalls.FaultTokens faults]
    (entry : Entry captured code history body profile registry arguments nativeArguments before store location current currentGhost)
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ copies copied environment bound outcome after finalMap finalWorld,
      Dynamic.EnvironmentCopies function.source function.captured before copies copied ∧
      Dynamic.BindersAllocate copies copied function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function body.context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  cases evaluated with
  | apply callee argument applied =>
    have expected : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.second (.first (.var 0)))
        (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
          (code.body.rename captured.embedding.lift.lift) (encode prepared.ancestry.layout.frame history.native :: capturedActual)) store :=
      .second (.first (.var rfl))
    obtain ⟨sameClosure, sameStore⟩ := evaluation_deterministic callee expected
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj sameClosure
    rw [sameStore] at argument
    obtain ⟨sameArgument, sameAfter⟩ := evaluation_deterministic argument
      (show Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store (.var 1) (DataPatternValues.packValues nativeArguments) store from .var rfl)
    rw [sameArgument, sameAfter] at applied
    obtain ⟨bodyStore, bodyEval, finalEq⟩ := entry.unwrap applied
    have registered := CallableIndexedAmbient.frame_registered prepared
    obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
      body.certificate.reflects (model prepared profile) extension rfl registered program body.valid body.unique uninitialized missing
        (identity_faithful prepared) (observations prepared profile) (runtime_views prepared profile)
        entry.entry.environments entry.entry.heaps entry.entry.locals entry.entry.lookups entry.entry.actualTyped
        entry.entry.reference entry.entry.read entry.entry.unmapped bodyEval
    have maps := entry.entry.maps.trans maps
    have worlds := entry.entry.worlds.trans worlds
    have frame := entry.entry.frame.trans frame
    have metadata := entry.entry.metadata.trans metadata
    obtain ⟨restoredHeap, restoredFrame, restoredCaller⟩ := CallableIndexedBodyFrames.restore registered entry.unmapped entry.referenceTyped
      (show CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost store from
        ⟨entry.currentRead, entry.currentHistory⟩) finalHeaps worlds frame
    subst finalStore
    exact ⟨entry.entry.copies, entry.entry.copiedHeap, entry.entry.environment, entry.entry.heap, outcome, after,
      finalMap, finalWorld, entry.entry.copy, entry.entry.allocation, trace,
      related, restoredHeap, maps, worlds, restoredFrame, metadata, restoredCaller⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem reflects [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {result : Value} {finalStore : Store}
    (evaluated : Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
      store applyPayload result finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  obtain ⟨copies, copied, environment, bound, outcome, after, finalMap, finalWorld, copy, allocated, trace, rest⟩ :=
    Entry.reflects captured code history body profile extension uninitialized missing entry evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace.call body.frame body.extended copy allocated, rest⟩

include body represented heaps locals reference read currentCarried unmapped allowed extension uninitialized missing in
theorem preserves [FunctionCalls.FaultTokens faults] {callerContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : FunctionCallBody.Outcome program callerContext callerEvidence function.evidence before (.closure function) arguments outcome after) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates [value code captured.embedding history.native capturedActual, DataPatternValues.packValues nativeArguments]
        store applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry (model prepared profile))
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry (model prepared profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location current currentGhost finalStore := by
  have arity : function.parameters.length = arguments.length := by rw [parameters code]; simpa using represented.length.1
  obtain ⟨types, context, copies, copied, environment, bound, extended, copy, allocated, trace⟩ :=
    FunctionCallBody.Outcome.trace arity executed
  have sameTypes : types = body.types := extended.bodyTypes_eq.symm.trans body.extended.bodyTypes_eq
  subst types
  have sameContext := extended.functional body.extended
  subst context
  obtain ⟨entry⟩ := entry_exists captured code history body profile represented heaps locals reference read currentCarried unmapped allowed
  exact Entry.preserves captured code history body profile extension uninitialized missing entry copy allocated trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticCalls
end
