import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaManifest
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody
import Solcore.SourceSemantics.CoreLowering.NamedCallMeaning

/-! Ordinary lambda entry uses the formation receipt's actual capture and
code, installs its authenticated lexical state, and constructs the parameter
prefix. The concrete body certificate is static; it contains no body run. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where
  source : code.view = function.source
  frame : Dynamic.ClosureFrame program function
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  kinds : ∀ binding ∈ code.receipt.loweredParameters,
    function.source.inputs.any (fun input => decide (input.id = binding.1.id)) = false
  referenceIndex : code.referenceIndex = scope.length + 1 + prepared.base.globals.length
  readFuel : Nat
  policy : SourceCoreLoops.Policy
  bodyFuel : Nat
  certificate : BuiltinNamedBody.Certificate prepared.layouts code.compilation.owner code.active
    prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError readFuel values
    function.source context code.compilation.solvedRequirements code.reasonAt
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body function.resultType code.receipt.resultCore policy bodyFuel code.compilation.internalReason
    code.compilation.internalReason code.receipt.body
  valid : CompatibleExpressionLiterals.ContextValid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source

theorem parameters {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    function.parameters = code.receipt.loweredParameters.map Prod.fst :=
  (FunctionCode.Parameters.of_accepted code.receipt.parametersCompiled).binders.symm

theorem prefix_accepted {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (source : code.view = function.source) :
    SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
        (prepared.layouts.allocatorAt code.compilation.owner code.active code.allocationError))
      function.source scope code.receipt.loweredParameters code.receipt.resultCore SourceCoreFunctions.argumentProjection
      (code.receipt.body.weakenAt code.receipt.loweredParameters.length) = .ok code.receipt.allocatedBody := by
  have accepted := code.receipt.allocated
  simpa only [CallableIndexedLambdaCertificates.parameterBody, code.allocationProfile, source] using accepted

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

structure Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) where private mk ::
  next : NativeFrame
  nextHistory : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next
    (.lambda code.descriptor.id history.ghost) (some history.metadata)
  actual : Environment
  actualContext : Core.Context
  embedding : Renaming
  entry : CallableIndexedLambdaPrefix.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values
    (model prepared profile) registry function body.context scope code.receipt.loweredParameters arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world captured.administrative
    actualContext actual embedding code.receipt.allocatedBody code.receipt.body
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
    captured.represented actualLayout descriptor fields code.receipt.allocatedBody (store.set location (encode layout next))
  obtain ⟨entry⟩ := CallableIndexedLambdaPrefix.entry_of_accepted (model prepared profile) code.allocationError
    (prefix_accepted code body.source) (parameters code) body.kinds body.extended rfl registered represented
    captured.represented installedHeaps locals (GenericExpressionMeaning.agree_prefix actualLayout manifest)
    (.cons manifestTyped actualTyped) (body.referenceIndex ▸ reference) installedCurrent.read unmapped
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
  refine ⟨⟨next, nextHistory, _, _, _, entry, ?_, ?_, unmapped, refTyped, .stable currentCarried, read⟩⟩
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaInvocation
