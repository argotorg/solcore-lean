import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation

/-! Ordinary lambda entry uses the formation receipt's actual capture and
code, installs its authenticated lexical state, and constructs the parameter
prefix. The concrete body certificate is static; it contains no body run. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

structure Body {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) where
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

/-- The original compiler certificate still supplies its canonical static
body receipt. The public Body record and its original accepted field are retained. -/
def Body.semantic {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {administrative : Core.Context}
    {code : Code prepared function scope administrative} {program : Program}
    (body : Body code program) : CallableIndexedLambdaSemanticInvocation.Body code program :=
  { context := body.context, types := body.types, extended := body.extended,
    kinds := body.kinds, referenceIndex := body.referenceIndex, frame := body.frame,
    readFuel := body.readFuel, certificate := body.certificate.semantic, valid := body.valid, unique := body.unique }

abbrev parameters := @CallableIndexedLambdaEntryPrefix.parameters
abbrev prefix_accepted := @CallableIndexedLambdaEntryPrefix.prefix_accepted
abbrev bodyEmbedding := CallableIndexedLambdaEntryPrefix.bodyEmbedding

abbrev Entry {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
    {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
    {capturedActual : Environment}
    (captured : Captures prepared mapping world scope function.captured capturedActual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {program : Program} (body : Body code program) (profile : values.checked.catalog.callableContracts = true)
    (registry : SourceCoreRawMetadata.Registry) (arguments : List Dynamic.Value) (nativeArguments : List Value)
    (before : Dynamic.Heap) (store : Store) (location : Location) (current : NativeFrame) (currentGhost : GhostFrame) :=
  CallableIndexedLambdaSemanticInvocation.Entry captured code history body.semantic profile registry arguments nativeArguments
    before store location current currentGhost

/- Fully qualified field access remains available for the original Entry. -/
section EntryFields
variable {values : SourceCoreCompatibleValues.Context} {prepared : Prepared values.checked}
  {function : Dynamic.Closure} {scope : Scope} {mapping : LocationMap} {world : StoreTyping}
  {capturedActual : Environment} {captured : Captures prepared mapping world scope function.captured capturedActual}
  {code : Code prepared function scope captured.administrative} {history : History code}
  {program : Program} {body : Body code program} {profile : values.checked.catalog.callableContracts = true}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}

abbrev Entry.next (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.next entry
abbrev Entry.nextHistory (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.nextHistory entry
abbrev Entry.actual (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.actual entry
abbrev Entry.actualContext (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.actualContext entry
abbrev Entry.embedding (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.embedding entry
abbrev Entry.entry (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.entry entry
abbrev Entry.wrap (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) {result : Value} {bodyStore : Store} :=
  CallableIndexedLambdaEntryPrefix.Entry.wrap (result := result) (bodyStore := bodyStore) entry
abbrev Entry.unwrap (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) {result : Value} {finalStore : Store} :=
  CallableIndexedLambdaEntryPrefix.Entry.unwrap (result := result) (finalStore := finalStore) entry
abbrev Entry.unmapped (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.unmapped entry
abbrev Entry.referenceTyped (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.referenceTyped entry
abbrev Entry.currentHistory (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.currentHistory entry
abbrev Entry.currentRead (entry : Entry captured code history body profile registry arguments nativeArguments
    before store location current currentGhost) := CallableIndexedLambdaEntryPrefix.Entry.currentRead entry
end EntryFields

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
  exact CallableIndexedLambdaSemanticInvocation.entry_exists captured code history body.semantic profile
    represented heaps locals reference read currentCarried unmapped allowed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewInvocation
