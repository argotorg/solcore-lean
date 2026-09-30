import Solcore.SourceSemantics.CoreLowering.DataPlaceReadTotality

/-! Reflection of any completed generated selector from an authenticated
present root. The independent source read/fault is constructed, not assumed.
Fault tokens remain actual generated results; their site-table interpretation
is a separate diagnostic obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataEquality

/-- Success retains the exact full leaf relation; failure retains an
independent source fault and the exact returned Core word. No source trace or
child/helper evaluation is an assumption of this reflection theorem. -/
theorem reflects {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities)
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection}
    {coreTypes : List Ty}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    {sourceRoot : Dynamic.Value} {coreRoot : Value}
    (rootRelated : ValueRep checked.catalog signatures functions mapping world root sourceRoot coreRoot rootType)
    {environment : Environment} {before after : Store} {current keys : Expr} {result : Value}
    (rootSelected : Selects environment current coreRoot)
    (keysSelected : Selects environment keys (packValues values))
    (completed : Evaluates environment before (select prepared prepared.steps current keys) result after) :
    ∃ administrative count,
      after = before ++ administrative ∧ administrative.length ≤ count ∧
      DataPayloadReadPaths.Path checked signatures functions mapping world values root rootType
        prepared.steps evaluated leaf leafType count ∧
      ((∃ selected value, Dynamic.ProjectionsRead (some sourceRoot) evaluated (some selected) ∧
          ValueRep checked.catalog signatures functions mapping world leaf selected value leafType ∧
          result = .inRight .word (.inRight .unit value)) ∨
        ∃ reason token, Dynamic.ProjectionsFaults (some sourceRoot) evaluated reason ∧
          result = .inLeft prepared.optionalLeaf (.word token)) := by
  obtain ⟨count, semanticPath⟩ := path.prepared_path preparation shaped keysRelated (allKeys := values)
    (by intro index value selected; simpa only [Nat.zero_add] using selected)
  rcases DataPlaceReadTotality.read_or_fault functionTypes layouts path preparation shaped keysRelated rootRelated with
      ⟨selected, value, read, related⟩ | ⟨reason, fault⟩
  · have tree := semanticPath.read_tree observations layouts prepared rootRelated read
    obtain ⟨actual, finalStore, administrative, _, actualRelated, ran, appended, length⟩ :=
      tree.preserves faithful keyLength environment before current keys rootSelected keysSelected
    have same := evaluation_deterministic completed ran
    rcases same with ⟨rfl, rfl⟩
    exact ⟨administrative, count, appended, by omega, semanticPath,
      .inl ⟨selected, actual, read, actualRelated, rfl⟩⟩
  · obtain ⟨token, finalStore, administrative, ran, _, appended, length⟩ :=
      semanticPath.fault_preserves observations faithful layouts prepared keyLength rootRelated fault
        environment before current keys .unit rootSelected keysSelected
    have same := evaluation_deterministic completed ran
    rcases same with ⟨rfl, rfl⟩
    exact ⟨administrative, count, appended, length, semanticPath, .inr ⟨reason, token, fault, rfl⟩⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
