import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationEntries

/-! A generic caller keeps the actual current ghost, full carried named-source
metadata, physical frame and ordered catalog. Its history may be named or lambda;
no named-frame cast or native typing supplies source provenance. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedFormationEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
variable {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program}
  {locations : Locations (prepared := indexed.ancestry) (values := values)
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)}
  {scope : SourceCoreLocalCell.Scope} {capturePrefix callerPrefix : Nat}

/-- The carried metadata has the original named source, owner and substitution;
the separate catalog retains full global closure authority and snapshots. -/
structure Entry (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values) (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)) (capturePrefix callerPrefix : Nat)
    (scope : SourceCoreLocalCell.Scope) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical
  history : Carries indexed.ancestry.graph.inputs indexed.ancestry.graph.table catalog.authority.current
    catalog.authority.ghost (some (CallableIndexedNamedGeneration.state caller.named))
  bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType
  reference : canonical[scope.length + 1 + caller.globals]? =
    some (.cellRef indexed.ancestry.layout.frame.type catalog.authority.frameLocation)

def protectedEntry (caller : Header indexed.ancestry values indexed.layouts.definitions program)
    (headers : Inventory indexed.ancestry values indexed.layouts.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values) (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (program := program)) (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (Entry caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical)


def Entry.extend {scope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : Entry caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry caller headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds preserved metadata }

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry caller headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry caller headers locations capturePrefix callerPrefix) := by
  constructor
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{
      catalog := ⟨entry.catalog.authority, ?_⟩
      history := entry.history
      bundle := ?_
      reference := ?_ }⟩
    · intro header member
      have found := entry.catalog.globals header member
      have pos : ((id, type) :: scope).length + callerPrefix + header.slot =
          (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [pos, List.getElem?_cons_succ] using found
    · simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using entry.bundle
    · have pos : ((id, type) :: scope).length + 1 + caller.globals =
          (scope.length + 1 + caller.globals) + 1 := by simp only [List.length_cons]; omega
      simpa only [pos, List.getElem?_cons_succ] using entry.reference
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{
      catalog := ⟨entry.catalog.authority, ?_⟩
      history := entry.history
      bundle := ?_
      reference := ?_ }⟩
    · intro header member
      have found := entry.catalog.globals header member
      have pos : ((id, type) :: scope).length + callerPrefix + header.slot =
          (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [pos, List.getElem?_cons_succ] using found
    · have found := entry.bundle
      simpa only [List.map_cons, List.length_cons, List.getElem?_cons_succ] using found
    · have found := entry.reference
      have pos : ((id, type) :: scope).length + 1 + caller.globals =
          (scope.length + 1 + caller.globals) + 1 := by simp only [List.length_cons]; omega
      simpa only [pos, List.getElem?_cons_succ] using found

theorem catalog {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
    (entry : protectedEntry caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical) :
    RecursiveNamedCatalog.protectedEntry headers locations capturePrefix callerPrefix scope mapping world heap store canonical := by
  obtain ⟨entry⟩ := entry
  exact ⟨entry.catalog⟩

/-- The old named receipt is the same state with a more specific ghost. -/
def Entry.of_named {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (entry : RecursiveNamedLambdaFormationEntries.Entry (ambient := CallableIndexedAmbient.ambientDefinitions indexed)
      indexed caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical) :
    Entry caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical := {
  catalog := entry.catalog
  history := by rw [entry.ghost]; exact entry.history
  bundle := entry.bundle
  reference := entry.reference }

/-- An actual lambda prefix retains its own ghost. Full metadata equality is
an independent source receipt, rather than a conclusion from native typing. -/
def Entry.of_lambda {function : Dynamic.Closure} {outerScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code indexed function outerScope administrative}
    {history : History code} {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (entry : CallableIndexedLambdaCatalogEntries.SourceEntry code history headers locations capturePrefix callerPrefix
      scope mapping world heap store canonical)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state caller.named)
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = indexed.base.globals.length) :
    Entry caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical := {
  catalog := entry.catalog
  history := by rw [entry.ghost]; simpa only [metadata] using entry.carried
  bundle := bundle
  reference := by simpa only [globals] using entry.reference }

/-- The caller bundle tag comes from the actual reached environment relation.
The rest of the native environment, including every unused suffix, is retained. -/
theorem bundle_of_environment {mapping : LocationMap} {world : StoreTyping}
    {administrative : Core.Context} {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical indexed.layouts.definitions)
    (leading : administrative[0]? = some caller.named.signature.parameterType) :
    (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType := by
  rw [related.runtime_hasTypes.type_tags]
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using leading

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedFormationEntries
