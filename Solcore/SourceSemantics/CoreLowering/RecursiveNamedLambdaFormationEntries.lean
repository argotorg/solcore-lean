import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeValues

/-! Formation entries keep independent named history and the real canonical
frame reference alongside the complete catalog authority. They transport only
through the original effects and binder operations. An arbitrary BodyState,
a native frame type, or a descriptor lookup does not construct this receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

variable {values : ValuesContext} (indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked)
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory indexed.ancestry values ambient.definitions program} {locations : Locations}
  {capturePrefix callerPrefix : Nat}
  {caller : Header indexed.ancestry values ambient.definitions program}

/-- Actual preparation data fixes the complete specialization and the compiler
context used by lambda sites. Global captures remain full ordered captures. -/
structure FormationHeader (caller : Header indexed.ancestry values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (capturePrefix : Nat) : Prop where
  record : SourceCompilationPlan.exactSpecialization indexed.base.plan caller.named.signature.key = .ok caller.named.specialized
  context : compilation = CallableIndexedNamedGeneration.context indexed caller.named
  source : caller.function.source = CallableIndexedNamedGeneration.source caller.named
  layouts : caller.layouts = indexed.layouts
  owner : caller.owner = caller.named.signature.key
  active : caller.active = []
  globals : caller.globals = indexed.base.globals.length
  capture : capturePrefix = 0

/-- The carried metadata has the original named source, owner and substitution;
the separate catalog retains full global closure authority and snapshots. -/
structure Entry (caller : Header indexed.ancestry values ambient.definitions program)
    (headers : Inventory indexed.ancestry values ambient.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values) (ambient := ambient) (program := program)) (capturePrefix callerPrefix : Nat)
    (scope : SourceCoreLocalCell.Scope) (mapping : LocationMap) (world : StoreTyping)
    (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical
  origin : Word
  owned : indexed.ancestry.graph.inputs.callable.table.idAt? (.named caller.named.signature.key) = some origin
  ghost : catalog.authority.ghost = .named origin
  history : Carries indexed.ancestry.graph.inputs indexed.ancestry.graph.table catalog.authority.current
    (.named origin) (some (CallableIndexedNamedGeneration.state caller.named))
  bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType
  reference : canonical[scope.length + 1 + caller.globals]? =
    some (.cellRef indexed.ancestry.layout.frame.type catalog.authority.frameLocation)

def protectedEntry (caller : Header indexed.ancestry values ambient.definitions program)
    (headers : Inventory indexed.ancestry values ambient.definitions program)
    (locations : Locations (prepared := indexed.ancestry) (values := values) (ambient := ambient) (program := program)) (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (Entry indexed caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

variable {indexed}

def Entry.extend {scope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
    {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : Entry indexed caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Entry indexed caller headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds preserved metadata }

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry indexed caller headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry indexed caller headers locations capturePrefix callerPrefix) := by
  constructor
  · intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{
      catalog := ⟨entry.catalog.authority, ?_⟩
      origin := entry.origin
      owned := entry.owned
      ghost := entry.ghost
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
      origin := entry.origin
      owned := entry.owned
      ghost := entry.ghost
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
    (entry : protectedEntry indexed caller headers locations capturePrefix callerPrefix scope mapping world heap store canonical) :
    RecursiveNamedCatalog.protectedEntry headers locations capturePrefix callerPrefix scope mapping world heap store canonical := by
  obtain ⟨entry⟩ := entry
  exact ⟨entry.catalog⟩

variable (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)

/-- The aligned body predicate keeps the actual source frame and its canonical
physical reference. It imposes no execution law on the body. -/
def BodyAligned : BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry caller :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} entry =>
    protectedEntry indexed caller headers locations capturePrefix (capturePrefix + 1)
      (caller.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical

/-- Only actual named hook output and its carried original metadata construct
an aligned callee state. Full specialization fixes every metadata field. -/
theorem authorize {compilation : SourceCoreFunctions.Context}
    (header : FormationHeader indexed caller compilation capturePrefix) :
    BodyAuthorization (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      functions registry caller (BodyAligned functions registry) := by
  intro origin index metadata arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation owned history _ entry
  have seed := CallableIndexedNamedGeneration.seed indexed owned header.record
  have generated : SourceCoreCallableAncestryPairedPreparation.named? indexed.ancestry.graph.inputs origin = some metadata := by
    cases history.authenticates with
    | named generated => exact generated
  have same : metadata = CallableIndexedNamedGeneration.state caller.named := Option.some.inj (generated.symm.trans seed)
  subst metadata
  refine ⟨{
    catalog := entry.catalog
    origin := origin
    owned := owned
    ghost := entry.catalog_ghost
    history := ?_
    bundle := ?_
    reference := ?_ }⟩
  · simpa only [entry.catalog_current] using history
  · have typed := entry.environments.runtime_hasTypes.type_tags
    rw [typed, ← caller.parameterType]
    simp [SourceCoreLocalCell.coreContext]
  · simpa only [List.length_map, List.length_reverse, entry.catalog_frame] using entry.reference

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationEntries
