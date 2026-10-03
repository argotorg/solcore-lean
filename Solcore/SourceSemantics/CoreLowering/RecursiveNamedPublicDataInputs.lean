import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections
import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload
import Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping

/-! Actual public data input encoding supplies independent source arguments.
Constructors retain their complete raw metadata, mappings retain entry order
and their transported default, and proxies retain their raw inner types.
Opaque handles need separate capture, history and authority representation.
This boundary retains the actual first root, native prefix and final registry.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open CallableIndexedParameterCertificates

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

private theorem codebook_ambient {ambient : DataEnvironment}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory} {first : Nat}
    {prepared : SourceCoreAllocationCodebook.Prepared}
    (accepted : SourceCoreAllocationCodebook.prepare ambient inventories first = .ok prepared) :
    prepared.ambient = ambient := by
  unfold SourceCoreAllocationCodebook.prepare at accepted
  split at accepted
  · obtain ⟨_, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
    dsimp only at accepted
    split at accepted
    · obtain ⟨_, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
      split at accepted
      · cases accepted; rfl
      · split at accepted
        · cases accepted
        · split at accepted <;> cases accepted
    · cases accepted
  · cases accepted

private theorem map_ok {α β ε : Type} {first : Except ε α} {f : α → β} {value : β}
    (accepted : first.map f = .ok value) : ∃ input, first = .ok input ∧ f input = value := by
  cases first with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, Except.ok.inj accepted⟩

private theorem ancestry_ambient {ambient : DataEnvironment}
    {layout : SourceCoreCallableIndexedAncestry.Layout}
    (accepted : SourceCoreCallableIndexedAncestry.Layout.prepare ambient = .ok layout) :
    layout.ambient = ambient := by
  unfold SourceCoreCallableIndexedAncestry.Layout.prepare at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private theorem layouts_ambient {initial : SourceCoreAllocationDiscovery.Prepared} {fuel : Nat} {expression : Expr}
    {discovered : SourceCoreAllocationDiscovery.Discovered initial fuel expression}
    {prepared : SourceCoreAllocationLayouts.Prepared}
    (accepted : SourceCoreAllocationLayouts.prepare discovered = .ok prepared) :
    prepared.codebook.ambient = discovered.codebook.ambient := by
  unfold SourceCoreAllocationLayouts.prepare at accepted
  dsimp only at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted; rfl
      · cases accepted
    · cases accepted
  · cases accepted

private theorem compiled_prefix (compiled : SourceCoreUnifiedCompilation.Compiled) :
    compiled.compatible.checked.catalog.definitions.Extends compiled.indexed.layouts.definitions := by
  have ancestry := ancestry_ambient compiled.indexed.ancestry.layoutPrepared
  have discovery := compiled.indexed.discoveryPrepared
  unfold SourceCoreAllocationDiscovery.prepare at discovery
  obtain ⟨metadata, generated, sameMetadata⟩ := map_ok discovery
  have discoveryAmbient : compiled.indexed.discovery.ambient = compiled.indexed.ancestry.layout.definitions := by
    rw [← sameMetadata]
    exact codebook_ambient generated
  have discoveredAmbient := codebook_ambient compiled.indexed.discovered.checked
  have finalAmbient := layouts_ambient compiled.indexed.layoutsPrepared
  unfold SourceCoreAllocationLayouts.Prepared.definitions
  rw [finalAmbient, discoveredAmbient, discoveryAmbient]
  apply DataEnvironment.Extends.trans (second := compiled.indexed.ancestry.layout.definitions)
  · simpa only [SourceCoreCallableIndexedAncestry.Layout.definitions, ancestry] using
      DataEnvironment.Extends.append compiled.compatible.checked.catalog.definitions
        [compiled.indexed.ancestry.layout.frame.definition]
  · exact DataEnvironment.Extends.append _ _

/-- The public data carrier has the same independent interpretation as its
structural data codec image, including every raw metadata field. -/
def Means (value : SourceCorePublicValues.Value) (source : Dynamic.Value) : Prop :=
  ∃ carrier, value = DataInput.publicValue carrier ∧ DataPayloadEncoding.Means carrier source

inductive Meanings : List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
  | nil : Meanings [] []
  | cons {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
      {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
      (head : Means value source) (tail : Meanings values sources) :
      Meanings (value :: values) (source :: sources)

theorem EncodedDataInput.represents {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {native : Core.Value} {type : Core.Ty}
    (input : SourceCoreIndexedSession.EncodedDataInput checked registry expected value native)
    (projected : checked.catalog.project expected = .ok type)
    {future : DataEnvironment} (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeValueHasType world native type future) :
    ∃ source, Means value source ∧ ValueRep checked registry functions mapping world expected source native type := by
  obtain ⟨carrier, fuel, before, encoded, image, owner, accepted, same, extended⟩ := input
  have baseTyped := CompatibleEncodedDataTyping.encodeRaw_restrict_typing accepted projected extension (same.symm ▸ typed)
  obtain ⟨source, meaning, represented⟩ := CompatibleEncoding.encodeRaw_represents
    (functions := noFunctions checked.catalog) (mapping := mapping) owner accepted projected baseTyped
  refine ⟨source, ⟨carrier, image, meaning⟩, ?_⟩
  rw [same] at represented
  exact (represented.extend extended (.refl _) (.refl _)).map_functions
    (initial := noFunctions checked.catalog) (future := functions) (fun impossible => False.elim impossible)

theorem EncodedDataInputs.arguments {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    {bindings : List Binding} {values : List SourceCorePublicValues.Value} {native : Core.Environment}
    (inputs : SourceCoreIndexedSession.EncodedDataInputs checked registry
      (bindings.map (fun binding => binding.1.scheme.body)) values native)
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    {future : DataEnvironment} (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeEnvironmentHasTypes world native (bindings.map Prod.snd) future) :
    ∃ sources, Meanings values sources ∧
      CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world bindings sources native := by
  induction bindings generalizing values native with
  | nil => cases inputs; exact ⟨[], .nil, .nil⟩
  | cons binding bindings ih =>
    cases inputs with
    | cons head tail =>
      cases typed with
      | cons headTyped tailTyped =>
        obtain ⟨type, rest, projectedHead, projectedTail, same⟩ := CompatibleEncoding.project_cons projected
        obtain ⟨sameType, sameRest⟩ := List.cons.inj same
        rw [← sameType] at projectedHead
        rw [← sameRest] at projectedTail
        obtain ⟨source, meaning, represented⟩ := EncodedDataInput.represents functions mapping world head projectedHead extension headTyped
        obtain ⟨sources, meanings, representedTail⟩ := ih tail projectedTail tailTyped
        exact ⟨source :: sources, .cons meaning meanings, .cons represented representedTail⟩

/-- Equality of the original checkpoint state and values fixes its entire
encoded native prefix and final registry. Neither native tags nor key identity
replace the actual first-find root selection. -/
theorem StartAt.data_inputs {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    (data : ∀ argument ∈ arguments, DataPublic argument) :
    SourceCoreIndexedSession.EncodedDataInputs recipe.compiled.compatible.checked encodedValues.registry
      root.inputs arguments native ∧
    root.inputs.mapM recipe.compiled.compatible.checked.catalog.project = .ok root.types := by
  have receipt := started.original.data_inputs data
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, inputs, projected, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  have original := started.initial
  have actualValues := started.values
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values owner
  change values = encodedValues at actualValues
  change SourceCoreIndexedSession.EncodedDataInputs actualRecipe.compiled.compatible.checked values.registry
    root.inputs arguments encodedPrefix at inputs
  rw [actualValues] at inputs
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact ⟨inputs, projected⟩

/-- Actual public encoding plus the selected Header's raw projections supplies
source arguments for all recursively handle-free data. Caller Entry, source
heap representation and staging remain separate from this input theorem. -/
theorem StartAt.data_arguments {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient) (mapping : LocationMap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (data : ∀ argument ∈ publicArguments, DataPublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    ∃ arguments, Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        mapping world header.bindings arguments native := by
  obtain ⟨inputs, actualProjection⟩ := StartAt.data_inputs started data
  have headerProjection := RecursiveNamedHeaderParameterProjections.projections_of_record header sameChecked programTyped record
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1] at inputs actualProjection
  have inputs' : SourceCoreIndexedSession.EncodedDataInputs values.checked encodedValues.registry
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments native := by
    simpa only [sameChecked] using inputs
  have actualProjection' : (header.bindings.map (fun binding => binding.1.scheme.body)).mapM
      values.checked.catalog.project = .ok root.types := by
    simpa only [sameChecked] using actualProjection
  have nativeTypes := Except.ok.inj (actualProjection'.symm.trans headerProjection)
  have typed := started.typed
  rw [nativeTypes] at typed
  have extension : values.checked.catalog.definitions.Extends recipe.compiled.indexed.layouts.definitions := by
    simpa only [sameChecked] using compiled_prefix recipe.compiled
  exact EncodedDataInputs.arguments functions mapping world inputs' headerProjection extension typed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
