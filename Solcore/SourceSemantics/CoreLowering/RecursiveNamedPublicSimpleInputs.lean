import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderParameterProjections

/-! Scalar and product arguments obtain their independent source representation
from the actual public encoder. This bounded input family does not include
handles or metadata-bearing data. Full Header provenance and its actual raw
parameter projections remain explicit; native typing does not identify source
declarations, captured environments or authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open CallableIndexedParameterCertificates

inductive Means : SourceCorePublicValues.Value → Dynamic.Value → Prop where
  | unit : Means .unit .unit
  | bool (value : Bool) : Means (.bool value) (.bool value)
  | word (value : Word) : Means (.word value) (.word value)
  | integer (value : Int) : Means (.integer value) (.integer value)
  | product {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
      (leftMeaning : Means left first) (rightMeaning : Means right second) :
      Means (.product left right) (.product first second)

inductive Meanings : List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
  | nil : Meanings [] []
  | cons {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
      {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
      (head : Means value source) (tail : Meanings values sources) :
      Meanings (value :: values) (source :: sources)

theorem Means.functional {value : SourceCorePublicValues.Value} {first second : Dynamic.Value}
    (left : Means value first) (right : Means value second) : first = second := by
  induction left generalizing second with
  | unit => cases right; rfl
  | bool => cases right; rfl
  | word => cases right; rfl
  | integer => cases right; rfl
  | product _ _ left rightIH =>
    cases right with
    | product first second => rw [left first, rightIH second]

theorem SimpleInput.represents {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {native : Core.Value}
    (input : SourceCoreIndexedSession.SimpleInput expected value native) :
    ∃ source type, Means value source ∧
      ValueRep checked registry functions mapping world expected source native type := by
  induction input with
  | unit view => exact ⟨_, _, .unit, .compatible (CompatibleEncoding.runtime_view view) .unit⟩
  | bool value view => exact ⟨_, _, .bool value, .compatible (CompatibleEncoding.runtime_view view) (.bool value)⟩
  | word value view => exact ⟨_, _, .word value, .compatible (CompatibleEncoding.runtime_view view) (.word value)⟩
  | integer value view => exact ⟨_, _, .integer value, .compatible (CompatibleEncoding.runtime_view view) (.integer value)⟩
  | product view _ _ first second =>
    obtain ⟨left, leftType, leftMeaning, leftRep⟩ := first
    obtain ⟨right, rightType, rightMeaning, rightRep⟩ := second
    exact ⟨_, _, .product leftMeaning rightMeaning,
      .compatible (CompatibleEncoding.runtime_view view) (.product leftRep rightRep)⟩

/-- Actual binder projections choose the native payload type for each retained
raw source type. The source value comes from the encoder's structural receipt. -/
theorem SimpleInputs.arguments {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    {bindings : List Binding} {values : List SourceCorePublicValues.Value} {native : Core.Environment}
    (inputs : SourceCoreIndexedSession.SimpleInputs
      (bindings.map (fun binding => binding.1.scheme.body)) values native)
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd)) :
    ∃ sources, Meanings values sources ∧
      CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world bindings sources native := by
  induction bindings generalizing values native with
  | nil => cases inputs; exact ⟨[], .nil, .nil⟩
  | cons binding bindings ih =>
    cases inputs with
    | cons head tail =>
      obtain ⟨type, rest, projectedHead, projectedTail, same⟩ := CompatibleEncoding.project_cons projected
      obtain ⟨sameType, sameRest⟩ := List.cons.inj same
      rw [← sameType] at projectedHead
      rw [← sameRest] at projectedTail
      obtain ⟨source, nativeType, meaning, represented⟩ := SimpleInput.represents (registry := registry) functions mapping world head
      have nativeTypeEq := Except.ok.inj (represented.projection.symm.trans projectedHead)
      subst nativeType
      obtain ⟨sources, meanings, representedTail⟩ := ih tail projectedTail
      exact ⟨source :: sources, .cons meaning meanings, .cons represented representedTail⟩

/-- The original startup equation fixes the same first root and complete
native prefix used by StartAt, before any source interpretation is attached. -/
theorem StartAt.simple_inputs {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    (simple : ∀ argument ∈ arguments, SimplePublic argument) :
    SourceCoreIndexedSession.SimpleInputs root.inputs arguments native := by
  have receipt := started.original.simple_inputs simple
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, inputs, _, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  have original := started.initial
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values owner
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact inputs

/-- Public scalar/product encoding now supplies Source Arguments. Program
validity and exact specialization selection supply the real Header's raw
projections; no input representation callback is required for this family. -/
theorem StartAt.simple_arguments {artifact : Artifact} {session : Session artifact}
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
    (simple : ∀ argument ∈ publicArguments, SimplePublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    ∃ arguments, Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        mapping world header.bindings arguments native := by
  have inputs := StartAt.simple_inputs started simple
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1] at inputs
  exact SimpleInputs.arguments functions mapping world inputs
    (RecursiveNamedHeaderParameterProjections.projections_of_record header sameChecked programTyped record)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
