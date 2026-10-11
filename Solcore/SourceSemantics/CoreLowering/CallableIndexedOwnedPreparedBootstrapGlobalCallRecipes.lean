import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts

/-! A positive global recipe retains one capture from the actual bootstrap as
an explicit seed. Every reached recipe extends that same seed capture.
No broad global value representation is inverted into bootstrap provenance. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key NamedCapture NamedInstalledCode NamedSourceAt)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- One bootstrap capture and its installed code remain a literal witness.
Every reached Recipe is indexed by this same seed, preserving carrier identity. -/
structure Seed (origin : NamedOwner (headers := headers) keys functions registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  member : header ∈ headers
  initialCapture : NamedCapture headers origin.owner.key header [] origin.world
  installed : NamedInstalledCode initialCapture

/-- The real bootstrap producer supplies one seed inside a proposition.
No Type-valued choice is made by a public definition. -/
theorem Seed.of_bootstrap (origin : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : header ∈ headers) : Nonempty (Seed functions origin header) := by
  obtain ⟨capture, installed⟩ := origin.named_capture member
  exact ⟨⟨member, capture, installed⟩⟩

/-- Map/world growth retains the same bootstrap seed and full capture. -/
structure Recipe (origin : NamedOwner (headers := headers) keys functions registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (seed : Seed functions origin header)
    (mapping : LocationMap) (world : StoreTyping) where
  member : header ∈ headers
  maps : LocationMap.Extends [] mapping
  worlds : WorldExtends origin.world world

namespace Recipe
variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {origin : NamedOwner (headers := headers) keys functions registry}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {seed : Seed functions origin header}
  {mapping : LocationMap} {world : StoreTyping}

/-- This is the retained original bootstrap witness, independent of reached map/world. -/
def initialCapture (_recipe : Recipe functions origin header seed mapping world) :
    NamedCapture headers origin.owner.key header [] origin.world := seed.initialCapture

theorem installed (recipe : Recipe functions origin header seed mapping world) :
    NamedInstalledCode recipe.initialCapture := seed.installed

def capture (recipe : Recipe functions origin header seed mapping world) :
    NamedCapture headers origin.owner.key header mapping world :=
  recipe.initialCapture.extend recipe.maps recipe.worlds

def carrier (recipe : Recipe functions origin header seed mapping world)
    (identity descriptor : Word) : Value :=
  CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier
    origin.owner recipe.capture identity descriptor

/-- Reached growth changes only admission fields and preserves the literal seed. -/
theorem extend (recipe : Recipe functions origin header seed mapping world)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    Recipe functions origin header seed futureMap futureWorld :=
  ⟨recipe.member, recipe.maps.trans maps, recipe.worlds.trans worlds⟩

theorem carrier_extend (recipe : Recipe functions origin header seed mapping world)
    {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (identity descriptor : Word) :
    (recipe.extend maps worlds).carrier identity descriptor = recipe.carrier identity descriptor := rfl

end Recipe

/-- A reached recipe keeps this exact seed; no fresh capture is selected. -/
theorem of_seed (origin : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (seed : Seed functions origin header) {mapping : LocationMap} {world : StoreTyping}
    (maps : LocationMap.Extends [] mapping) (worlds : WorldExtends origin.world world) :
    Recipe functions origin header seed mapping world :=
  ⟨seed.member, maps, worlds⟩

/-- The actual bootstrap producer is invoked once inside Prop. The returned
seed is retained as the common index for all later map/world extensions. -/
theorem of_bootstrap (origin : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : header ∈ headers) {mapping : LocationMap} {world : StoreTyping}
    (maps : LocationMap.Extends [] mapping) (worlds : WorldExtends origin.world world) :
    ∃ seed : Seed functions origin header, Nonempty (Recipe functions origin header seed mapping world) := by
  obtain ⟨seed⟩ := Seed.of_bootstrap functions origin member
  exact ⟨seed, ⟨of_seed functions origin seed maps worlds⟩⟩

variable {qualification : Facet compiled}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {context : SourceSemantics.Context} {source : TypedSource}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  (admitted : Admission bridge context initial)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  {calleeHeap : Dynamic.Heap} {arguments : List Dynamic.Value} {payloads : List Value}
  {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty} {packed : Dynamic.Value}
  (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
  (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)

include bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- Zero prefix and global size follow from the retained bootstrap. Genuine
Source attribution and static profiles remain those of the same Header. -/
theorem at_arguments
    (origin : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : header ∈ headers)
    {seed : Seed functions origin header}
    (recipe : Recipe functions origin header seed index.mapping index.world)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    (identity descriptor : Word) (sameLayouts : header.layouts = compiled.indexed.layouts)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      index.mapping index.world header.bindings arguments payloads)
    (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions origin.owner (header := header))
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap)
      (arguments := arguments) (payloads := payloads) functions (.global function) function.evidence
      (recipe.carrier identity descriptor) header.function.resultType header.output :=
  CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.named
    functions bridge initial admitted runtime extension argumentsTyped packing bundle
    origin.owner member origin.capture_zero (origin.globals member) sourceAt recipe.capture
    identity descriptor sameLayouts wellFormed calleeTyped represented profiles syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes
