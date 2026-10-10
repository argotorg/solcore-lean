import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts

/-! A positive global recipe chooses its owner and capture from the actual
bootstrap. Only that same capture is extended to the actual argument post.
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

/-- The stored capture is the output of the real bootstrap capture producer.
Its extension changes only type/map admission, preserving carrier fields. -/
structure Recipe (origin : NamedOwner (headers := headers) keys functions registry)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (mapping : LocationMap) (world : StoreTyping) where
  member : header ∈ headers
  maps : LocationMap.Extends [] mapping
  worlds : WorldExtends origin.world world

namespace Recipe
variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {origin : NamedOwner (headers := headers) keys functions registry}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping}

/-- The capture is chosen from the original bootstrap producer; it is not a
field supplied by a caller or recovered from an arbitrary global carrier. -/
noncomputable def initialCapture (recipe : Recipe functions origin header mapping world) :
    NamedCapture headers origin.owner.key header [] origin.world :=
  Classical.choose (origin.named_capture recipe.member)

theorem installed (recipe : Recipe functions origin header mapping world) :
    NamedInstalledCode recipe.initialCapture :=
  Classical.choose_spec (origin.named_capture recipe.member)

noncomputable def capture (recipe : Recipe functions origin header mapping world) :
    NamedCapture headers origin.owner.key header mapping world :=
  recipe.initialCapture.extend recipe.maps recipe.worlds

noncomputable def carrier (recipe : Recipe functions origin header mapping world)
    (identity descriptor : Word) : Value :=
  CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.carrier
    origin.owner recipe.capture identity descriptor

end Recipe

/-- The only positive recipe producer obtains its capture from bootstrap
once. The caller supplies actual map/world growth at the reached packet. -/
theorem of_bootstrap (origin : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (member : header ∈ headers) {mapping : LocationMap} {world : StoreTyping}
    (maps : LocationMap.Extends [] mapping) (worlds : WorldExtends origin.world world) :
    Nonempty (Recipe functions origin header mapping world) := by
  exact ⟨⟨member, maps, worlds⟩⟩

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
    (recipe : Recipe functions origin header index.mapping index.world)
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
