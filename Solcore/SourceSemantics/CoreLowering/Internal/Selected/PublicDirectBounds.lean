import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectClosureApplications
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectApplications
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins

/-!
# Selected compilations: public direct bounds

Public bounds of direct calls through a handle, for named, builtin and closure callees, with data inputs and initial arguments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
/-! Direct packed inputs are split using the real retained Source binder row.
The zero, singleton and longer cases retain exact grouping and argument order,
including nested functions, nominal metadata and mapping payloads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)


variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) (.closure function) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- The retained closure's actual binder row determines the source argument
vector, including the distinction between zero arguments and one Unit argument.
The existing numeric body family reflects the same complete native application. -/
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.closure function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have children : ∀ childSize,
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        callFaults childSize :=
    SelectedCompilationPhysicalMixedCallerFamily.reflects_with_methods
      receiver (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
      support.profile support.bodyTyping support.certificates (SelectedCompilationPhysicalProgramSupport.observations support) (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
      (SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension) support.bodies support.bodySupport
      support.closurePackets support.closureSupport support.owners support.methods rfl
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.closure_member support.profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed
  obtain ⟨sources, values, packing, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
  have arity : sources.length = function.parameters.length := represented.length.1.symm.trans binderLength
  have argumentsTyped := packing.unpackTypes
    (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    argumentsTyped packing parameterEq.symm arity
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, covers⟩
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← nativeEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_reflects
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension)
      support.profile association (support.closurePackets association) (support.closureSupport association)
      caller raw represented heaps physical support.owners stable runtime
      valid size (fun childSize _ => children childSize) evaluation (Nat.le_refl _)
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- A Source application of the exact packed input constructs finite native
execution at the original caller store. The real Source arity disambiguates
zero, singleton and longer packs before the existing body preservation proof. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.closure function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have children : ∀ childSize,
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        callFaults childSize :=
    SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
      receiver (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
      support.profile support.bodyTyping support.certificates (SelectedCompilationPhysicalProgramSupport.observations support) (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
      (SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension) support.bodies support.bodySupport
      support.closurePackets support.closureSupport support.owners support.methods
  obtain ⟨bindings, actualParameter, actualResult, ⟨association⟩, nativeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.closure_member support.profile calleeRelated function rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  obtain ⟨parameterEq, resultEq, signatures, code, covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : parameter = TypeSystem.Ty.productMany
      (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [association.source_binders]
    exact parameterEq
  have packed := packedRelated
  rw [sourceBundle] at packed

  obtain ⟨decodedSources, values, decodedPacking, nativeEq, represented⟩ :=
    RecursivePublicPackedArguments.arguments bindings association.projected_bindings packed
  have binderLength : bindings.length = function.parameters.length := by
    simpa only [List.length_map] using congrArg List.length association.source_binders
  have decodedArity : decodedSources.length = function.parameters.length :=
    represented.length.1.symm.trans binderLength
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (decodedArity.trans arity.symm)
  subst decodedSources
  have argumentsTyped := packing.unpackTypes
    (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime calleeTyped heapTyped
    argumentsTyped packing parameterEq.symm arity
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult, finalHeaps,
    maps, worlds, frame, metadata, returned, related, post⟩ :=
    SelectedCompilationPhysicalClosureApplicationBounds.application_preserves
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver) (semantic := SelectedCompilationPhysicalProgramSupport.semantic_extension support receiver extension)
      support.profile association (support.closurePackets association) (support.closureSupport association)
      caller raw represented heaps physical support.owners stable runtime
      sourceSize (fun childSize _ => children childSize) trace (Nat.le_refl _)
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [nativeEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
  rw [← resultEq, ← nativeTypes.2] at representedResult
  rw [← resultEq] at post
  exact ⟨value, finalStore, finalMap, finalWorld, padded.sound,
    representedResult, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectClosureBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataInputs
/-! Actual public data input encoding supplies independent source arguments.
Constructors retain their complete raw metadata, mappings retain entry order
and their transported default, and proxies retain their raw inner types.
Opaque handles need separate capture, history and authority representation.
This boundary retains the actual first root, native prefix and final registry.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataInputs
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

open RecursiveNamedPublicDataInputs

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
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
      .ok header.named.specialized) :
    ∃ arguments, Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        mapping world header.bindings arguments native := by
  obtain ⟨inputs, actualProjection⟩ := StartAt.data_inputs started data
  have headerProjection := SelectedCompilationHeaderParameterProjections.projections_of_record header sameChecked certified record
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

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedCatalog
open CallableIndexedParameterCertificates (Binding)
open RecursiveNamedPublicDataArgumentReceipts
private theorem arguments_metadata {checked : SourceCoreCompatibleCatalog.Checked}
    {encoded receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked encoded functions) mapping world bindings sources native)
    (metadata : SourceCoreRawMetadata.Extends encoded receiving) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked receiving functions) mapping world bindings sources native := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (CompatiblePayload.ValueRep.extend head metadata (.refl _) (.refl _)) ih

/-- The original encoder supplies both source meaning and payload representation.
Raw input correctness and exact registry extension construct the two argument
premises at the receiving metadata used by the initialized public bounds. -/
theorem data_arguments_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types) :
    ∃ arguments, RecursiveNamedPublicDataInputs.Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  obtain ⟨arguments, meanings, represented⟩ :=
    SelectedCompilationPublicDataInputs.StartAt.data_arguments functions mapping started selected
      typed.data sameChecked certified record
  exact ⟨arguments, meanings, arguments_metadata represented metadata, typed.source_haveTypes meanings⟩

/-- Match caller-supplied independent Source arguments to the actual encoder's
arguments before the initialized public Word preservation theorem is applied. -/
theorem data_arguments_at_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, actualTyped⟩ :=
    data_arguments_receiving functions receiving mapping before started selected sameChecked certified metadata typed
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional interpreted meanings
  cases same
  exact ⟨represented, actualTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
/-! Actual bootstrap and original public data encoding construct the positive
closure model and every installed cache cell, including selected method closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
  (sameRuntime : bootstrapSession.SameRuntime publicSession)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  {arguments : List Dynamic.Value}
  (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
    header.function.context publicArguments header.types)
  (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct bodyTyping prepared selected opened fresh ready sameRuntime atSession started inputTypes inputMeanings metadata in
/-- This proof is consumed immediately by the public endpoints below. The
runtime-preservation receipt fixes the initial store/world; the argument producer uses
the caller's receiving metadata without identifying two registries. -/
theorem initial_data_arguments :
    ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol rootHeaders rootKeys 0).State
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
        some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
          ((rootOwner).key.locations header)) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions [] world ⟨[]⟩ store ∧
      Dynamic.HeapWellTyped header.function.context ⟨[]⟩ ∧
      CallableIndexedParameterMeaning.Arguments rootModel [] world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨value, booted, worldEq, storeEq, _nativeAt, _registryAt, _initializedStart⟩ :=
    CallableIndexedOwnedPublicBootstrapInitialization.at_started prepared opened fresh ready sameRuntime atSession started
  subst world
  subst store
  obtain ⟨_result, _storeEq, caller, stable, heaps, globals, heapTyped⟩ :=
    SelectedCompilationPhysicalBootstrap.of_completed bodyTyping inputs rows prepared distinct
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry booted
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicDataArgumentReceipts.data_arguments_at_receiving
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry [] ⟨[]⟩
      started selected rfl (SelectedCompilationHeaderCertificates.certified bodyTyping header) metadata inputTypes inputMeanings
  exact ⟨caller, stable, globals header selected.member, heaps,
    heapTyped header.function.context, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicInitialArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicBodyInvocationBounds
/-! Public boundary adapters for every accepted named body consume physical laws produced by
the numeric family. Actual public starts and outcomes select the same cache,
parameter state and returned store as the original Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicBodyInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functions) identities)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) headers root header)
  (packet : CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (functions))
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functions)
    mapping world before store)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootFunctions" => functions
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "rootBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable
  (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
    (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (functions))
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget)
  (reflectsBodies : ∀ budget {child : Staging.Recursive.Scope},
    (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
        (functions))
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) budget)

include packet keyPhysical physical bodyTyping preservesBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- The actual cached root consumes the mixed numeric family. Ordinary closure
packets come from preparation, and the selected named packet supplies its own
static roots. The exact optional-cell read, parameter entry, body, restoration
and root argument packing are all executed by the existing producers. -/
theorem preserves_root
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments outcome after) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial root.body
            (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
          .done value finalStore) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
    packet.prepared packet.aligned selected.member keyPhysical physical heaps.runtime_hasTypes
  let nativeCapture := capture.named
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    SelectedCompilationPhysicalNamedInvocationPreservation.preserves_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (physicalCapture := capture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (sourceAt := sourceAt)
      packet.layouts physical selected.member bodyTyping.function_ids (SelectedCompilationHeaderCertificates.certified bodyTyping header) stable heapTyped argumentsTyped represented heaps
      supports size (fun {child} selected => preservesBodies size selected) trace (Nat.le_refl _)
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  have read := OptionalCell.read_success Word.zero
    (show Evaluates
      (DataPatternValues.packValues payloads :: payloads.reverse ++
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (.var (header.slot + root.types.length + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) store
      from .var actualReference) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated read result.1
  have rootEvaluation : Evaluates
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      store root.body value finalStore := by
    simpa only [selected.shape.2] using called
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel rootEvaluation
  exact ⟨nativeCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩

include packet keyPhysical physical bodyTyping reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- A completed original root exposes its exact cached named body. Numeric
reflection supplies the staged application and actual returned pool; a staged
rejection remains a staged rejection rather than an ordinary Dynamic fault. -/
theorem reflects_root
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body
        (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
      .done value finalStore) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) arguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
    packet.prepared packet.aligned selected.member keyPhysical physical heaps.runtime_hasTypes
  let nativeCapture := capture.named
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  rw [selected.shape.2] at measured
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated actualReference capture.read measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    SelectedCompilationPhysicalNamedInvocationBounds.reflects_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (physicalCapture := capture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (prepared := packet.prepared) (aligned := packet.aligned) (stagePrepared := stagePrepared)
      (descriptor := descriptor) (sourceAt := sourceAt)
      packet.layouts physical selected.member (SelectedCompilationHeaderCertificates.certified bodyTyping header) stable heapTyped argumentsTyped represented heaps
      supports size (fun {child} selected => reflectsBodies size selected) bodyEvaluation (Nat.le_of_lt smaller)
  exact ⟨nativeCapture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩

variable {recipe : SourceCoreIndexedSession.Recipe} {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {options : SourceCoreExecution.RunOptions}
  (sameCompiled : recipe.compiled = compiled)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe (sameCompiled.symm ▸ root)
    world store payloads encodedValues)

include packet keyPhysical physical bodyTyping reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- An actual public success reaches the same cached named body and staged
Source application. Export metadata and the body model's receiving metadata
retain their own actual receipts; no registry equality is invented. -/
theorem public_run_succeeded_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (bodyTyping := bodyTyping) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (reflectsBodies := reflectsBodies) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩

include packet keyPhysical physical bodyTyping reflectsBodies
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- Public failure retains the actual staged failure relation. In particular,
a nested stage rejection is not relabeled as a Dynamic semantic fault. -/
theorem public_run_failed_reflects
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (bodyTyping := bodyTyping) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (reflectsBodies := reflectsBodies) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    failed, sessionAt, trace, result⟩

include packet keyPhysical physical bodyTyping preservesBodies observations
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- A staged Source Word result is preserved by the same public checkpoint
at sufficient native fuel. The actual export budget remains independent of
the input budget and the staged trace is retained unchanged. -/
theorem public_word_preserved
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments (.value (.word word)) after) :
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context (.value (.word word)) after
          (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    preserves_root
      (stagePrepared := stagePrepared) (functions := functions)
      (packet := packet) (keyPhysical := keyPhysical) (physical := physical)
      (bodyTyping := bodyTyping) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) (preservesBodies := preservesBodies) trace
  have represented := result.2.1
  rw [outputWord] at represented
  have nativeWord : value = .inRight .word (.word word) := by
    cases represented with
    | value payload =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨capture, finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => RecursiveNamedPublicExecutionMeaning.resume_word_succeeded
      atCheckpoint resumed (started.initial.native_done_iff.mpr (completes fuel enough)) requested positive,
    result⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicBodyInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectNamedBounds
/-! A direct named handle keeps its genuine Header, Source dictionary and full
stored native capture. Packed inputs use that Header's actual parameter row;
the existing finite static family closes every nested body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectNamedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.GlobalFunction} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.global function) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) (.global function) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- Actual direct completion reflects the same global function, dictionary,
ordered arguments, captured native environment and full returned caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.global function) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.global function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  classical
  obtain ⟨originalType, ⟨association⟩, _rawType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member support.profile calleeRelated function rfl
  let owner := association.owner
  let header := association.header
  let descriptor := association.descriptor
  let sourceAt := association.sourceAt
  have member := association.member
  let packet := support.bodies header member
  obtain ⟨⟨capture, captureEq⟩⟩ :=
    association.at_store packet.prepared packet.aligned (support.owners owner) physical
  have nativeEq := association.native_eq
  rw [← captureEq] at nativeEq
  have nativeType := association.type_eq
  let identity := association.identity
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at sourceAt
    support.bodyTyping packet.prepared packet.aligned
  have headerCertified := support.certificates header member
  obtain ⟨_facts, certified⟩ := certifiedAt
  have signature : parameter = TypeSystem.Ty.productMany header.types ∧ result = header.function.resultType := by
    rcases calleeTyped.global_inv with ordinary | staged
    · obtain ⟨typeEq, _valid, _evidence⟩ := ordinary
      have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
      exact ⟨signature.1, signature.2.trans sourceAt.frame.result.symm⟩
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
    have same := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
    rw [header.parameters] at same
    simpa only [List.map_map, Function.comp_def] using same.symm
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values header.types packed
  have typeLength : header.types.length = header.bindings.length := by rw [bindingTypes, List.length_map]
  have nativeRow : nativeTypesRow = header.bindings.map Prod.snd :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (by simpa only [List.length_map] using rows.length.2.2.symm.trans typeLength)
      (packedType.symm.trans (nativeTypes.1.trans header.parameterType))
  rw [bindingTypes, nativeRow] at rows
  have represented := RecursivePublicPackedArguments.of_values header.bindings rows
  have arity : header.function.parameters.length = sources.length := by
    simpa only [header.parameters, List.length_map] using represented.length.1
  obtain ⟨bodyHeap, argumentsTyped⟩ :=
    SelectedCompilationPackedNamedArguments.arguments_at_global
      sourceAt ⟨_facts, certified⟩ runtime heapTyped calleeTyped packing packedTyped arity
  have supports := SelectedCompilationNamedAdmission.caller_supports headerCertified runtime
  have children : ∀ {child : Staging.Recursive.Scope}, (callStages).Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers) (keys := keys) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages child callFaults size := by
    intro child selected
    exact SelectedCompilationPhysicalProgramSupport.reflects_bodies
      support receiver extension header member selected size
  have evaluation : EvaluationSize size
      [CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
        (owner := owner) header capture.named identity descriptor.id, DataPatternValues.packValues values]
      store CallableIndexedLambdaCalls.applyPayload value finalStore := by
    have measured := RecursiveNamedPublicDirectClosureApplicationBounds.application_tail
      (other := []) completed
    rw [nativeEq, packedEq] at measured
    exact measured
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated, resultAt⟩ :=
    SelectedCompilationPhysicalNamedApplicationBounds.application_reflects
      functions owner caller header capture sourceAt packet.prepared packet.aligned
        (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled) descriptor packet.layouts physical member headerCertified
      stable bodyHeap argumentsTyped represented heaps supports identity descriptor.id size children evaluation (Nat.le_refl _)
  have actualResult : resultCore = header.output := nativeTypes.2.trans header.resultType
  have finalResult := resultAt.2
  rw [← signature.2, ← actualResult] at finalResult
  have count : header.sourceBody.source.inputs.length = sources.length := by
    rw [← sourceAt.frame.parameters]
    exact arity
  exact ⟨sources, packing, count ▸ RecursivePublicCallableArity.Arity.global sourceAt.frame.instantiated, sourceSize, outcome, after, finalMap, finalWorld, trace, finalResult⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.global function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  exact ⟨sources, packing, meaning⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- An independent named application at the authentic declared arity drives
the original native payload, retaining success or failure and the full caller post. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.global function) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.global function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  classical
  obtain ⟨originalType, ⟨association⟩, _rawType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member support.profile calleeRelated function rfl
  let owner := association.owner
  let header := association.header
  let descriptor := association.descriptor
  let sourceAt := association.sourceAt
  have member := association.member
  let packet := support.bodies header member
  obtain ⟨⟨capture, captureEq⟩⟩ :=
    association.at_store packet.prepared packet.aligned (support.owners owner) physical
  have nativeEq := association.native_eq
  rw [← captureEq] at nativeEq
  have nativeType := association.type_eq
  let identity := association.identity
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at sourceAt
    support.bodyTyping packet.prepared packet.aligned
  have headerCertified := support.certificates header member
  obtain ⟨_facts, certified⟩ := certifiedAt
  have signature : parameter = TypeSystem.Ty.productMany header.types ∧ result = header.function.resultType := by
    rcases calleeTyped.global_inv with ordinary | staged
    · obtain ⟨typeEq, _valid, _evidence⟩ := ordinary
      have signature := TypeSystem.Ty.function.inj (typeEq.trans certified.callable_type)
      exact ⟨signature.1, signature.2.trans sourceAt.frame.result.symm⟩
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have bindingTypes : header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
    have same := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
    rw [header.parameters] at same
    simpa only [List.map_map, Function.comp_def] using same.symm
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values header.types packed
  have typeLength : header.types.length = header.bindings.length := by rw [bindingTypes, List.length_map]
  have nativeRow : nativeTypesRow = header.bindings.map Prod.snd :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (by simpa only [List.length_map] using rows.length.2.2.symm.trans typeLength)
      (packedType.symm.trans (nativeTypes.1.trans header.parameterType))
  rw [bindingTypes, nativeRow] at rows
  have represented := RecursivePublicPackedArguments.of_values header.bindings rows
  have decodedArity : header.function.parameters.length = decodedSources.length := by
    simpa only [header.parameters, List.length_map] using represented.length.1
  have arity : header.function.parameters.length = sources.length := by
    have actual := SelectedCompilationPackedNamedArguments.global_count arityAt support.bodyTyping.function_ids sourceAt.frame.instantiated
    simpa only [header, sourceAt.frame.parameters] using actual
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (decodedArity.symm.trans arity)
  subst decodedSources
  obtain ⟨bodyHeap, argumentsTyped⟩ :=
    SelectedCompilationPackedNamedArguments.arguments_at_global
      sourceAt ⟨_facts, certified⟩ runtime heapTyped calleeTyped packing packedTyped arity
  have supports := SelectedCompilationNamedAdmission.caller_supports headerCertified runtime
  have children : ∀ {child : Staging.Recursive.Scope}, (callStages).Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) header
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        callStages child callFaults sourceSize := by
    intro child selected
    exact SelectedCompilationPhysicalProgramSupport.preserves_bodies
      support receiver extension header member selected sourceSize
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    SelectedCompilationPhysicalNamedApplicationBounds.application_preserves
      functions owner caller header capture sourceAt packet.layouts physical member support.bodyTyping.function_ids headerCertified
      stable bodyHeap argumentsTyped represented heaps supports identity descriptor.id sourceSize children trace (Nat.le_refl _)
  have actualResult : resultCore = header.output := nativeTypes.2.trans header.resultType
  have finalResult := resultAt.2
  rw [← signature.2, ← actualResult] at finalResult
  obtain ⟨nativeSize, measured⟩ := evaluation_has_size evaluated
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [nativeEq, packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail measured
  exact ⟨value, finalStore, finalMap, finalWorld, padded.sound, finalResult⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.global function) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectNamedBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
/-! The authentic builtin identity supplies its ordered parameter row. The
primitive application proof keeps the caller, heap and store unchanged while
relating the actual result to independent Source application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : BuiltinFunctionId} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.builtin ⟨function⟩) (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) (.builtin ⟨function⟩) native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Actual complete builtin execution determines the same Source primitive
result and unchanged caller; no builtin body law is supplied by a caller. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := SelectedCompilationPhysicalBuiltinOrigins.builtin_member support.profile calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨sources, values, nativeTypesRow, rows, packing, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have evaluation : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore := by
    rw [← packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail completed
  obtain ⟨sourceResult, trace, representedResult, applied, finalStoreEq⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.reflects functions (SelectedCompilationPhysicalProgramSupport.observations support) builtin rows evaluation
  subst finalStore
  rw [← signature.2, ← nativeTypes.2] at representedResult
  refine ⟨sources, packing, rows.length.1.symm ▸ RecursivePublicCallableArity.Arity.builtin ⟨function⟩, Staging.Recursive.Size.stepSize [], .value sourceResult,
    before, mapping, world, trace, representedResult, heaps, .refl _, .refl _, .refl _ _, .refl _,
    caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.builtin ⟨function⟩) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed
  exact ⟨sources, packing, meaning⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- The actual primitive argument arity fixes its unpacking. Typed primitive
inputs exclude Source dispatch faults; all caller state remains unchanged. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arityAt : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) (.builtin ⟨function⟩) sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  have builtin := SelectedCompilationPhysicalBuiltinOrigins.builtin_member support.profile calleeRelated ⟨function⟩ rfl
  have nativeType : CallableContract.functionType parameterCore resultCore =
      CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) := by
    generalize sourceTypeEq : function.type = sourceType at builtin
    cases builtin
    rfl
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters nativeType
  have signature : parameter = TypeSystem.Ty.productMany function.parameterTypes ∧ result = function.returnType := by
    rcases calleeTyped.builtin_inv with ordinary | staged
    · exact TypeSystem.Ty.function.inj ordinary
    · obtain ⟨inner, impossible, _typed⟩ := staged
      cases impossible
  have packed := packedRelated
  rw [signature.1] at packed
  obtain ⟨decodedSources, values, nativeTypesRow, rows, decodedPacking, packedEq, packedType⟩ :=
    RecursivePublicPackedArguments.values function.parameterTypes packed
  have expectedLength : function.parameterTypes.length = (CompatibleBuiltinMeaning.argumentTypes function).length := by
    cases function <;> rfl
  have nativeRow : nativeTypesRow = CompatibleBuiltinMeaning.argumentTypes function :=
    CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
      (rows.length.2.2.symm.trans expectedLength)
      (packedType.symm.trans (nativeTypes.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function).symm))
  rw [nativeRow] at rows
  have arity : function.parameterTypes.length = sources.length := arityAt.builtin_count
  have sameSources : decodedSources = sources :=
    decodedPacking.injective_of_length_eq packing (rows.length.1.symm.trans arity)
  subst decodedSources
  obtain ⟨nativeSize, value, evaluated, representedResult, sameHeap, _sourceGrade⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.preserves functions (SelectedCompilationPhysicalProgramSupport.observations support) builtin rows trace
  subst after
  rw [← signature.2, ← nativeTypes.2] at representedResult
  have padded : EvaluationSize nativeSize (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value store := by
    rw [packedEq]
    exact RecursiveNamedPublicDirectClosureApplicationBounds.application_tail evaluated
  obtain ⟨source, sameOutcome, _sameHeap, _size, applied⟩ :=
    CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions (SelectedCompilationPhysicalProgramSupport.observations support) rows trace
  cases sameOutcome
  refine ⟨value, store, mapping, world, padded.sound, representedResult, heaps,
    .refl _, .refl _, .refl _ _, .refl _, caller, (protocol headers keys).refl caller, stable, ?_⟩
  intro source same
  cases same
  exact ⟨signature.2 ▸ applied.preserves.2, heapTyped⟩

include support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated in
/-- Successful Source execution supplies the genuine arity automatically. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before (.builtin ⟨function⟩) sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectBuiltinBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableBounds
/-! Actual Source callable shape selects the existing closure, named or builtin
application proof. The common public input and completion keep the same full
returned caller and independent Source execution for every function kind. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Packed
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Value} {native : Value} {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
  (calleeTyped : Dynamic.ValueHasType context before function (.function parameter result))
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world (.function parameter result) function native
    (CallableContract.functionType parameterCore resultCore))
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world before store)

  {packedSource : Dynamic.Value} {packedNative : Value}
  (packedTyped : Dynamic.ValueHasType context before packedSource parameter)
  (packedRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (SelectedCompilationPhysicalProgramSupport.functions support)
    mapping world parameter packedSource packedNative parameterCore)

local notation "functions" => SelectedCompilationPhysicalProgramSupport.functions support
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- The authentic source function branch supplies its actual ordered argument
row; the same native completion reflects independent Source application. -/
theorem reflects_packed_at_arity {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) function sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before function sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  cases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure closure =>
      obtain ⟨sources, packing, arity, reflected⟩ :=
        SelectedCompilationPublicDirectClosureBounds.reflects_packed
          support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
      exact ⟨sources, packing, arity.symm ▸ RecursivePublicCallableArity.Arity.closure closure, reflected⟩
  | global global =>
      exact SelectedCompilationPublicDirectNamedBounds.reflects_packed_at_arity
        support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  | builtin builtin =>
      cases builtin with
      | mk id =>
        exact SelectedCompilationPublicDirectBuiltinBounds.reflects_packed_at_arity
          support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated completed

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
theorem reflects_packed {invocation : Staging.Recursive.Scope}
    {size : Nat} {value : Value} {finalStore : Store} {tail : Environment}
    (completed : EvaluationSize size (native :: packedNative :: tail) store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before function sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := reflects_packed_at_arity support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated completed
  exact ⟨sources, packing, meaning⟩

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- An independent Source application at the genuine callable arity preserves
its complete outcome and reached heap. Packing alone does not fix arity. -/
theorem preserves_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) function sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before function sources outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        outcome after value finalStore finalMap finalWorld callFaults := by
  cases CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.callable_shape calleeTyped with
  | closure closure =>
      exact SelectedCompilationPublicDirectClosureBounds.preserves_packed
        support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
        packing arity.closure_count.symm trace
  | global global =>
      exact SelectedCompilationPublicDirectNamedBounds.preserves_packed
        support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
        packing arity trace
  | builtin builtin =>
      cases builtin with
      | mk id =>
        exact SelectedCompilationPublicDirectBuiltinBounds.preserves_packed
          support caller stable heapTyped calleeTyped calleeRelated heaps packedRelated packing arity trace

include support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated in
/-- Successful Source execution supplies the genuine callable arity. -/
theorem preserves_value_packed {invocation : Staging.Recursive.Scope} {tail : Environment}
    {sources : List Dynamic.Value} (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
      invocation context before function sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (native :: packedNative :: tail) store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result resultCore
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact preserves_packed support receiver extension caller physical stable runtime heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    packing (.of_value trace) trace

end Packed
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableBounds
end
