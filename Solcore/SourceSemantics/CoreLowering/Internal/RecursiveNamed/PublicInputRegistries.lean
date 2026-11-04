import Solcore.SourceSemantics.CoreLowering.CompatibleMissingDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload
import Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.Frontend.SourceCoreIndexedSession

/-!
# Recursive named public results: execution and input registries

Public start, runtime and execution meaning, the checkpoint receiver, and the registries of simple, function and returned inputs.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
/-! Authentic diagnostic receivers preserve previously decoded errors when the
actual raw metadata registry extends. The fixed function model is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingReservedReceipts
open CallableIndexedOwnedPublicFaultReceiverTables

private theorem extra_below {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {base : SourceCoreProgramFaultSites.Program} {initialExtra : List (Word × Diagnostic)}
    (reserved : ReservedAt context plan root program base initialExtra)
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table} (rebuilt : program.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (origin : MissingDiagnosticOrigin registry program.missing row) :
    row.1.val < program.nextReason := by
  obtain ⟨site, member, rawKey, rawValue, header, lookup, _keys, _values, _within, token, _diagnostic⟩ :=
    origin.mapping_header
  have belowBound := CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member
    (show MetadataRep registry (.mapping rawKey rawValue) header from ⟨lookup⟩)
  simpa only [token] using belowBound

private theorem suffix_preserved {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {plan : Plan} {root : Key} {sources : List (Key × TypedSource)}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (prepared : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program)
    {registry future : SourceCoreRawMetadata.Registry}
    {leftExtension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {rightExtension : SourceCoreRawMetadata.Extends program.context.registry future}
    {left right : SourceCoreFaultSites.Table}
    (leftBuilt : program.tableForRegistry registry leftExtension = .ok left)
    (rightBuilt : program.tableForRegistry future rightExtension = .ok right)
    (preserves : ∀ {oldRows newRows},
      missingDiagnostics registry program.missing = .ok oldRows →
      missingDiagnostics future program.missing = .ok newRows →
      ∀ {token row}, oldRows.find? (fun item => decide (item.1 = token)) = some row →
        newRows.find? (fun item => decide (item.1 = token)) = some row)
    (suffix : List (Word × Diagnostic))
    (above : ∀ row, row ∈ suffix → program.nextReason ≤ row.1.val)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : {left with additional := left.additional ++ suffix}.diagnostic? token = some diagnostic) :
    {right with additional := right.additional ++ suffix}.diagnostic? token = some diagnostic := by
  obtain ⟨base, initialExtra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt prepared
  obtain ⟨oldRows, oldBuilt, oldShape, _oldOrigins⟩ := program.tableForRegistry_receipt leftBuilt
  obtain ⟨newRows, newBuilt, newShape, newOrigins⟩ := program.tableForRegistry_receipt rightBuilt
  rw [oldShape, reserved.sameRoot] at decoded
  rw [newShape, reserved.sameRoot]
  by_cases zero : token = Word.zero
  · simpa only [SourceCoreFaultSites.Table.diagnostic?, zero, if_pos] using decoded
  by_cases escaped : token = base.rootTable.escapedReason
  · simpa only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, if_false, if_pos] using decoded
  simp only [SourceCoreFaultSites.Table.diagnostic?, zero, escaped, if_false, List.find?_append] at decoded ⊢
  cases fixed : program.fixed.find? (fun item => decide (item.1 = token)) with
  | some row => simpa only [fixed, Option.some_or] using decoded
  | none =>
    simp only [fixed, Option.none_or] at decoded ⊢
    cases old : oldRows.find? (fun item => decide (item.1 = token)) with
    | some row =>
      have current := preserves oldBuilt newBuilt old
      simpa only [old, current, Option.some_or] using decoded
    | none =>
      simp only [old, Option.none_or] at decoded
      cases appended : suffix.find? (fun item => decide (item.1 = token)) with
      | some row =>
        have rowMember := List.mem_of_find?_eq_some appended
        have same : row.1 = token := of_decide_eq_true (List.find?_some (p := fun item : Word × Diagnostic => decide (item.1 = token)) appended)
        have threshold := above row rowMember
        have absent : newRows.find? (fun item => decide (item.1 = token)) = none := by
          apply List.find?_eq_none.mpr
          intro added member matched
          have addedEq : added.1 = token := of_decide_eq_true matched
          have belowBound := extra_below reserved rightBuilt (newOrigins added member)
          rw [addedEq] at belowBound
          rw [same] at threshold
          omega
        simpa only [absent, Option.none_or, appended] using decoded
      | none =>
        simp only [appended] at decoded
        cases readAt : base.rootTable.reads.find? (fun site => decide (site.reason = token)) with
        | none => simp only [readAt, Option.map_none] at decoded; cases decoded
        | some read =>
          have member := List.mem_of_find?_eq_some readAt
          have same : read.reason = token := of_decide_eq_true (List.find?_some (p := fun site : SourceCoreFaultSites.ReadSite => decide (site.reason = token)) readAt)
          have absent : newRows.find? (fun item => decide (item.1 = token)) = none := by
            apply List.find?_eq_none.mpr
            intro added addedMember matched
            have addedEq : added.1 = token := of_decide_eq_true matched
            exact CompatiblePublicDiagnosticPriority.read_extra_different reserved rightBuilt member
              (newOrigins added addedMember) (same.trans addedEq.symm)
          simpa only [absent, Option.none_or, appended, readAt] using decoded

private theorem issued_preserved_of_rows (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (preserves : ∀ {oldRows newRows},
      missingDiagnostics left.result.context.registry program.missing = .ok oldRows →
      missingDiagnostics right.result.context.registry program.missing = .ok newRows →
      ∀ {token row}, oldRows.find? (fun item => decide (item.1 = token)) = some row →
        newRows.find? (fun item => decide (item.1 = token)) = some row)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : left.result.diagnostics.diagnostic? token = some diagnostic) :
    right.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨leftBase, leftBuilt, leftTable⟩ := leftIssued
  obtain ⟨rightBase, rightBuilt, rightTable⟩ := rightIssued
  rw [present] at leftBuilt rightBuilt
  rw [leftTable] at decoded
  rw [rightTable]
  cases callableAt : compiled.indexed.base.callableDiagnostics with
  | none =>
    have result := suffix_preserved prepared leftBuilt rightBuilt preserves [] (by simp)
      (by simpa only [appendCallable, callableAt, List.append_nil] using decoded)
    simpa only [appendCallable, callableAt, List.append_nil] using result
  | some callable =>
    have allocation := CompatiblePublicCallableAllocationReceipts.of_compiled compiled present
    obtain ⟨contracts, allocated⟩ := (by
      simpa only [CompatiblePublicCallableAllocationReceipts.AllocationAt, callableAt] using allocation :
      ∃ contracts, SourceCoreCallableFaultSites.prepare compiled.indexed.base.plan contracts
        program.program.rootTable program.nextReason = .ok callable)
    let suffix := callable.rootTable.additional.filter (fun item => callable.unknown.val ≤ item.1.val)
    have above : ∀ row, row ∈ suffix → program.nextReason ≤ row.1.val := by
      intro row member
      have bound : callable.unknown.val ≤ row.1.val := of_decide_eq_true (List.mem_filter.mp member).2
      exact Nat.le_trans (CompatibleCallableDiagnosticBounds.prepare_unknown allocated).2 bound
    have result := suffix_preserved prepared leftBuilt rightBuilt preserves suffix above
      (by simpa only [appendCallable, callableAt, suffix] using decoded)
    simpa only [appendCallable, callableAt, suffix] using result

/-- The same compiled issuer preserves the complete previously selected
public diagnostic at a genuine extension of its raw metadata registry. -/
theorem diagnostic_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {token : Word} {diagnostic : Diagnostic}
    (decoded : left.result.diagnostics.diagnostic? token = some diagnostic) :
    right.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, prepared⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have limits : left.result.context.registry.limits.maxEntries =
      compiled.compatible.checked.staticRegistry.limits.maxEntries :=
    congrArg SourceCoreRawMetadata.Limits.maxEntries left.result.extension.limits
  have ranges := (CompatiblePlaceMissingPreparationRanges.prepare_ranges prepared).1
  apply issued_preserved_of_rows compiled leftIssued rightIssued present (decoded := decoded)
  intro oldRows newRows oldBuilt newBuilt token row found
  exact CompatibleMissingDiagnosticExtension.missingDiagnostics_find_preserved extension
    (limits.symm ▸ ranges) oldBuilt newBuilt found

/-- A fixed semantic function model remains meaningful at the actual next
receiver. Only the diagnostic table changes, following real metadata extension. -/
theorem semantic_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedCallFaults.faults left.result.diagnostics reason token) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults right.result.diagnostics (.semantic reason) token := by
  obtain ⟨diagnostic, decoded, view⟩ := represented
  exact ⟨diagnostic, diagnostic_preserved compiled leftIssued rightIssued present extension decoded, view⟩

/-- Stage-tagged failures preserve the same original call site and error view
as well as the exact decoded diagnostic. -/
theorem staged_preserved (compiled : SourceCoreUnifiedCompilation.Compiled)
    {left right : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (leftIssued : IssuedAt compiled.indexed left.entry left.result.context.registry
      left.result.extension left.result.diagnostics)
    (rightIssued : IssuedAt compiled.indexed right.entry right.result.context.registry
      right.result.extension right.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some program)
    (extension : SourceCoreRawMetadata.Extends left.result.context.registry right.result.context.registry)
    {failure : Staging.Recursive.Failure} {token : Word}
    (represented : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults left.result.diagnostics failure token) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults right.result.diagnostics failure token := by
  cases failure with
  | semantic reason => exact semantic_preserved compiled leftIssued rightIssued present extension represented
  | stage invocation call reason =>
    obtain ⟨diagnostic, decoded, view⟩ := represented
    exact ⟨diagnostic, diagnostic_preserved compiled leftIssued rightIssued present extension decoded, view⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
/-! Public startup fixes the original recipe, store and encoded native prefix.
The views below return propositions only; they expose no executable state or
authority accessor. Independent source arguments and catalog Entry evidence
remain separate from the encoder's native typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Equality with the actual retained recipe, without an executable getter. -/
def ArtifactRecipe (artifact : Artifact) (recipe : Recipe) : Prop :=
  Artifact.casesOn (motive := fun _ => Prop) artifact (fun _ actual => actual = recipe)

/-- The original complete native world and store of this session. -/
def SessionState {artifact : Artifact} (session : Session artifact)
    (world : StoreTyping) (store : Store) : Prop :=
  Session.casesOn (motive := fun _ => Prop) session
    (fun _ actualWorld actualStore _ _ _ _ _ _ => actualWorld = world ∧ actualStore = store)

/-- Equality with the original machine state, used only inside proofs. -/
def CheckpointInitial {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (expression : Expr) (environment : Environment) (store : Store) : Prop :=
  Checkpoint.casesOn (motive := fun _ => Prop) checkpoint
    (fun _ _ _ state _ _ _ _ _ _ => state = .initial expression environment store)

/-- The actual metadata context retained after input encoding. -/
def CheckpointValues {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (values : SourceCoreCompatibleValues.Context) : Prop :=
  Checkpoint.casesOn (motive := fun _ => Prop) checkpoint
    (fun _ _ _ _ _ _ _ _ actual _ => actual = values)

theorem CheckpointInitial.native_done_iff {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {expression : Expr} {environment : Environment} {store : Store}
    (initial : CheckpointInitial checkpoint expression environment store)
    {fuel : Nat} {value : Core.Value} {finalStore : Store} :
    checkpoint.NativeDone fuel value finalStore ↔
      runStateful fuel (.initial expression environment store) = .done value finalStore := by
  cases checkpoint
  rename_i origin request world state stored typed extension registry values owner
  change _ = Core.State.initial expression environment store at initial
  change runStateful fuel state = _ ↔ _
  rw [initial]

/-- Every index denotes an actual startup value. All fields are proofs; no
source execution, body law or authority is introduced into this receipt. -/
structure StartAt {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List SourceCorePublicValues.Value) (boundaryFuel : Nat)
    (checkpoint : Checkpoint artifact) (recipe : Recipe) (root : Root recipe.compiled)
    (world : StoreTyping) (store : Store) (native : Environment)
    (encodedValues : SourceCoreCompatibleValues.Context) : Prop where
  recipe_eq : ArtifactRecipe artifact recipe
  state : SessionState session world store
  original : checkpoint.RootStart session key arguments boundaryFuel
  selected : recipe.roots.find? (fun root => decide (root.key = key)) = some root
  initial : CheckpointInitial checkpoint root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
  values : CheckpointValues checkpoint encodedValues
  typed : RuntimeEnvironmentHasTypes world native root.types recipe.compiled.indexed.layouts.definitions
  owner : encodedValues.checked = recipe.compiled.compatible.checked

/-- Successful startup exposes its exact native prefix and metadata context.
Native typing supplies no independent source representation of the inputs. -/
theorem actual_start {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments boundaryFuel = .ok checkpoint) :
    ∃ (recipe : Recipe) (root : Root recipe.compiled) (world : StoreTyping) (store : Store)
      (native : Environment) (encodedValues : SourceCoreCompatibleValues.Context),
      StartAt session key arguments boundaryFuel checkpoint recipe root world store native encodedValues := by
  have receipt := Session.start_root_receipt session accepted
  cases artifact
  rename_i authority recipe
  cases session
  rename_i sessionAuthority world store stored environmentTyped registry values owner sourcePrefix
  have original := receipt
  obtain ⟨root, selected, _, _, encoded, _, _, _, _, initial, _, valuesEq⟩ := receipt
  rcases encoded with ⟨encodedValues, encodedOwner, native, typed⟩
  refine ⟨recipe, root, world, store, native, encodedValues, ?_⟩
  exact ⟨rfl, ⟨rfl, rfl⟩, original, selected,
    by cases checkpoint; exact initial,
    by cases checkpoint; exact valuesEq, typed, encodedOwner⟩

/-- Real preparation and the original first-find membership select the full
Header. Neither a key nor native type tags replace this provenance. -/
theorem StartAt.selection {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments boundaryFuel checkpoint recipe root world store native encodedValues)
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program}
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) :
    ∃ header, RecursiveNamedPublicRootMeaning.RootSelection headers root header :=
  RecursiveNamedPublicRootMeaning.selection_of_recipe prepared
    (List.mem_of_find?_eq_some started.selected) complete

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel_with_evidence
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    RecursiveNamedPublicRootMeaning.has_sufficient_fuel_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller selected represented heaps executed
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => started.initial.native_done_iff.mpr (completes fuel enough), result⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_with_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRootMeaning.completed_reflects_program_with_evidence authenticated runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps
    admitted heapTyped argumentsTyped (started.initial.native_done_iff.mp completed)

end Evidence

section Common
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (runtime : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel_with
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact has_sufficient_fuel_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_with
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact completed_reflects_program_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps admitted heapTyped argumentsTyped completed

end Common

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact has_sufficient_fuel_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected started represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact completed_reflects_program_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected started represented heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
/-! The actual post-issuance Session is used by the original startup encoder.
These receipts identify the exact callable bytes at the actual argument index,
retain their cached named/builtin factory, and preserve native memory and
metadata across issuance. Source function interpretation remains separate
until that factory's code and complete Source provenance are joined. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Startup consumes the same authenticated opaque handle whose native value
was retained by issuance. No value is chosen by native type or descriptor alone. -/
theorem StartAt.imported_function
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {issuanceFuel : Nat} {expected : TypeSystem.Ty} {handle : Handle} {callable : Core.Value}
    (imported : session.EncodesAt issuanceFuel expected (.function handle) callable)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    native[index]? = some callable := by
  have receipt := started.original.imported_function imported found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, lookup, initial⟩ := receipt
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
  exact lookup

/-- A real named issuance is consumed by the exact later startup. Its whole
cached factory remains attached to the selected native argument. -/
theorem StartAt.named_argument_after
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {name : Key} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt name issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.NamedCallableAt name expected callable ∧
      native[index]? = some callable := by
  obtain ⟨expected, callable, same, sourceType, budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have argument := StartAt.imported_function started (continued.encodes_function encoded) found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  exact ⟨expected, callable, same, sourceType, budget, factory, argument⟩

/-- The original one-issuance entry is the empty continuation case. -/
theorem StartAt.named_argument
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {name : Key} {issuanceFuel : Nat}
    (issuance : before.NamedIssuedAt name issuanceFuel issued)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.NamedCallableAt name expected callable ∧
      native[index]? = some callable := by
  exact StartAt.named_argument_after issuance (.refl _) started handleValue found

/-- Builtin issuance reaches the same original argument encoder and literal
cached closed builtin factory, while the initialized native state is retained. -/
theorem StartAt.builtin_argument_after
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {session : Session artifact}
    (continued : issued.session.IssuanceChain session)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.BuiltinCallableAt function expected callable ∧
      native[index]? = some callable := by
  obtain ⟨expected, callable, same, sourceType, budget, encoded, factory⟩ := issuance.receipt
  rw [handleValue] at encoded
  have argument := StartAt.imported_function started (continued.encodes_function encoded) found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  exact ⟨expected, callable, same, sourceType, budget, factory, argument⟩

/-- The original one-issuance entry is the empty continuation case. -/
theorem StartAt.builtin_argument
    {artifact : Artifact} {before : Session artifact} {issued : Completion artifact}
    {function : BuiltinFunctionId} {issuanceFuel : Nat}
    (issuance : before.BuiltinIssuedAt function issuanceFuel issued)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt issued.session key arguments fuel checkpoint recipe root world store native encodedValues)
    {handle : Handle} (handleValue : issued.value = .function handle)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    ∃ expected callable, before.SameRuntime issued.session ∧ issued.sourceType = expected ∧
      issued.boundaryFuel = issuanceFuel ∧ recipe.BuiltinCallableAt function expected callable ∧
      native[index]? = some callable := by
  exact StartAt.builtin_argument_after issuance (.refl _) started handleValue found

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedFunctionInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
/-! The actual public startup and full data codec receipt supply source arguments
for the runtime catalog family. Every raw constructor/proxy type and ordered
mapping row is retained. Source input typing, staging, heap correspondence and
catalog authority remain independent conditions. Opaque handles and automatic
whole-body profile extraction are separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
open Core Frontend SourceInference
open SourceCoreIndexedSession

/- The public carrier retains all raw metadata and the original list order. -/
mutual
  private theorem public_value_injective (left right : SourceCoreDataValues.Value)
      (same : DataInput.publicValue left = DataInput.publicValue right) : left = right := by
    cases hleft : left <;> cases right <;> simp only [hleft, DataInput.publicValue] at same <;> try (solve | cases same)
    case unit.unit => rfl
    case bool.bool a b => cases same; rfl
    case word.word a b => cases same; rfl
    case integer.integer a b => cases same; rfl
    case proxy.proxy a b => cases same; rfl
    case product.product a b c d =>
      obtain ⟨first, second⟩ := SourceCorePublicValues.Value.product.inj same
      rw [public_value_injective a c first, public_value_injective b d second]
    case constructed.constructed a xs b ys =>
      obtain ⟨metadata, payloads⟩ := SourceCorePublicValues.Value.constructed.inj same
      rw [metadata, public_values_injective xs ys payloads]
    case mapping.mapping k v xs k' v' ys =>
      obtain ⟨key, value, entries⟩ := SourceCorePublicValues.Value.mapping.inj same
      rw [key, value, public_entries_injective xs ys entries]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega

  private theorem public_values_injective (left right : List SourceCoreDataValues.Value)
      (same : DataInput.publicValues left = DataInput.publicValues right) : left = right := by
    cases hleft : left with
    | nil => cases right <;> simp_all [DataInput.publicValues]
    | cons head tail =>
      cases right with
      | nil => simp [hleft, DataInput.publicValues] at same
      | cons other rest =>
        simp only [hleft, DataInput.publicValues] at same
        obtain ⟨first, next⟩ := List.cons.inj same
        rw [public_value_injective head other first, public_values_injective tail rest next]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega

  private theorem public_entries_injective (left right : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value))
      (same : DataInput.publicEntries left = DataInput.publicEntries right) : left = right := by
    cases hleft : left with
    | nil =>
      cases right with
      | nil => rfl
      | cons pair rest => cases pair; simp [hleft, DataInput.publicEntries] at same
    | cons head tail =>
      cases head with
      | mk key value =>
        cases right with
        | nil => simp [hleft, DataInput.publicEntries] at same
        | cons other rest =>
          cases other with
          | mk otherKey otherValue =>
            simp only [hleft, DataInput.publicEntries] at same
            obtain ⟨first, next⟩ := List.cons.inj same
            obtain ⟨keys, values⟩ := Prod.mk.inj first
            rw [public_value_injective key otherKey keys,
              public_value_injective value otherValue values, public_entries_injective tail rest next]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega
end

theorem means_functional {value : SourceCorePublicValues.Value} {left right : Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Means value left)
    (second : RecursiveNamedPublicDataInputs.Means value right) : left = right := by
  obtain ⟨firstCarrier, firstImage, firstMeaning⟩ := first
  obtain ⟨secondCarrier, secondImage, secondMeaning⟩ := second
  have same := public_value_injective firstCarrier secondCarrier (firstImage.symm.trans secondImage)
  cases same
  exact DataPayloadEncoding.Means.functional firstMeaning secondMeaning

theorem meanings_functional {values : List SourceCorePublicValues.Value} {left right : List Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Meanings values left)
    (second : RecursiveNamedPublicDataInputs.Meanings values right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => rw [means_functional head other, ih rest]


section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable (authenticated : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include selected started data sameChecked programTyped record meanings in
/-- Actual encoding supplies the same independently interpreted source arguments.
Native carrier equality is not used to infer a source type or authority. -/
theorem source_arguments :
    CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
      mapping world header.bindings arguments payloads := by
  obtain ⟨actual, related, represented⟩ := RecursiveNamedPublicDataInputs.StartAt.data_arguments functions mapping started selected data sameChecked programTyped record
  have same := meanings_functional related meanings
  exact same ▸ represented


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel_evidence
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicStartMeaning.has_sufficient_fuel_with_evidence authenticated true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started
    (source_arguments functions selected started data sameChecked programTyped record meanings) heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicStartMeaning.completed_reflects_program_with_evidence authenticated true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started
    (source_arguments functions selected started data sameChecked programTyped record meanings) heaps admitted heapTyped argumentsTyped completed

end Evidence

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact has_sufficient_fuel_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact completed_reflects_program_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
/-! Actual public facade startup and returned outcomes retain the same indexed
checkpoint and export receipt. The existing static catalog profiles, Source
admission, argument interpretation and heap representation remain explicit.
No separate body execution law is assumed by this connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
open Core Frontend SourceInference
open SourceCoreIndexedSession

/-- Public compile, open and start success recover one real recipe preparation
and the original indexed startup. All returned observations are propositions. -/
theorem actual_start {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCoreExecution.Compiled}
    (compiledAccepted : SourceCoreExecution.compileChecked program seeds options = .ok compiled)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (opened : publicArtifact.CompiledAt compiled)
    (accepted : publicSession.start key arguments boundaryFuel = .ok publicCheckpoint) :
    ∃ (recipe : Recipe) (artifact : Artifact) (session : Session artifact)
      (checkpoint : Checkpoint artifact) (root : Root recipe.compiled)
      (world : StoreTyping) (store : Store) (native : Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt compiled recipe artifact ∧
      Recipe.prepare recipe.compiled = .ok recipe ∧ recipe.compiled.sourceProgram = program ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments boundaryFuel
        checkpoint recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, atArtifact, atSession, atCheckpoint, issued⟩ :=
    publicSession.start_indexed opened accepted
  have selected : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe :=
    atArtifact.compiled_recipe
  obtain ⟨source, sourceAccepted, cached, prepared⟩ :=
    RecursiveNamedPreparedStageContracts.public_compilation compiledAccepted selected
  have sourceProgram := (SourceCoreCompiler.Compiled.artifact_fields source cached).1.trans
    (SourceCoreCompiler.compileChecked_program sourceAccepted)
  obtain ⟨actualRecipe, root, world, store, native, encodedValues, started⟩ :=
    RecursiveNamedPublicStartMeaning.actual_start session issued
  have actualAt : artifact.RecipeAt actualRecipe := by
    cases artifact
    exact started.recipe_eq
  have atRecipe := atArtifact.recipe_at
  have same : actualRecipe = recipe := by
    unfold Artifact.RecipeAt at actualAt atRecipe
    exact actualAt.symm.trans atRecipe
  cases same
  exact ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sourceProgram, atSession, atCheckpoint, started⟩

/-- Word export follows the same public resume and native execution receipt.
This is a proof transport through the facade, with no native replay. -/
theorem resume_word_succeeded {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicOutcome : SourceCoreExecution.Outcome publicArtifact}
    {artifact : Artifact} {checkpoint : Checkpoint artifact} {fuel outputBudget : Nat}
    {word : Word} {store : Store}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt fuel outputBudget publicOutcome)
    (completed : checkpoint.NativeDone fuel (.inRight .word (.word word)) store)
    (requested : checkpoint.ResultTypeAt .word) (positive : 0 < outputBudget) :
    ∃ completion : SourceCoreExecution.Completion publicArtifact,
      publicOutcome = .succeeded completion ∧ completion.value = .word word := by
  rcases publicArtifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases publicCheckpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected actualArtifact atRecipe =>
      rcases publicCheckpoint with ⟨actualCheckpoint⟩
      rcases atCheckpoint with ⟨rfl, same⟩
      cases eq_of_heq same
      obtain ⟨actualOutcome, receipt, returned⟩ := resumed
      obtain ⟨actual, succeeded, valueEq⟩ := receipt.word_succeeded completed requested positive
      rw [succeeded] at returned
      exact ⟨_, returned.symm, valueEq⟩

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable (authenticated : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- A success from one actual facade run reflects to a Source (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) outcome
at its same native result/store. The returned public session remains aligned
with the exact indexed export session and its full semantic heap relation. -/
theorem run_succeeded_reflects_program_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (admitted : Staging.ProgramHasStages (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (outcome : Dynamic.ExpressionOutcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram) (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result, finalHeap, mapExtension,
    worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps
      admitted heapTyped argumentsTyped completed
  exact ⟨actual, generation, value, finalStore, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, executed, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- An actual public failure reconstructs a Source fault with the same token
relation, final heap, and the exact returned indexed session. -/
theorem run_failed_reflects_program_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (admitted : Staging.ProgramHasStages (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram))
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sourceReason : Dynamic.SemanticFault) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧ faults sourceReason reason ∧
      Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)
        (RecursiveNamedProgramEntrySource.entry header arguments) before (.fault sourceReason) after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults (.fault sourceReason) value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨outcome, after, finalMap, finalWorld, executed, result, finalHeap, mapExtension,
    worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps
      admitted heapTyped argumentsTyped completed
  have decoded := failed.2.1
  have faulted : ∃ sourceReason, outcome = .fault sourceReason ∧ faults sourceReason reason := by
    cases result with
    | value represented => simp [LanguageResult.decode?] at decoded
    | fault related =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        exact ⟨_, rfl, decoded ▸ related⟩
  obtain ⟨sourceReason, rfl, related⟩ := faulted
  exact ⟨actual, value, finalStore, sourceReason, after, finalMap, finalWorld,
    failed, sessionAt, related, executed, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- A Source Word result reaches the same public checkpoint at sufficient
native fuel and exports that Word at a positive output budget. -/
theorem word_preserved_at_resume_evidence
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {word : Word} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome (SourceSemantics.Program.ofChecked recipe.compiled.sourceProgram)
      (RecursiveNamedProgramEntrySource.entry header arguments) before (.value (.word word)) after) :
    ∃ finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → ∀ outcome,
        publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ completion, outcome = .succeeded completion ∧ completion.value = .word word) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults
        (.value (.word word)) (.inRight .word (.word word)) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result, finalHeap,
    mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩ :=
    RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel_evidence authenticated functions
      extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
      caller selected started data sameChecked programTyped record meanings heaps executed
  have wordResult := result
  rw [outputWord] at wordResult
  have nativeWord : value = .inRight .word (.word word) := by
    cases wordResult with
    | value represented =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations represented
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : artifact.RecipeAt recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => resume_word_succeeded atCheckpoint resumed
      (completes fuel enough) requested positive,
    result, finalHeap, mapExtension, worldExtension, administrative, heapExtension, finalEntry⟩

end Evidence
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
/-! The receiver at actual encoded input metadata is the exact diagnostic
lookup used by the pending public checkpoint. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedPublicFaultReceivers
open CallableIndexedOwnedPublicFaultReceiverTables

/-- A present genuine compiler inventory makes the table independent of the
requested entry's fallback fields. The actual input registry remains exact. -/
theorem diagnostic_eq {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    {receiver : Receiver recipe.compiled.indexed}
    (context : receiver.result.context = values)
    (issued : IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
      receiver.result.extension receiver.result.diagnostics)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial recipe.compiled.compatible.checked)}
    (present : recipe.compiled.indexed.base.diagnostics = some program)
    (token : Word) :
    checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  cases checkpoint
  rename_i origin request world state stored typed extension slots actualValues owner
  change actualValues = values at atValues
  subst actualValues
  obtain ⟨base, rebuilt, table⟩ := issued
  rw [present] at rebuilt
  have registryEq : receiver.result.context.registry = values.registry := congrArg (·.registry) context
  have extensionAt : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry values.registry := by
    rw [← owner]
    exact values.extension
  have rebuiltAt : program.tableForRegistry values.registry extensionAt = .ok base := by
    simpa only [registryEq] using rebuilt
  rw [table]
  apply Checkpoint.diagnostic_of_rebuilt
  · exact present
  · exact rebuiltAt

/-- Startup supplies the exact metadata context; the receiver producer builds
and authenticates the corresponding table without running a program. -/
theorem at_checkpoint {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    (owner : values.checked = recipe.compiled.compatible.checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts)
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial recipe.compiled.compatible.checked)}
    (present : recipe.compiled.indexed.base.diagnostics = some program) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨receiver, entryAt, contextAt, issued⟩ := Receiver.at_context recipe.compiled entry values owner
  exact ⟨receiver, entryAt, contextAt, issued, fun token =>
    diagnostic_eq atRecipe atValues contextAt issued present token⟩

/-- Actual callable preparation supplies the diagnostic inventory, so clients
need no separate presence observation. -/
theorem at_prepared_checkpoint {artifact : Artifact} {recipe : Recipe}
    (atRecipe : ArtifactRecipe artifact recipe)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (prepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled native)
    {checkpoint : Checkpoint artifact} {values : SourceCoreCompatibleValues.Context}
    (atValues : CheckpointValues checkpoint values)
    (owner : values.checked = recipe.compiled.compatible.checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry = entry ∧ receiver.result.context = values ∧
      IssuedAt recipe.compiled.indexed receiver.entry receiver.result.context.registry
        receiver.result.extension receiver.result.diagnostics ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨_, present, _, _⟩ := CallableIndexedOwnedPublicCallableDiagnostics.of_compiled
    recipe.compiled prepared.present
  exact at_checkpoint atRecipe atValues owner entry present

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
/-! A successful public return retains the metadata registry from the actual
input encoding. Later calls can therefore derive their metadata conditions
from a prior startup and completion, without assuming a receiving registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Core Frontend SourceInference SourceCoreIndexedSession

theorem StartAt.returned_registry
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments inputFuel checkpoint recipe root world store native encodedValues)
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {value : Core.Value} {finalStore : Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore completion) :
    completion.session.RegistryAt encodedValues.registry := by
  obtain ⟨_done, _payload, _extension, _slots, _encoded, _decoded, _decode, _encode, _recovered,
    _sourceType, _boundary, _stored, _world, _authority, _prefix, returnedValues, _owner,
    _registry, _origin, _authenticated⟩ := succeeded
  have values := started.values
  cases checkpoint
  unfold Session.RegistryAt
  exact congrArg SourceCoreCompatibleValues.Context.registry (returnedValues.trans values)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
/-! Actual scalar and product argument encoding preserves the session metadata
registry. This follows from the retained startup operation; Source typing and
value representation are not premises. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.simple_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : StartAt session key arguments fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry)
    (simple : ∀ argument ∈ arguments, SourceCoreIndexedSession.SimplePublic argument) :
    encodedValues.registry = registry := by
  have unchanged := started.original.simple_registry simple
  cases checkpoint
  cases session
  exact (congrArg SourceCoreCompatibleValues.Context.registry started.values).symm.trans
    (unchanged.trans atRegistry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
/-! An actual public Word completion fixes the value of the independent Source
outcome. The existing full result relation forces a common native/Source Word;
the genuine public decoder identifies that Word with the observed output. No
new execution, source typing or payload representation premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
open Core Frontend SourceInference GeneralHeap CompatiblePayload

/-- Scalar payload inversion and the actual successful export identify the
Source result. The public success receipt also rules out semantic faults. -/
theorem represented_word
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : SourceCoreIndexedSession.Artifact} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Value} {store : Store} {completion : SourceCoreIndexedSession.Completion artifact}
    {word : Word}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt .word)
    (exported : completion.value = .word word)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType .word
      faults outcome native) : outcome = .value (.word word) := by
  obtain ⟨payload, decoded, _⟩ := succeeded.reimports
  cases represented with
  | value related =>
    obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields related
    have actualOutput := succeeded.word_value requested
    have same := SourceCorePublicValues.Value.word.inj (actualOutput.symm.trans exported)
    rw [same]
  | fault related =>
    simp only [LanguageResult.decode?, Option.some.injEq] at decoded
    cases decoded

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world}
  {payloads : List Value} {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome}
  {after : Dynamic.Heap} {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Consume the complete named invocation result returned by public history
execution. Heap, caller and metadata postconditions remain in that same result. -/
theorem result_word
    {artifact : SourceCoreIndexedSession.Artifact} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : SourceCoreIndexedSession.Completion artifact} {word : Word}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (requested : checkpoint.ResultTypeAt .word)
    (exported : completion.value = .word word)
    (outputWord : header.output = .word)
    (result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := payloads) functions owner caller header capture context outcome
      after native finalStore finalMap finalWorld faults) : outcome = .value (.word word) := by
  have represented := result.2.1
  rw [outputWord] at represented
  exact represented_word succeeded requested exported represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicEmptyInputRegistry
/-! Empty public argument encoding preserves the original session's metadata
registry. The receipt uses the actual startup encoder and retains its exact
context; neither Source typing nor a value representation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.empty_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key [] fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry) : encodedValues.registry = registry := by
  exact started.simple_registry atRegistry (by intro argument member; cases member)


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionInputRegistry
/-! Actual input encoding of an authenticated function handle preserves the
metadata registry, including when the handle was retained across earlier calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Frontend SourceInference

theorem StartAt.function_registry
    {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {key : SourceCoreIndexedSession.Key}
    {handle : SourceCorePublicValues.Handle}
    {fuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {recipe : SourceCoreIndexedSession.Recipe} {root : SourceCoreIndexedSession.Root recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    (started : StartAt session key [.function handle] fuel checkpoint recipe root
      world store native encodedValues)
    (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  have unchanged := started.original.function_registry
  cases checkpoint
  cases session
  exact (congrArg SourceCoreCompatibleValues.Context.registry started.values).symm.trans
    (unchanged.trans atRegistry)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
end
