import Solcore.Frontend.SourceCoreCallableAncestry
import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions

/-! Own one administrative callable frame alongside source-allocation markers.
Both passes use the actual common contextual compiler and the same cached
ancestry metadata. Native entries and resumable results retain the complete
frame/marker definition suffix. Public source inputs keep the original cached
admission plan. The source heap excludes the administrative frame cell.

This factory connects Core frame execution, not source closure reconstruction
or the complete source/Core meaning theorem. Those consume its owned receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPrograms
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev Representation := SourceCoreGeneralFunctions.Representation

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | discovery (error : SourceCoreAllocationDiscovery.Error)
  | layouts (error : SourceCoreAllocationLayouts.Error)
  | compilation (error : SourceCoreCompatibleMarkedFunctions.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | missingRoot (key : Key)
  | ancestry (error : SourceCoreCallableAncestry.Error)
  deriving Repr

def discoveryRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : Representation :=
  SourceCoreCallableAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.discoveryRepresentation base fuel discovery)

def markedRepresentation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (fuel : Nat) (layouts : Layouts) : Representation :=
  SourceCoreCallableAncestry.representation ancestry (SourceCoreCompatibleMarkedFunctions.markedRepresentation checked fuel layouts)

def assembleCall {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base) (closures : List Core.Expr)
    (key : Key) (arguments : SourceCoreBasic.LoweredExpr) : Except Error Core.Expr := do
  let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions closures key arguments).mapError Error.functions
  pure (SourceCoreCallableContextFrames.allocate ancestry.layout.frame body)

structure Entry (layouts : Layouts) where private mk ::
  key : Key
  inputs : List TypedBinder
  sourceResultType : TypeSystem.Ty
  native : SourceCoreGeneralEntry.NativeEntry layouts.definitions

structure SourceInputs (checked : Checked) (layouts : Layouts) where private mk ::
  context : SourceCoreCompatibleInputs.Context
  valuesExact : context.values = SourceCoreCompatibleValues.Context.initial checked
  definitionsExact : context.definitions = layouts.definitions

private def prepareInputs (checked : Checked) (base : Base checked) (layouts : Layouts) :
    Except Error (SourceInputs checked layouts) :=
  match accepted : SourceCoreCompatibleInputs.prepare (.initial checked) base.plan base.globals
      (base.callableContext.map (·.table)) layouts.definitions Core.Word.zero (some base.validationPlan) with
  | .error error => .error (.inputs error)
  | .ok context => .ok ⟨context, SourceCoreCompatibleInputs.prepare_values accepted, by
      unfold SourceCoreCompatibleInputs.prepare at accepted
      split at accepted
      · contradiction
      · cases accepted; rfl⟩

structure Prepared (checked : Checked) where private mk ::
  base : Base checked
  fuel : Nat
  ancestry : SourceCoreCallableAncestry.Prepared base
  ancestryPrepared : SourceCoreCallableAncestry.prepare base = .ok ancestry
  contexts : SourceCoreAllocationContexts.Inventory base.plan base.contexts
  contextsPrepared : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok contexts
  discovery : SourceCoreAllocationDiscovery.Prepared
  discoveryPrepared : SourceCoreAllocationDiscovery.prepare ancestry.layout.definitions contexts.contexts = .ok discovery
  firstPass : SourceCoreCompatibleMarkedFunctions.Compilation base (discoveryRepresentation ancestry fuel discovery) fuel
  discovered : SourceCoreAllocationDiscovery.Discovered discovery (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
    (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures)
  scanned : SourceCoreAllocationDiscovery.discover discovery (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
    (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) = .ok discovered
  layouts : Layouts
  layoutsPrepared : SourceCoreAllocationLayouts.prepare discovered = .ok layouts
  secondPass : SourceCoreCompatibleMarkedFunctions.Compilation base (markedRepresentation ancestry fuel layouts) fuel
  sourceInputs : SourceInputs checked layouts
  entries : List (Entry layouts)

def prepare {checked : Checked} (base : Base checked) (fuel : Nat) : Except Error (Prepared checked) := do
  let ancestry ← match accepted : SourceCoreCallableAncestry.prepare base with
    | .error error => throw (.ancestry error)
    | .ok ancestry => pure (⟨ancestry, accepted⟩ : {ancestry // SourceCoreCallableAncestry.prepare base = .ok ancestry})
  let contexts ← match accepted : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts with
    | .error error => throw (.contexts error)
    | .ok inventory => pure (⟨inventory, accepted⟩ : {inventory //
        SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok inventory})
  let discovery ← match accepted : SourceCoreAllocationDiscovery.prepare ancestry.val.layout.definitions contexts.val.contexts with
    | .error error => throw (.discovery error)
    | .ok discovery => pure (⟨discovery, accepted⟩ : {discovery //
        SourceCoreAllocationDiscovery.prepare ancestry.val.layout.definitions contexts.val.contexts = .ok discovery})
  let firstPass ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt base (discoveryRepresentation ancestry.val fuel discovery.val) fuel).mapError Error.compilation
  let discovered ← match accepted : SourceCoreAllocationDiscovery.discover discovery.val
      (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures)) (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) with
    | .error error => throw (.discovery error)
    | .ok discovered => pure (⟨discovered, accepted⟩ : {discovered //
        SourceCoreAllocationDiscovery.discover discovery.val (SourceCoreCompatibleMarkedFunctions.scanBudget (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures))
          (SourceCoreCompatibleMarkedFunctions.packClosures firstPass.closures) = .ok discovered})
  let layouts ← match accepted : SourceCoreAllocationLayouts.prepare discovered.val with
    | .error error => throw (.layouts error)
    | .ok layouts => pure (⟨layouts, accepted⟩ : {layouts //
        SourceCoreAllocationLayouts.prepare discovered.val = .ok layouts})
  let secondPass ← (SourceCoreCompatibleMarkedFunctions.compileWithReceipt base (markedRepresentation ancestry.val fuel layouts.val) fuel).mapError Error.compilation
  let sourceInputs ← prepareInputs checked base layouts.val
  let entries ← base.plan.seedKeys.mapM fun key => do
    let function ← match base.functions.find? (fun function => decide (function.signature.key = key)) with
      | none => throw (.missingRoot key)
      | some function => pure function
    let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
      ⟨type, Core.OptionalCell.read type (.var (base.globals.length + 1 + function.inputs.length - 1 - index)) Core.Word.zero⟩)
    let body ← assembleCall ancestry.val secondPass.closures key arguments
    let native ← (SourceCoreGeneralEntry.NativeEntry.compile layouts.val.definitions (function.inputs.map Prod.snd)
      function.signature.resultType body).mapError Error.native
    pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
  pure ⟨base, fuel, ancestry.val, ancestry.property, contexts.val, contexts.property,
    discovery.val, discovery.property, firstPass, discovered.val, discovered.property,
    layouts.val, layouts.property, secondPass, sourceInputs, entries⟩

def Prepared.find? {checked : Checked} (prepared : Prepared checked) (key : Key) : Option (Entry prepared.layouts) :=
  prepared.entries.find? (fun entry => decide (entry.key = key))

inductive RunError where
  | missingEntry (key : Key)
  | input (error : SourceCoreCompatibleInputs.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | compile (error : SourceCoreGeneralEntry.NativeCompileError)
  | native (error : SourceCoreGeneralEntry.RunError)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  deriving Repr

structure Result {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts) where private mk ::
  context : SourceCoreCompatibleValues.Context
  contextOwner : context.checked = checked
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry context.registry
  diagnostics : SourceCoreFaultSites.Table
  native : SourceCoreGeneralEntry.Result prepared.layouts.definitions entry.native.resultType

structure Completion {checked : Checked} (prepared : Prepared checked) where private mk ::
  entry : Entry prepared.layouts
  result : Result prepared entry

private def diagnosticTable {checked : Checked} (prepared : Prepared checked) (entry : Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) : Except RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Core.Word.zero }
  pure <| match prepared.base.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

def Prepared.runSource {checked : Checked} (prepared : Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (executionFuel : Nat) (validationFuel : Nat := 256) :
    Except RunError (Completion prepared) := do
  let entry ← match prepared.find? key with
    | none => throw (.missingEntry key)
    | some entry => pure entry
  let ready := prepared.sourceInputs
  let encoded ← (SourceCoreCompatibleInputs.encode ready.context (entry.inputs.map (·.scheme.body))
    arguments validationFuel).mapError RunError.input
  have extension : SourceCoreRawMetadata.Extends checked.staticRegistry encoded.values.registry := by
    change SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial checked).registry _
    rw [← ready.valuesExact]
    exact encoded.preserves
  let context := (SourceCoreCompatibleValues.Context.initial checked).extend encoded.values.registry extension
  let body ← (SourceCoreGeneralFunctions.assembleCall prepared.base.globals prepared.base.functions
    prepared.secondPass.closures key ⟨encoded.type, encoded.expression⟩).mapError RunError.functions
  let body := SourceCoreCallableContextFrames.allocate prepared.ancestry.layout.frame body
  let native ← match accepted : SourceCoreGeneralEntry.NativeEntry.compile prepared.layouts.definitions []
      entry.native.resultType body with
    | .error error => throw (.compile error)
    | .ok runner =>
        let result ← (runner.run [] executionFuel).mapError RunError.native
        have resultType := (SourceCoreGeneralEntry.NativeEntry.compile_fields accepted).2.1
        pure (resultType ▸ result)
  let table ← diagnosticTable prepared entry encoded.values.registry extension
  pure ⟨entry, ⟨context, rfl, extension, table, native⟩⟩

def Completion.resume {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (fuel : Nat) : Completion prepared :=
  match completion.result.native.checkpoint? with
  | none => completion
  | some checkpoint => ⟨completion.entry, {completion.result with native := checkpoint.resume fuel}⟩

end Solcore.Frontend.SourceCoreCallableAncestryPrograms
