import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreAllocationContexts
import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.Frontend.SourceCoreCallableViewLowering

/-! Compile source allocation metadata through the common compiler twice.
The discovery pass retains its actual compiler equation. Its reached requests
determine one shared nominal-definition suffix. The second pass authenticates
each request against that inventory and emits ordinary Core allocation code.
Entries and checkpoints are checked against this complete definition list.

Source inputs use the original admission plan and cached globals. No source
expression is evaluated by this runtime. Source heap export is a separate
consumer of the allocation ledger. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev Representation := SourceCoreGeneralFunctions.Representation

structure ViewTable where
  program : CheckedProgram
  plan : SourceSpecializationWorklist.Plan
  table : SourceCoreCallableViews.Table program plan

inductive Error where
  | contexts (error : SourceCoreAllocationContexts.Error)
  | discovery (error : SourceCoreAllocationDiscovery.Error)
  | layouts (error : SourceCoreAllocationLayouts.Error)
  | functions (error : SourceCoreGeneralFunctions.Error)
  | inputs (error : SourceCoreCompatibleInputs.Error)
  | native (error : SourceCoreGeneralEntry.NativeCompileError)
  | diagnosticsUnavailable
  | missingRoot (key : Key)
  | views (error : SourceCoreCallableViews.Error)
  deriving Repr

def packClosures : List Core.Expr → Core.Expr
  | [] => .unit
  | expression :: rest => .pair expression (packClosures rest)

mutual
  /-- Count Core nodes and branch-list links, independently of source or
  runtime fuel. Lowered helpers and the number of cached functions contribute. -/
  def scanBudget : Core.Expr → Nat
    | .unit | .bool _ | .word _ | .integer _ | .var _ => 1
    | .construct _ payload | .first payload | .second payload | .loadCell payload
    | .unary _ payload | .lambda _ _ payload | .inLeft _ payload | .inRight _ payload
    | .newCell _ payload => 1 + scanBudget payload
    | .pair left right | .apply left right | .storeCell left right | .binary _ left right
    | .letE left right => 1 + scanBudget left + scanBudget right
    | .caseE condition left right | .ifE condition left right | .ternary _ condition left right =>
      1 + scanBudget condition + scanBudget left + scanBudget right
    | .matchData _ _ scrutinee branches => 1 + scanBudget scrutinee + scanBranchesBudget branches
  def scanBranchesBudget : List Core.Expr → Nat
    | [] => 1
    | expression :: rest => 1 + scanBudget expression + scanBranchesBudget rest
end

def discoveryRepresentation {checked : Checked} (base : Base checked) (fuel : Nat)
    (discovery : SourceCoreAllocationDiscovery.Prepared)
    (views : Option (SourceCoreCallableViews.Table base.sourceProgram base.plan) := none) : Representation :=
  {SourceCoreCompatibleFunctions.representation (.initial checked) fuel with
    allocatorAt := fun owner active => some (discovery.allocatorAt owner active
      (fun error => .sourceAllocation (reprStr error)))
    localReadView := fun owner active source _ read lowered =>
      match views with
      | none => pure lowered
      | some views => (SourceCoreCallableViewLowering.lower views owner active source read lowered)
          |>.mapError (fun error => .callableMetadata (reprStr error))}

def markedRepresentation (checked : Checked) (fuel : Nat) (layouts : Layouts)
    (views : Option ViewTable := none) : Representation :=
  {SourceCoreCompatibleFunctions.representation (.initial checked) fuel with
    allocatorAt := fun owner active => some (layouts.allocatorAt owner active
      (fun error => .sourceAllocation (reprStr error)))
    localReadView := fun owner active source _ read lowered =>
      match views with
      | none => pure lowered
      | some views => (SourceCoreCallableViewLowering.lower views.table owner active source read lowered)
          |>.mapError (fun error => .callableMetadata (reprStr error))}

/-- This is the actual shared contextual function compiler, with its retained
diagnostic and local-evidence inventories. -/
def compileClosures {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) : Except Error (List Core.Expr) := do
  if base.functions.isEmpty then pure [] else
    let diagnostics ← match base.diagnostics with
      | none => throw .diagnosticsUnavailable
      | some diagnostics => pure diagnostics.program
    let diagnostics := match base.callableContext with
      | none => diagnostics
      | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
    (base.functions.mapM (SourceCoreGeneralFunctions.compileClosureWithRepresentation
      base.sourceProgram representation base.sourceProgram.signatures base.plan base.globals
      diagnostics base.locals base.callableContext fuel)).mapError Error.functions

structure Compilation {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) where private mk ::
  closures : List Core.Expr
  compiled : compileClosures base representation fuel = .ok closures

def compileWithReceipt {checked : Checked} (base : Base checked) (representation : Representation)
    (fuel : Nat) : Except Error (Compilation base representation fuel) :=
  match compiled : compileClosures base representation fuel with
  | .error error => .error error
  | .ok closures => .ok ⟨closures, compiled⟩

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
  views : SourceCoreCallableViews.Table base.sourceProgram base.plan
  viewsPrepared : SourceCoreCallableViews.prepare base = .ok views
  contexts : SourceCoreAllocationContexts.Inventory base.plan base.contexts
  contextsPrepared : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok contexts
  discovery : SourceCoreAllocationDiscovery.Prepared
  discoveryPrepared : SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.contexts = .ok discovery
  firstPass : Compilation base (discoveryRepresentation base fuel discovery (some views)) fuel
  discovered : SourceCoreAllocationDiscovery.Discovered discovery (scanBudget (packClosures firstPass.closures))
    (packClosures firstPass.closures)
  scanned : SourceCoreAllocationDiscovery.discover discovery (scanBudget (packClosures firstPass.closures))
    (packClosures firstPass.closures) = .ok discovered
  layouts : Layouts
  layoutsPrepared : SourceCoreAllocationLayouts.prepare discovered = .ok layouts
  secondPass : Compilation base (markedRepresentation checked fuel layouts
    (some ⟨base.sourceProgram, base.plan, views⟩)) fuel
  sourceInputs : SourceInputs checked layouts
  entries : List (Entry layouts)

def prepare {checked : Checked} (base : Base checked) (fuel : Nat) : Except Error (Prepared checked) := do
  let views ← match accepted : SourceCoreCallableViews.prepare base with
    | .error error => throw (.views error)
    | .ok views => pure (⟨views, accepted⟩ : {views // SourceCoreCallableViews.prepare base = .ok views})
  let contexts ← match accepted : SourceCoreAllocationContexts.fromPrepared base.plan base.contexts with
    | .error error => throw (.contexts error)
    | .ok inventory => pure (⟨inventory, accepted⟩ : {inventory //
        SourceCoreAllocationContexts.fromPrepared base.plan base.contexts = .ok inventory})
  let discovery ← match accepted : SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.val.contexts with
    | .error error => throw (.discovery error)
    | .ok discovery => pure (⟨discovery, accepted⟩ : {discovery //
        SourceCoreAllocationDiscovery.prepare checked.catalog.definitions contexts.val.contexts = .ok discovery})
  let firstPass ← compileWithReceipt base (discoveryRepresentation base fuel discovery.val (some views.val)) fuel
  let discovered ← match accepted : SourceCoreAllocationDiscovery.discover discovery.val
      (scanBudget (packClosures firstPass.closures)) (packClosures firstPass.closures) with
    | .error error => throw (.discovery error)
    | .ok discovered => pure (⟨discovered, accepted⟩ : {discovered //
        SourceCoreAllocationDiscovery.discover discovery.val (scanBudget (packClosures firstPass.closures))
          (packClosures firstPass.closures) = .ok discovered})
  let layouts ← match accepted : SourceCoreAllocationLayouts.prepare discovered.val with
    | .error error => throw (.layouts error)
    | .ok layouts => pure (⟨layouts, accepted⟩ : {layouts //
        SourceCoreAllocationLayouts.prepare discovered.val = .ok layouts})
  let secondPass ← compileWithReceipt base (markedRepresentation checked fuel layouts.val
    (some ⟨base.sourceProgram, base.plan, views.val⟩)) fuel
  let sourceInputs ← prepareInputs checked base layouts.val
  let entries ← base.plan.seedKeys.mapM fun key => do
    let function ← match base.functions.find? (fun function => decide (function.signature.key = key)) with
      | none => throw (.missingRoot key)
      | some function => pure function
    let arguments := SourceCoreCalls.packArguments (function.inputs.zipIdx.map fun ((_, type), index) =>
      ⟨type, Core.OptionalCell.read type (.var (base.globals.length + function.inputs.length - 1 - index)) Core.Word.zero⟩)
    let body ← (SourceCoreGeneralFunctions.assembleCall base.globals base.functions secondPass.closures key arguments)
      |>.mapError Error.functions
    let native ← (SourceCoreGeneralEntry.NativeEntry.compile layouts.val.definitions (function.inputs.map Prod.snd)
      function.signature.resultType body).mapError Error.native
    pure (Entry.mk key (function.inputs.map Prod.fst) function.specialized.function.inferredBodyType native)
  pure ⟨base, fuel, views.val, views.property, contexts.val, contexts.property, discovery.val, discovery.property,
    firstPass, discovered.val, discovered.property, layouts.val, layouts.property, secondPass, sourceInputs, entries⟩

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

end Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
