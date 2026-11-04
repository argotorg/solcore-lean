import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.AcceptedPackets
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping

/-!
# Prepared callables: bootstrap

Bootstrap root state, global references and recipes, physical bootstrap and root policy receipts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
/-! An aligned named Header exposes the literal contextual compiler action.
Its original cached slot and hook authenticate the same specialization record.
Successful action acceptance therefore produces the root policy receipt at
the original source, scope, reason and lowering, with its genuine predecessor
budget. No action or selection equality is assumed independently. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)
  {values : SourceCoreCompatibleValues.Context}
  {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values
    compiled.indexed.layouts.definitions (Program.ofChecked compiled.sourceProgram)}
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned

/-- The original Header policy forwards precisely this selected second-pass
contextual action, including its diagnostic issuer and callable context. -/
theorem header_action :
    header.policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression
      compiled.indexed.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext prepared.named.signature.key [])
      compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
      prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
      (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      compiled.indexed.base.callableContext none none := by
  rw [aligned.policy]
  rfl

/-- The real cached Header and hook select the same complete specialization.
The accepted expression action is unwrapped once at its successor budget. -/
theorem at_successor {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression (fuel + 1) source scope id header.reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics
      prepared.code prepared.compilation fuel source scope id header.reasonAt lowered) := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [aligned.named] at record
  rw [header_action prepared aligned] at accepted
  exact RootPolicyReceipt.of_accepted prepared.compilation record accepted

/-- Zero is rejected by the literal contextual traversal. The returned receipt
keeps the actual callback's predecessor budget rather than choosing another
lowering or silently changing the source occurrence. -/
theorem at_accepted {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      Nonempty (RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics
        prepared.code prepared.compilation predecessor source scope id header.reasonAt lowered) := by
  cases fuel with
  | zero =>
    rw [header_action prepared aligned] at accepted
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    change Except.error (SourceCoreBasic.Error.traversalExhausted (.occurrence id.occurrence)) = .ok lowered at accepted
    cases accepted
  | succ predecessor =>
    exact ⟨predecessor, rfl, at_successor prepared aligned accepted⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
/-! Original named compilation and observed lambda nodes produce physical
formation support. No execution law or full ordinary-header inventory is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

theorem of_actual
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal_parameters (registry := registry) (faults := faults) terminal
    prepared diagnostic wellFormed profile selected member found form owner requirements coercions ordinary read
    returnFound returnForm returnType
  simpa only [stages.evidence selected] using formed

/-- Original scoped body syntax and the accepted lambda compiler supply full
formation support before any closure body runs. -/
theorem of_branching
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :
    Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal) := by
  refine ⟨⟨point, ?_⟩⟩
  intro child selected
  have formed := CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation.of_terminal (registry := registry) (faults := faults) terminal
    prepared diagnostic receiver included wellFormed profile selected member found form owner requirements coercions ordinary read
    shape syntaxFor
  simpa only [stages.evidence selected] using formed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
/-! Actual finite issued Headers supply the cache ledger and empty Source
locals used by bootstrap. Distinct selected input slots remain a static
inventory condition; no Header ledger or desired entry facts are supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedNamedBootstrapReceipts
open RecursiveNamedCatalog

private theorem closures_of_same_pass {checked : SourceCoreCompatibleCatalog.Checked}
    {base : SourceCoreCompatibleMarkedFunctions.Base checked}
    {firstRepresentation secondRepresentation : SourceCoreGeneralFunctions.Representation}
    {firstFuel secondFuel : Nat}
    (representation : firstRepresentation = secondRepresentation) (fuel : firstFuel = secondFuel)
    {first : SourceCoreCompatibleMarkedFunctions.Compilation base firstRepresentation firstFuel}
    {second : SourceCoreCompatibleMarkedFunctions.Compilation base secondRepresentation secondFuel}
    (same : HEq first second) : first.closures = second.closures := by
  cases representation
  cases fuel
  exact congrArg (fun compiled => compiled.closures) (eq_of_heq same)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (inputs : List (Input compiled))
  (rows : Inventory inputs)

theorem slots : (headers rows).map (·.slot) =
    inputs.map (fun input => input.prepared.index) := by
  induction rows with
  | nil => rfl
  | cons packet rest previous =>
      simp only [headers, List.map_cons, packet.aligned.slot, previous,
        CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued]

theorem empty_locals : ∀ header, header ∈ headers rows →
    header.function.context.locals = [] := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  rw [packet.function]
  rfl

theorem cache : ∀ header, header ∈ headers rows →
    compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType) header.code) := by
  intro header member
  obtain ⟨input, receipt, retained, same⟩ := rows.mem_headers header member
  subst header
  have sameClosures := closures_of_same_pass receipt.aligned.representation
    receipt.aligned.compiledFuel receipt.aligned.secondPass
  simpa only [sameClosures] using receipt.header.cached

include wellFormed in
/-- All ledger fields are derived from authentic issued rows and the checked
program. The finite list must select each real physical slot at most once. -/
theorem ledger (distinct : (inputs.map (fun input => input.prepared.index)).Nodup) :
    Ledger (headers rows) compiled.indexed.secondPass.closures where
  slots := by rw [slots inputs rows]; exact distinct
  owners := wellFormed.function_ids
  cached := cache inputs rows

include wellFormed in
/-- The original entry factory runs once on the finite inventory. Global
sizes, empty locals and the entire cache ledger are internal conclusions. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (Bootstrap (headers := headers rows) functions registry world) :=
  CallableIndexedOwnedNamedBootstrapReceipts.of_recipe accepted
    (ledger wellFormed inputs rows distinct) (globals rows)
    (empty_locals inputs rows) functions registry

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
/-! The actual bootstrap constructs the owned state used by the public root.
The key is fixed before choosing a function model: initialized globals, no
capture prefix, and physical frame zero. Native completion fixes the complete
store, and store typing fixes the exact world. The original stored authority
supplies empty stable history, source heap representation and global reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

/-- The real initial frame is at zero; each global keeps its prepared slot. -/
def key (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Key compiled (Program.ofChecked compiled.sourceProgram) :=
  ⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot), 0, 0⟩

def keys (compiled : SourceCoreUnifiedCompilation.Compiled) :
    List (Key compiled (Program.ofChecked compiled.sourceProgram)) := [key compiled]

def owner (compiled : SourceCoreUnifiedCompilation.Compiled) : OwnedKey (keys compiled) :=
  ⟨⟨0, by simp [keys]⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- The original entry constructor retains the empty histories omitted by the
older existential bootstrap packet. Its actual native typing fixes the world. -/
private theorem initial
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (ledger : RecursiveNamedCatalog.Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ caller : State headers (keys compiled)
        ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
          ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
          SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      (∀ header, header ∈ headers →
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
          some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
            ((owner compiled).key.locations header))) ∧
      (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨world, entry, heaps, receipt⟩ :=
    RecursiveNamedCatalogPreparedInitializationReceipts.entry_with_constructor
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) compiled headers
      ledger sizes locals accepted rfl functions registry
  have worldEq := heaps.runtime_hasTypes.world_eq
  subst world
  let row : CallableIndexedAuthorityPool.EntryValid
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers (key compiled) []
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
    refine { authority := entry.authority, frame_eq := ?_ }
    change entry.authority.frameLocation = 0
    exact receipt.frameLocation
  let caller : State headers (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
    CallableIndexedAuthorityPool.Pool.singleton row
  refine ⟨caller, ?_, heaps, ?_, ?_⟩
  · intro selected
    have same : selected = (owner compiled).position := by
      apply Fin.ext
      have bound := selected.isLt
      change selected.val < 1 at bound
      change selected.val = 0
      omega
    subst selected
    change ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table entry.authority.current entry.authority.ghost metadata
    rw [receipt.current, receipt.ghost]
    exact ⟨none, .empty⟩
  · intro header member
    have reference : (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)) := by
      simpa only [List.length_nil, Nat.zero_add] using entry.globals header member
    rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
    exact reference
  · intro context cell member
    exact nomatch member

/-- Accepted finite rows derive their ledger, global sizes and empty locals.
The actual completed bootstrap fixes the returned native store before the
owned state is constructed. No initial pool, stable-row or heap law is supplied. -/
theorem of_completed
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      finalStore = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      ∃ caller : State (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled)
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨result, storeEq⟩ := RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed
  refine ⟨result, storeEq, ?_⟩
  rw [storeEq]
  exact initial accepted
    (CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.ledger wellFormed inputs rows distinct)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.globals rows)
    (CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.empty_locals inputs rows)
    functions registry

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
/-! Actual finite ordinary inputs and the completed native bootstrap establish
both the old semantic pool and every physical cache row, including methods.
No complete ordinary Header inventory or body execution premise is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The finite bootstrap owner's association is the actual installed layout. -/
theorem key_physical (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))) :
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical (owner compiled).key headers := by
  constructor
  · rfl
  · rfl
  · intro header _member
    rfl

theorem of_completed
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      finalStore = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled) 0).State
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨valueEq, storeEq, caller, stable, heaps, globals, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedBootstrapRootState.of_completed wellFormed inputs rows accepted distinct functions registry completed
  refine ⟨valueEq, storeEq, ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩,
    CallableIndexedOwnedPhysicalGlobals.of_completed accepted completed⟩, stable, heaps, globals, sourceTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
/-! The immutable public global environment retains each finite inventory
Header's actual reserved reference at every session state. This lookup uses
the accepted catalog slot and fixed bootstrap owner, without replaying
initialization or claiming a value at that location in the current store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (owner)

/-- Inventory provenance fixes the literal global reference independently of
the current heap and store. The owned caller carries the separate store facts. -/
theorem global_reference
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers rows) :
    (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        ((owner compiled).key.locations header)) := by
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
  subst header
  have selected : compiled.indexed.base.globals[packet.header.slot]? =
      some packet.header.named.signature := by
    rw [packet.aligned.slot, packet.aligned.named]
    exact input.slot.selected
  have reference := RecursiveNamedCatalogInitialization.global_reference
    compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame selected
  change (RecursiveNamedCatalogPreparedInitialization.environment compiled)[packet.header.slot]? =
    some (.cellRef (OptionalCell.cellType packet.header.named.signature.functionType)
      (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals packet.header.slot)) at reference
  rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
  exact reference

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationBounds
/-! Genuine graded ordinary and selected-method formation leaves retain the
compiler-qualified member, cells and result inside their actual reached
packet, in the formed state that holds the copies of the captured cells. Source preservation inverts the original lambda head. Native reflection
compares one actual factory result and assigns its own finite Source grade.
Receiving registry is explicit on every local ResultAt use. No legacy output
port, equal-registry premise or second factory call is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember CellOrigins functions Post)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The complete leaf output retains all real effects and the stronger facet
inside the original existential at the same reached packet. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins qualification headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context qualification profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The proved strong post is attached without selecting another state or
running formation again. Source admission belongs to that post's actual trace. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩}
    (related : (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached)
    (post : Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context qualification profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The actual Source value/fault head selects the authentic lambda. Exactly
one prepared formation establishes native completion and the stronger post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        captured code owner qualification profile support initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include qualified prefixContext observed prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Native completion is compared with one genuine formation. Its own Source
grade is obtained from that factory trace; preservation is not invoked again. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Ordinary.formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet) (prefixContext := prefixContext) (observed := observed)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      captured code owner qualification profile support initial packet formed nativeTrace member related post⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

/-- The selected-method leaf retains its own principal packet and dictionary.
The outer payload registry is independent of the retained body registry. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins qualification headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context qualification profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
          owner.key.frameLocation,
        StaticMember qualification headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (functions qualification headers keys bodyRegistry faults profile)) captured code history heap store
      owner.key.frameLocation)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore)
    (member : StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore)
    {reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩}
    (related : (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached)
    (post : Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context qualification profile code.sourceNode.type code.lowered.type
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
      (.value (.closure formed.closure)) formed.finalHeap (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) formed.finalStore :=
  ⟨nativeTrace, formed.finalMap, formed.finalWorld, post.result, post.cells, formed.maps, formed.worlds, formed.frame,
    formed.copy.metadata_extends, reached, related, post, formed, member⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Source inversion keeps the actual selected principal, then invokes one
prepared method formation at its original dictionary-bearing packet. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore,
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
        outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
      obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions evaluated
      obtain ⟨formed, _sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, _determined⟩ :=
        CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_post
          (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
          (support := support) (qualified := qualified) (prepared := prepared)
          (initial := initial) (packet := packet)
          (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
          (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
      obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
      exact ⟨_, formed.finalStore, result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        captured code owner qualification profile support initial packet formed nativeTrace member related post⟩
  | fault failed =>
      exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
        (program := Program.ofChecked compiled.sourceProgram) code support.body.unique coercions failed)

include qualified prepared cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- The native grade is independent of the Source grade obtained from one
actual method factory trace. The same strong post and reached pool are retained. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) captured code owner qualification profile support initial packet
        outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post⟩, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_post
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults) (captured := captured) (code := code) (owner := owner) (qualification := qualification) (profile := profile)
      (support := support) (qualified := qualified) (prepared := prepared)
      (initial := initial) (packet := packet)
      (cells := cells) (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals)
      (typed := typed) (sourceType := sourceType) (admitted := admitted) ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      captured code owner qualification profile support initial packet formed nativeTrace member related post⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
/-! Finite named Headers and their actual selected diagnostic issuers construct
the rich catalog profile at a genuine parameter entry. The enclosing native
collector supplies the coupled Tree and prepared plan once. Diagnostic table
identity and structural token equations are derived from the retained issuer;
no completed expression or body execution is a construction premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedPreparedNamedDiagnosticSources

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled → ExpressionId → Prop}
  {administrative : Core.Context}

/-- Project the authentic coupled compiler receipt into a rich profile. All
diagnostic alignment fields come from the same selected Header construction. -/
def of_collected
    (extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) (prepared packet) (issuer packet).typing.2
      (assignments_prepared packet)) :
    CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) packet.header administrative where
  row := input.row
  prepared := prepared packet
  instantiation := CallableNamedCanonicalOrder.retainedInstantiation input.row
  aligned := packet.aligned
  first := (issuer packet).first
  operandsTyped := (issuer packet).typing.2
  assignmentsPrepared := assignments_prepared packet
  extraction := extraction
  issued := issuer packet
  assignments := assignments packet
  operand := operand packet
  unary := unary packet
  projection := projection packet
  missing := missing packet

variable {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry packet.header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)

include recipeAccepted nativeMember functions owner complete entry in
/-- Invoke the actual enclosing-code collector once at the real parameter
state, then construct the profile without caller-supplied diagnostic identities. -/
theorem extract_at
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Children
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := packet.header) (administrative := administrative)) :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) packet.header administrative) := by
  obtain ⟨extraction⟩ := CallableIndexedOwnedPreparedDirectNamedProfileExtraction.extract_at
    (prepared packet) packet.aligned (issuer packet).typing.2 (assignments_prepared packet)
    recipeAccepted nativeMember functions owner complete entry wellFormed children
  exact ⟨of_collected packet extraction⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveNamedValueReceipts
/-! Named formation retains the actual bootstrap capture chosen by the
existing recipe. The reached read observes that same carrier, and the positive
function model stores its complete owner, Source dictionary and installed code.
Argument receipts use the same capture under the receiving model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveNamedValueReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key NamedSourceAt NamedInstalledCode)
open CallableIndexedOwnedFunctionEntries (OwnedPool)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins (Owner NamedAssociation functions)
open CallableIndexedOwnedPreparedBootstrapGlobalCallRecipes (Seed Recipe)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  (qualification : Facet compiled)
  {mapping : LocationMap} {world : StoreTyping}
  (origin : Owner (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (profile := profile))
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {seed : Seed (CallableIndexedLambdaValues.model compiled.indexed profile) origin header}
  (recipe : Recipe (CallableIndexedLambdaValues.model compiled.indexed profile) origin header seed mapping world)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD source)
  {identity : Word}
  (number : Word.ofNat? (header.slot + 1) = some identity)
  (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
    (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
    (LanguageResult.resultType header.named.signature.resultType)
    (header.code.rename recipe.capture.embedding.lift) recipe.capture.captured)
    header.named.signature.functionType compiled.indexed.layouts.definitions)

/-- The installed template is inherited from the same recipe capture. Map
and world extension leave its embedding and captured values unchanged. -/
theorem installed : NamedInstalledCode recipe.capture := by
  simpa only [Recipe.capture, NamedInstalledCode, CallableIndexedOwnedFunctionValues.NamedCapture.extend]
    using recipe.installed

/-- Construct the positive association from the real recipe and complete
carrier fields; no older function relation is inverted. -/
def association :
    NamedAssociation headers keys bodyRegistry profile mapping world
      header.named.specialized.function.type source (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
  .named origin recipe.member sourceAt recipe.capture (installed origin recipe)
    number projection descriptor typed

include sourceAt number projection typed in
/-- The receiving model records the same actual named carrier. -/
theorem represented
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedOwnedPreparedPositiveFunctionOrigins.PayloadOrigins qualification headers keys
      bodyRegistry registry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate sourceAt wellFormed
  have sameType : header.named.specialized.function.type = source.instantiation.type :=
    (congrArg (fun global => global.instantiation.type) sourceAt.retained).symm
  have callable := sameType.trans certified.callable_type
  have related : CallableIndexedOwnedPreparedPositiveFunctionOrigins.FunctionOrigins qualification headers keys
      bodyRegistry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) :=
    .global ⟨association origin recipe sourceAt number projection descriptor typed⟩
  rw [callable] at related ⊢
  exact .function related

include sourceAt number projection typed in
/-- The actual live read is for the literal recipe capture. The original
reference evaluator runs once and returns the same store and positive carrier. -/
theorem of_read {heap : Dynamic.Heap} {store : Store}
    {internalReason : Word} {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
    {canonical actual : Environment} {xi : Renaming}
    (pool : OwnedPool headers keys mapping world heap store)
    (entry : RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers origin.owner.key.locations origin.owner.key.capturePrefix callerPrefix scope
      mapping world heap store canonical)
    (agrees : EnvironmentsAgree xi canonical actual)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (read : store.read? (origin.owner.key.locations header) = some (.inRight .unit
      (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename recipe.capture.embedding.lift) recipe.capture.captured))) :
    let expression := LanguageResult.bind
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (SourceCoreFunctions.namedReference header.named.signature (xi (scope.length + callerPrefix + header.slot))
        identity internalReason)
      (LanguageResult.success (descriptor.wrap (.var 0)))
    Evaluates actual store expression (.inRight .word (recipe.carrier identity descriptor.id)) store ∧
    CallableIndexedOwnedPreparedPositiveFunctionOrigins.PayloadOrigins qualification headers keys
      bodyRegistry registry faults profile mapping world header.named.specialized.function.type
      (.global source) (recipe.carrier identity descriptor.id)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    (∀ result finalStore, Evaluates actual store expression result finalStore →
      result = .inRight .word (recipe.carrier identity descriptor.id) ∧ finalStore = store) := by
  dsimp only
  let capture := CallableIndexedOwnedFunctionEntries.named_capture_reached
    pool origin.owner recipe.member recipe.capture read
  have evaluation := NamedCalls.native_reference (identity := identity) (internalReason := internalReason)
    descriptor (entry.reindex agrees header recipe.member) capture.read
  exact ⟨evaluation, represented qualification origin recipe sourceAt number projection descriptor typed wellFormed,
    fun _ _ completed => Core.evaluation_deterministic completed evaluation⟩

variable
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {context : SourceSemantics.Context} {sourceTree : TypedSource}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
  (admitted : Admission bridge context initial)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context sourceTree)
  {calleeHeap : Dynamic.Heap} {arguments : List Dynamic.Value} {payloads : List Value}
  {types : List TypeSystem.Ty} {parameter result : TypeSystem.Ty} {packed : Dynamic.Value}
  (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
  (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
  (packing : Dynamic.ValuesPack arguments packed)
  (bundle : TypeSystem.Ty.productMany types = parameter)

include sourceAt bridge initial admitted runtime extension argumentsTyped packing bundle in
/-- Ordered argument admission uses the same positive model and bootstrap
owner. The recipe's actual capture is passed to the original named producer. -/
theorem at_arguments
    (currentRecipe : Recipe (CallableIndexedLambdaValues.model compiled.indexed profile) origin header seed
      index.mapping index.world)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global source) (.function parameter result))
    (representedArguments : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      index.mapping index.world header.bindings arguments payloads)
    (profiles : CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      (functions qualification headers keys bodyRegistry faults profile) origin.owner (header := header))
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (mapping := index.mapping) (world := index.world) (before := index.heap)
      (arguments := arguments) (payloads := payloads)
      (functions qualification headers keys bodyRegistry faults profile) (.global source) source.evidence
      (currentRecipe.carrier identity descriptor.id) header.function.resultType header.output :=
  CallableIndexedOwnedPreparedCatalogIndirectArgumentReceipts.named
    (functions qualification headers keys bodyRegistry faults profile)
    bridge initial admitted runtime extension argumentsTyped packing bundle
    origin.owner currentRecipe.member origin.capture_zero (origin.globals currentRecipe.member)
    sourceAt currentRecipe.capture identity descriptor.id sameLayouts wellFormed calleeTyped
    representedArguments profiles syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveNamedValueReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalRootPrefixTyping
/-! The actual selected method cache and prepared bootstrap bound one emitted
lambda to its genuine globals/frame prefix. Native entry typing then loses
only its unused wrapper input suffix before the original hook and marked
parameter fold are inverted. No ordinary Header, arbitrary body bound, Site
reindexing or Source execution law is an input. Child occurrence typing and
same-Site extraction remain separate static producer obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalRootPrefixTyping
open Core Frontend SourceInference

/-- The selected method's actual compiled body has exactly its canonical
parameter/global/frame prefix. The Source selector and dictionary remain in
the independent Principal; this theorem only derives native syntax typing. -/
theorem body_native_at_prefix
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    {recipe : SourceCoreIndexedSession.Recipe}
    (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext
        (principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
      principal.cached.compilation.body
      (LanguageResult.resultType principal.named.signature.resultType) compiled.indexed.layouts.definitions := by
  have selected : compiled.indexed.secondPass.closures[principal.cached.index]? = some
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output) := by
    simpa only [principal.cached.compilation.emitted] using principal.cached.cached
  have cachedTyped := CallableIndexedCachedNativeTyping.prepared_native_closure
    compiled.indexedPrepared member selected
    (CallableIndexedPreparedInventories.cached_global_at compiled principal.cached.selected)
  have cachedBound := RecursiveNamedCatalogPreparedInitialization.supported_cached recipeAccepted selected
  let leading : Core.Context := compiled.indexed.base.globals.map (·.referenceType) ++
    [.cell compiled.indexed.ancestry.layout.frame.type]
  have prefixed : HasType
      (leading ++ SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [leading, List.append_assoc, List.cons_append, List.nil_append] using cachedTyped
  have bounded : NativeExpressionContextSupport.supported
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      leading.length = true := by
    simpa only [leading, List.length_append, List.length_map, List.length_cons, List.length_nil,
      Nat.add_zero] using cachedBound
  have minimal : HasType leading
      (.lambda principal.named.signature.parameterType
        (LanguageResult.resultType principal.named.signature.resultType) principal.cached.compilation.output)
      principal.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [List.append_nil] using
      (NativeExpressionContextSupport.prefix_typing (targetSuffix := []) prefixed bounded)
  cases minimal with
  | lambda _ _ body =>
    simpa only [leading, CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix, List.append_assoc,
      List.cons_append] using CallableIndexedParameterNativeInversion.body_native principal.cached.compilation body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalRootPrefixTyping
end
