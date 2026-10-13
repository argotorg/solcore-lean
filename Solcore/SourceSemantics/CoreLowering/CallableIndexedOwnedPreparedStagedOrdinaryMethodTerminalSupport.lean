import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport

/-! The genuine retained ordinary terminal body supplies each selected mixed
root with its complete caller dictionary and actual method selection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport (SelectedBody)
variable {directSites : DeclarationInstantiation → Prop}
  {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (code : Code compiled.indexed function scope administrative)
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (supported : ∀ instantiation, directSites instantiation →
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported code.compilation.plan instantiation)
  (metadata : MetadataFor compiled.indexed support.caller.named function.source directSites)
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
  (covered : ∀ instantiation, directSites instantiation → ∀ index signature,
    SourceCompilationPlan.exactInstantiationKey code.compilation.plan instantiation = .ok signature.key →
    code.compilation.globals[index]? = some signature →
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
      header.slot = index ∧ header.named.signature = signature)
  {loaded : LoadedProgram}
  (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)

local notation "stages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
local notation "headers" => CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows


include receiver wellFormed supported metadata rows covered checked catalog methods signatureMember sourceOwner provenance in
/-- The accepted terminal callback yields the original method-aware expression
root at every genuine selected Source scope. -/
theorem of_actual
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (tree : GeneralSyntax function.source expression directSites)
    (child : Staging.Recursive.Scope) (selected : (stages).Closure function child) :
    Nonempty (Σ packet : Terminal code stages,
      SelectedBody («headers» := headers) code support.body.toContext stages packet faults) := by
  obtain ⟨packet, expressionEq, callback, reason, _child, point, prefixEq⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinaryTerminalChoice.of_actual code support provenance
      expression terminal child selected
  refine ⟨⟨packet, { point := point, readFuel := compiled.indexed.fuel, «prefix» := prefixEq, roots := ?_ }⟩⟩
  intro selectedChild selectedAt
  apply Classical.choice
  have sameSource := (stages).source selectedAt
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code support.body.toContext support.body.frame
    provenance.scope_declarations selectedAt
  obtain ⟨node, found, rawType, typed⟩ :=
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_raw_type
      code packet support.body.toContext support.body.frame selectedChild selectedAt
  have accepted := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.accepted_view_action code packet callback reason
  obtain ⟨⟨actualType, root⟩⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedRoots.of_child stagePrepared code support provenance
      receiver wellFormed supported metadata rows covered checked catalog methods signatureMember sourceOwner
      selectedAt (Dynamic.RuntimeContextFields.refl _)
      (by simpa only [sameSource] using declarations)
      (expressionEq.symm ▸ tree)
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.terminal_reached code packet)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) accepted
  have sameNode := Option.some.inj (root.found.symm.trans found)
  have resultEq : actualType = function.resultType := root.rawResult.symm.trans (sameNode ▸ rawType)
  exact ⟨resultEq ▸ root⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodTerminalSupport
