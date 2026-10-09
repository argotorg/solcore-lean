import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicPlaceMissingDiagnostics

/-! The selected compiler receipt supplies its original diagnostic issuer.
Only genuine full-Source unary and operand typing remain separate inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

/-- The actual cached Source and selected assignment row belong to the same
original compatible diagnostic preparation. The receiving root table may change. -/
theorem of_compilation
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    {lowered : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named lowered namedCode)
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : lowered = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled caller.named.signature.key (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program lowered := by
  obtain ⟨root, extra, prepared, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header caller found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have sameBase : lowered.base = diagnostics.program.base := by
    rw [actual]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  obtain ⟨first, assignmentsPrepared⟩ := SourceCoreProgramFaultSites.prepare_assignments_at
    basePrepared (CallableIndexedActualNamedSourceReceipts.header_record compiled caller) selected
  change SourceCoreAssignmentFaultSites.prepare (source caller.named) first =
    .ok compilation.own.assignments at assignmentsPrepared
  rw [caller.agreement.source] at collected
  let issued : IssuedSource compiled caller.named.signature.key (source caller.named) := {
    first := first
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := collected }
  exact ⟨issued, rfl, placeReasons_of_lowered diagnostics actual⟩

variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- This is the exact issuer owner stored by the already selected lambda Site. -/
theorem at_produced
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : produced.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = produced.compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program produced.diagnostics := by
  have owner : produced.site.code.compilation.owner = caller.named.signature.key := by
    rw [produced.site.compilation]
    rfl
  rw [owner]
  exact of_compilation caller produced.compilation found actual typing

/-- The existing same-root callback retains these literal compiler identities.
It transports the receipt to that original compilation without selecting again. -/
theorem at_callback
    {diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    {actualDiagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named actualDiagnostics namedCode)
    (diagnosticsEq : produced.diagnostics = actualDiagnostics)
    (namedCodeEq : produced.namedCode = namedCode)
    (compilationEq : HEq produced.compilation compilation)
    (found : compiled.indexed.base.diagnostics = some diagnostics)
    (actual : actualDiagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable})
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program actualDiagnostics := by
  have ownEq : produced.compilation.own = compilation.own := by
    cases diagnosticsEq
    cases namedCodeEq
    exact congrArg (fun retained => retained.own) (eq_of_heq compilationEq)
  obtain ⟨issued, assignments, places⟩ := at_produced caller produced found (diagnosticsEq.trans actual) typing
  exact ⟨issued, assignments.trans (congrArg (fun own => own.assignments) ownEq), diagnosticsEq ▸ places⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
