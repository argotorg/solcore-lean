import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedProgramAdmission (Selection)
open SelectedCompilationPreparedProgramCertificates (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedPreparedPhysicalProgramSupport (stagePrepared stages)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

include certificate bodies checked identity issued rows aligned in
theorem of_certificate
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : SelectedCompilationPhysicalClosureStaticSupport.PacketFor
        association (stages compiled),
      SelectedCompilationPhysicalClosureStaticSupport.SupportFor association
        (stages compiled) packet) := by
  cases association with
  | legacy original =>
    rcases original with ⟨original, _slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
      have found := code.sourceFound
      rw [support.source] at found
      obtain ⟨body⟩ := source.closures.selected found code.sourceForm
      cases body with
      | ordinary body =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationClosureAdmission.of_ordinary
          (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
          certificate.selection.operatorCatalog body
        exact ⟨⟨.terminal packet, supported⟩⟩
      | «scoped» body =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationScopedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
          certificate.selection.operatorCatalog body
        exact ⟨⟨.branching packet, supported⟩⟩
      | coerced enabled body =>
        cases selectionEq : certificate.selection with
        | closed methods catalog =>
          obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationCoercedClosureAdmission.of_actual
            (stagePrepared compiled) code support provenance issued bodies rows aligned checked identity
            catalog body
            (fun principal sourceAt diagnostic certified =>
              SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
                bodies.signatures certified (headers := headers rows) (stages compiled))
          exact ⟨⟨.terminal packet, supported⟩⟩
        | origins methods catalog =>
          simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      have found := code.sourceFound
      rw [support.source, support.principal.source_eq] at found
      cases certificate.selection with
      | closed methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
      | origins methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex typed provenance slots callerReceipt =>
    obtain ⟨caller⟩ := callerReceipt
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic certified =>
            SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
              bodies.signatures certified (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex typed provenance slots callerReceipt =>
    obtain ⟨caller⟩ := callerReceipt
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := SelectedCompilationPreparedBranchingCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance caller issued bodies rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic certified =>
            SelectedCompilationPrimitiveMethodAdmission.support methods principal sourceAt diagnostic issued
              bodies.signatures certified (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
