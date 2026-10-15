import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramNamedSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramClosureSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPrimitiveMethodAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopedMethodAdmission
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
open Core Frontend SourceInference
open SelectedCompilationPreparedProgramCertificates (Certificate)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPhysicalProgramSupport (stagePrepared stages Support)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  {recipe : SourceCoreIndexedSession.Recipe} (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  (registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (entryMember : entry ∈ compiled.indexed.entries)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

private theorem owners_physical (rows : Inventory inputs) :
    ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys compiled),
      CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

include certificate bodyTyping ready checked identity issued registry entryMember rows aligned in
/-- Finite raw-row alignment is the only inventory adapter. All three semantic
families are issued internally from the single original-source certificate. -/
theorem issue_for :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  have named : ∀ header, header ∈ headers rows →
      Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
        SelectedCompilationPhysicalNamedBodySupport.Support
          (headers := headers rows) (bodyRegistry := initial.result.context.registry)
          (stages := stages compiled)
          (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
          header body) := by
    intro header member
    obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
    cases same
    exact SelectedCompilationProgramNamedSupport.named_support certificate bodyTyping ready checked identity issued entryMember rows aligned input packet
  let namedChoice := fun header member => Classical.choice (named header member)
  let closureChoice := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) =>
    Classical.choice (SelectedCompilationProgramClosureSupport.of_certificate certificate bodyTyping checked identity issued rows aligned association)
  refine ⟨{
    profile := certificate.profile
    bodyTyping := bodyTyping
    certificates := SelectedCompilationCatalog.certificates bodyTyping rows
    issued := issued
    registry := registry
    diagnostics := certificate.diagnostics
    bodies := fun header member => (namedChoice header member).1
    bodySupport := fun header member => (namedChoice header member).2
    closurePackets := fun association => (closureChoice association).1
    closureSupport := fun association => (closureChoice association).2
    owners := owners_physical rows
    methods := ?_ }⟩
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port selection
  have certified := SelectedCompilationMethodBodySupport.Certified.of_typed port.principal port.sourceAt selection
  cases certificate.selection with
  | closed methods _ =>
    obtain ⟨packet, same, supported⟩ := SelectedCompilationPrimitiveMethodAdmission.support methods port.principal port.sourceAt
      ⟨port.diagnostics⟩ issued bodyTyping.signatures certified (headers := headers rows) (stages compiled)
    exact ⟨.terminal packet, same, supported⟩
  | origins methods _ =>
    exact SelectedCompilationScopedMethodAdmission.support methods port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ issued bodyTyping certified
      rows aligned ready entryMember (stages compiled)

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- The original public checker receipt retains its actual checking budget.
The separate static method receipt matches the compiler's method recheck. -/
theorem issue_for_checked_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  exact issue_for certificate bodyTyping ready methods
    (CallableCoercionSelectionIdentity.Catalog.of_checked accepted) issued registry entryMember rows aligned

include certificate bodyTyping ready issued registry entryMember in
/-- The automatic catalog issuer also retains the actual whole-program budget. -/
theorem issue_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodyTyping
  exact ⟨catalog, issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember
    catalog.rows (certificate.table.aligned catalog) methods accepted⟩

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- An empty retained method catalog needs no additional body check. The actual
original checker receipt establishes that every method target is absent. -/
theorem issue_for_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate bodyTyping ready issued registry entryMember in
theorem issue_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  issue_with_methods certificate bodyTyping ready issued registry entryMember
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate bodyTyping ready issued registry entryMember rows aligned in
/-- Original checker success supplies the method receipt at its actual budget. -/
theorem issue_for_checked {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  issue_for_checked_with_methods certificate bodyTyping ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_checked accepted) accepted

include certificate bodyTyping ready issued registry entryMember in
/-- Automatic catalog construction also accepts the actual original checking budget. -/
theorem issue {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  issue_with_methods certificate bodyTyping ready issued registry entryMember
    (CallableMethodBodyCoherence.of_checked accepted) accepted

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationProgramSupportIssuer
