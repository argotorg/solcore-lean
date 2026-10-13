import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosedCoercionAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap

/-! One finite certificate checks actual cached roots, original lambda bodies,
method sources and coercion selection. Its issuer constructs the shared static
program support; independent Source well-formedness remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedPreparedPhysicalProgramSupport (stagePrepared stages Support)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

inductive RootCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) where
  | scoped (source : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows)
  | formation (source : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate compiled named)
  | scopedFactory (source : CallableIndexedOwnedPreparedScopedFactoryAdmission.Certificate compiled named)
  | excluded (absent : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
      named.specialized.declaration ≠ signature.id)

def certifyRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (fuel : Nat) : Option (RootCertificate compiled named directRows) :=
  match CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource compiled named
      named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows fuel with
  | some ⟨source⟩ => some (.scoped source)
  | none =>
    match CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory compiled named with
    | some source => some (.formation source)
    | none =>
      if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
          decide (named.specialized.declaration ≠ signature.id)) = true then
        some (.excluded (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member)))
      else none

inductive Selection (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | closed (methods : CallableIndexedOwnedPreparedPrimitiveMethodAdmission.Certificate compiled)
      (catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  | origins (methods : CallableIndexedOwnedPreparedScopedMethodAdmission.Certificate compiled directRows)
      (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)

def Selection.allowCoerced {compiled : SourceCoreUnifiedCompilation.Compiled}
    {directRows : List SourceSpecialization.SpecializedFunction} : Selection compiled directRows → Bool
  | .closed .. => true
  | .origins .. => false

def Selection.operatorCatalog {compiled : SourceCoreUnifiedCompilation.Compiled}
    {directRows : List SourceSpecialization.SpecializedFunction} :
    Selection compiled directRows → CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled
  | .closed _ catalog => .generic ⟨catalog.formed, catalog.assumptions⟩
  | .origins _ catalog => .origins catalog

def certifySelection (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (Selection compiled directRows) :=
  let closed := do
    let methods ← CallableIndexedOwnedPreparedPrimitiveMethodAdmission.certify compiled fuel
    let ⟨catalog⟩ ← CallableIndexedOwnedPreparedClosedCoercionAdmission.certify compiled
    pure (.closed methods catalog)
  match closed with
  | some selection => some selection
  | none => do
    let methods ← CallableIndexedOwnedPreparedScopedMethodAdmission.certify compiled directRows fuel
    let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
    pure (.origins methods catalog)

structure RowCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) where
  root : RootCertificate compiled named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named directRows allowCoerced

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) : Option (RowCertificate compiled named directRows allowCoerced) := do
  let root ← certifyRoot compiled named directRows fuel
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ named ∈ compiled.indexed.base.functions,
    Nonempty (RowCertificate compiled named table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

/-- A rejected row rejects the whole certificate. The direct-site table may
omit unused rows, but every actual cached source still receives a root check. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) : Option (Certificate compiled) := do
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof? (fun named => Nonempty (RowCertificate compiled named table.rows selection.allowCoerced))
        (fun named => do
          let certificate ← certifyRow compiled named table.rows selection.allowCoerced fuel
          pure ⟨⟨certificate⟩⟩) compiled.indexed.base.functions
      pure ⟨table, selection, rows, profile, diagnostics, present⟩
  else none

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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

include certificate wellFormed ready checked identity issued entryMember rows aligned in
theorem Certificate.named_support (input : Input compiled) (packet : Issued input) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body packet.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := initial.result.context.registry)
        (stages := stages compiled)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        packet.header body) := by
  obtain ⟨source⟩ := certificate.rows input.prepared.named (List.mem_of_getElem? input.prepared.selected)
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨packet.selected.diagnostics, packet.selected.found, rfl⟩
  cases source.root with
  | «scoped» admission =>
    have original := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.source_at_header
      prepared packet.aligned input.prepared.selected input.prepared.same admission
    exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared packet.aligned rows aligned
      original ready diagnostic issued wellFormed checked identity
      certificate.selection.operatorCatalog
      entryMember (stagePrepared compiled)
  | formation admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := CallableIndexedOwnedPreparedNamedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      wellFormed certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | scopedFactory admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := CallableIndexedOwnedPreparedScopedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      wellFormed certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | excluded absent =>
    obtain ⟨request, signature, generic, member, _genericMember, _resolved, specialized⟩ := input.prepared.origin
    have fields := RecursiveNamedSpecializationBodyFacts.identities specialized
    have declaration : input.prepared.named.specialized.declaration = signature.id :=
      (congrArg (·.declaration) input.prepared.same).trans (fields.2.2.trans fields.1.symm)
    exact False.elim (absent signature member declaration)

include certificate wellFormed checked identity issued rows aligned in
theorem Certificate.closure_support
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor
        association.original (stages compiled),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original
        (stages compiled) packet) := by
  rcases association with ⟨original, _slots⟩
  cases original with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic => methods.support principal sourceAt diagnostic issued wellFormed
            (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    cases certificate.selection with
    | closed methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
    | origins methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)

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

include certificate wellFormed ready checked identity issued registry entryMember rows aligned in
/-- Finite raw-row alignment is the only inventory adapter. All three semantic
families are issued internally from the single original-source certificate. -/
theorem Certificate.issue_for :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  have named : ∀ header, header ∈ headers rows →
      Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
          (headers := headers rows) (bodyRegistry := initial.result.context.registry)
          (stages := stages compiled)
          (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
          header body) := by
    intro header member
    obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
    cases same
    exact certificate.named_support wellFormed ready checked identity issued entryMember rows aligned input packet
  let namedChoice := fun header member => Classical.choice (named header member)
  let closureChoice := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) =>
    Classical.choice (certificate.closure_support wellFormed checked identity issued rows aligned association)
  refine ⟨{
    profile := certificate.profile
    wellFormed := wellFormed
    issued := issued
    registry := registry
    diagnostics := certificate.diagnostics
    bodies := fun header member => (namedChoice header member).1
    bodySupport := fun header member => (namedChoice header member).2
    closurePackets := fun association => (closureChoice association).1
    closureSupport := fun association => (closureChoice association).2
    owners := owners_physical rows
    methods := ?_ }⟩
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  cases certificate.selection with
  | closed methods _ =>
    obtain ⟨packet, same, supported⟩ := methods.support port.principal port.sourceAt
      ⟨port.diagnostics⟩ issued wellFormed (headers := headers rows) (stages compiled)
    exact ⟨.terminal packet, same, supported⟩
  | origins methods _ =>
    exact methods.support port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ issued wellFormed
      rows aligned ready entryMember (stages compiled)

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- The original public checker receipt retains its actual checking budget.
The separate static method receipt matches the compiler's method recheck. -/
theorem Certificate.issue_for_checked_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  exact certificate.issue_for wellFormed ready methods
    (CallableCoercionSelectionIdentity.Catalog.of_checked accepted) issued registry entryMember rows aligned

include certificate wellFormed ready issued registry entryMember in
/-- The automatic catalog issuer also retains the actual whole-program budget. -/
theorem Certificate.issue_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled compiled wellFormed
  exact ⟨catalog, certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember
    catalog.rows (certificate.table.aligned catalog) methods accepted⟩

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- An empty retained method catalog needs no additional body check. The actual
original checker receipt establishes that every method target is absent. -/
theorem Certificate.issue_for_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate wellFormed ready issued registry entryMember in
theorem Certificate.issue_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  certificate.issue_with_methods wellFormed ready issued registry entryMember
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- Original checker success supplies the method receipt at its actual budget. -/
theorem Certificate.issue_for_checked {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_checked accepted) accepted

include certificate wellFormed ready issued registry entryMember in
/-- Automatic catalog construction also accepts the actual original checking budget. -/
theorem Certificate.issue {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  certificate.issue_with_methods wellFormed ready issued registry entryMember
    (CallableMethodBodyCoherence.of_checked accepted) accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
