import Solcore.SourceSemantics.CoreLowering.NamedCallCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation

/-! Named generation sites retain the real second-pass body callback, marked
parameter prefix and entry hook. Exact plan selection identifies the complete
source of the installed seed; neither a native type nor a descriptor key alone
identifies a source graph. Runtime prefix preservation remains explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
open Core Frontend SourceInference
open CallableIndexedHistory
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Named := SourceCoreGeneralFunctions.Function

def context {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named) :
    SourceCoreFunctions.Context :=
  CompatibleNamedBody.bodyContext prepared.base.plan prepared.base.globals named

def representation {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :=
  SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts

def source (named : Named) : TypedSource := named.specialized.function.typedBody

def state (named : Named) : MetadataState := ⟨⟨named.signature.key, [], source named⟩, []⟩

def allocator {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named) :=
  SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))

def bodyAction {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (parents : List SourceCoreLocalEvidence.Prepared)
    (own : SourceCoreProgramFaultSites.Function) (statements : List StatementId) : Except SourceCoreBasic.Error Expr :=
  let actual := (representation prepared).atContext named.signature.key []
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation actual named.specialized.function.solvedRequirements
    own.assignments diagnostics named.signature.key
    (SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [])
    (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (context prepared named) prepared.base.callableContext none none)
    prepared.fuel (source named) (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) statements
    named.signature.resultType (diagnostics.reasonAt named.signature.key) own.fellThroughReason own.table.escapedReason

/-- This records compiler actions, not body execution. The body source and
empty parent substitution are fixed by the actual named compiler call. -/
structure Compilation {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : Named) (diagnostics : SourceCoreDataPlaceFaultSites.Program) (code : Expr) where private mk ::
  parents : List SourceCoreLocalEvidence.Prepared
  parentsPrepared : SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
    (prepared.base.locals.bindings.flatMap (·.instances)) = .ok parents
  own : SourceCoreProgramFaultSites.Function
  diagnostic : diagnostics.base.find? named.signature.key = some own
  statements : List StatementId
  roots : (source named).roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
    | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) = .ok statements
  body : Expr
  bodyCompiled : bodyAction prepared named diagnostics parents own statements = .ok body
  parameterCode : Expr
  parametersCompiled : SourceCoreSourceCells.bindParameters (allocator prepared named) (source named) [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection body = .ok parameterCode
  output : Expr
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameterCode = .ok output
  emitted : code = .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

theorem of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (accepted : SourceCoreGeneralFunctions.compileClosureWithRepresentation prepared.base.sourceProgram
      (representation prepared) prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
      diagnostics prepared.base.locals prepared.base.callableContext prepared.fuel named = .ok code) :
    Nonempty (Compilation prepared named diagnostics code) := by
  unfold SourceCoreGeneralFunctions.compileClosureWithRepresentation at accepted
  obtain ⟨parents, parentsPrepared, accepted⟩ := bind_ok accepted
  have parentsPrepared := mapError_ok parentsPrepared
  cases selected : diagnostics.base.find? named.signature.key with
  | none => simp [selected, bind, Except.bind, throw] at accepted
  | some own =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨statements, roots, accepted⟩ := bind_ok accepted
    obtain ⟨body, bodyCompiled, accepted⟩ := bind_ok accepted
    have bodyCompiled : bodyAction prepared named diagnostics parents own statements = .ok body := mapError_ok bodyCompiled
    change (do
      let parameterCode ← (SourceCoreSourceCells.bindParameters (allocator prepared named) (source named) [] named.inputs
        named.signature.resultType SourceCoreFunctions.argumentProjection body).mapError SourceCoreGeneralFunctions.Error.lowering
      let output ← (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameterCode).mapError SourceCoreGeneralFunctions.Error.lowering
      pure (Expr.lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)) = .ok code at accepted
    obtain ⟨parameterCode, parametersCompiled, accepted⟩ := bind_ok accepted
    obtain ⟨output, hook, emitted⟩ := bind_ok accepted
    exact ⟨⟨parents, parentsPrepared, own, selected, statements, roots, body, bodyCompiled, parameterCode,
      mapError_ok parametersCompiled, output, mapError_ok hook, (Except.ok.inj emitted).symm⟩⟩

/-- The sealed second pass supplies this receipt at the real global slot. -/
theorem compiled_at {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {index : Nat} {named : Named} (selected : prepared.base.functions[index]? = some named) :
    ∃ diagnostics code, prepared.secondPass.closures[index]? = some code ∧
      Nonempty (Compilation prepared named diagnostics code) := by
  obtain ⟨diagnostics, code, _, cached, compiled⟩ := NamedCalls.compiled_at prepared selected
  exact ⟨_, code, cached, of_accepted prepared compiled⟩

private theorem entry_of_id (table : SourceCoreStageCodebook.Table) {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (selected : table.idAt? origin = some id) :
    ∃ entry, table.entryAt? id = some entry ∧ entry.origin = origin := by
  unfold SourceCoreStageCodebook.Table.idAt? at selected
  cases found : table.entries.find? (fun entry => decide (entry.origin = origin)) with
  | none => simp [found] at selected
  | some entry =>
    have origin : entry.origin = origin := by simpa using List.find?_some found
    have identifier : entry.id = id := by simpa [found] using selected
    subst id
    exact ⟨entry, CallableAncestryPairedValidation.stage_entry_self table (List.mem_of_find?_eq_some found), origin⟩

/-- Full exact specialization, together with the actual descriptor selection,
fixes every seed field. No erasure of source metadata is used. -/
theorem seed {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {named : Named} {origin : Word}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    SourceCoreCallableAncestryPairedPreparation.named? prepared.ancestry.graph.inputs origin = some (state named) := by
  obtain ⟨entry, found, originEq⟩ := entry_of_id _ selected
  simp [SourceCoreCallableAncestryPairedPreparation.named?, SourceCoreCallableAncestryPreparation.named?, found,
    originEq, record, state, source, Except.toOption]

/-- The real named hook installs the exact source seed certified above. -/
theorem Compilation.history {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized) :
    ∃ origin, prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) (some (state named)) ∧
      compiled.output = SourceCoreCallableIndexedFrames.withFrame (.var (prepared.base.globals.length + 1))
        (SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) compiled.parameterCode := by
  obtain ⟨origin, index, selected, frame, emitted⟩ :=
    CallableIndexedFormation.namedBody_receipt prepared.ancestry compiled.hook
  exact ⟨origin, selected, named_complete prepared.ancestry.graph (seed prepared selected record), by rw [frame]; exact emitted⟩

/-- Runtime installation uses the real writable administrative location. The
source metadata is obtained from the hook and graph, independently of its read. -/
theorem installed {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {origin : Word} {before : Store} {location : Location} {saved : Value}
    (selected : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (read : before.read? location = some saved) :
    CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin)
      (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) := by
  have written : before.write? location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) = some
    (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
      (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
  exact ⟨Store.write?_reads_written written, .stable (named_complete prepared.ancestry.graph (seed prepared selected record))⟩

/-- A completed actual entry hook exposes the exact marked parameter child,
its real saved-frame slots and its installed named seed. This is native trace
inversion, with no premise asserting a source body execution. -/
theorem Compilation.entered {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {environment : Environment} {before finalStore : Store} {location : Location} {saved result : Value}
    (reference : environment[prepared.base.globals.length + 1]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : before.read? location = some saved)
    (completed : Evaluates environment before compiled.output result finalStore) :
    ∃ origin bodyStore,
      prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin) (some (state named)) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame location
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin) (.named origin)
        (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin))) ∧
      Evaluates (.unit :: saved :: environment)
        (before.set location (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
          (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)))
        ((compiled.parameterCode.weakenAt 0).weakenAt 0) result bodyStore ∧
      finalStore = bodyStore.set location saved := by
  obtain ⟨origin, selected, carried, emitted⟩ := compiled.history record
  rw [emitted] at completed
  obtain ⟨installedValue, nextStore, bodyStore, next, bodyRun, final⟩ :=
    CallableContextFrames.withFrame_reflects (.var reference) read completed
  have expected : Evaluates (saved :: environment) before
      ((SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)).weakenAt 0)
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame
        (SourceCoreCallableIndexedDispatch.namedFrame prepared.ancestry.graph.table origin)) before := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic next expected
  exact ⟨origin, bodyStore, selected, carried, installed selected record read, bodyRun, final⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
