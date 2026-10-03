import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Initial context consumers start before a catalog Header. The whole actual
source must explicitly have no template IDs to obtain the old ordinary ledger
condition. Runtime/scoped validity retains templates and all unused rows.
Runtime audits are compiler observations, not proofs of program well-formedness. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedInitialContextValidity
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedInitialContextValidity GeneralHeap ReadOnly CompatiblePayload

section Frame
variable {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  (frame : NamedCalls.SourceFrame program instantiation body function)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (programTyped : ProgramWellFormed program)

include frame extended programTyped

/-- Scoped and runtime validity remain available for template-bearing sources;
coverage is the same frame dictionary, with the entire ledger retained. -/
theorem complete_ledger : ScopedRequirementLedgerWellFormed context function.source ∧
    RuntimeRequirementLedgerValid context ∧ function.evidence.Covers context ∧
    context.solvedRequirements = function.context.solvedRequirements :=
  ⟨scoped_ledger frame extended programTyped, runtime frame extended programTyped,
    covers frame extended, (mono_fields extended).solvedRequirements⟩

/-- The concrete literal semantic leaf receives computed initial validity,
without a Header.valid input or an execution premise for the source body. -/
theorem literal_preserves {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (templatesEmpty : function.source.localSchemeTemplateIds = [])
    (unique : NodeOccurrencesUnique function.source) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate function.context.solvedRequirements
        function.source id lowered) faults :=
  CompatibleExpressionLiterals.preserves functions program context function.evidence
    (of_templates_empty frame extended programTyped rfl templatesEmpty) unique faults

/-- Reflection uses native completion only; preservation and a prior source
trace are absent from the theorem's premises. -/
theorem literal_reflects {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (templatesEmpty : function.source.localSchemeTemplateIds = []) (faults : FunctionCalls.FaultRep) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel checked registry functions)
      program context function.evidence function.source
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate function.context.solvedRequirements
        function.source id lowered) faults :=
  CompatibleExpressionLiterals.reflects functions program context function.evidence
    (of_templates_empty frame extended programTyped rfl templatesEmpty) function.source faults
end Frame

section ActualCompilation
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
  {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  (programTyped : ProgramWellFormed (Program.ofChecked program))
  (signatureMember : signature ∈ program.signatures.functions) (genericMember : generic ∈ program.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
  (closed : named.specialized.assumptions = [])
  (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (extended : MonoBindersExtend named.specialized.function.typedBody.owner
    (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized).context
    named.specialized.function.typedBody.inputs types context)
  (templatesEmpty : named.specialized.function.typedBody.localSchemeTemplateIds = [])

include programTyped signatureMember genericMember accepted range closed inputs compiled extended templatesEmpty

theorem canonical_initial : CompatibleExpressionLiterals.ContextValid
    named.specialized.function.solvedRequirements context [] := by
  have frame := (RecursiveNamedSpecializationValidity.of_compilation signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range closed inputs compiled).2
  exact of_templates_empty frame extended programTyped rfl templatesEmpty

/-- Retained reverse substitution order produces the same complete body and
context; no equality of arbitrary dictionaries is used. -/
theorem retained_initial : CompatibleExpressionLiterals.ContextValid
    named.specialized.function.solvedRequirements context [] := by
  have frame := (RecursiveNamedSpecializationValidity.retained_of_compilation signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range closed inputs compiled).2
  exact of_templates_empty frame extended programTyped rfl templatesEmpty
end ActualCompilation

section Boundary
/-- Runtime validity alone deliberately permits assumption rows. It cannot
supply the old all-rows-valid condition without source-scoped facts. -/
theorem runtime_not_ordinary (id : RequirementId) (predicate : ProgramPredicate) :
    let row : SolvedRequirement := ⟨id, predicate, .assumption predicate⟩
    let context := (SourceSemantics.Context.ofSignatures ⟨[], [], [], [], [], []⟩).withSolvedRequirements [row]
    RuntimeRequirementLedgerValid context ∧ ¬ RequirementLedgerWellFormed context := by
  dsimp only
  constructor
  · constructor
    · simp [RequirementIdsUnique, Context.withSolvedRequirements]
    · intro row evidence member actual
      have same : row = ⟨id, predicate, .assumption predicate⟩ := by
        simpa [Context.withSolvedRequirements] using member
      subst row
      cases actual
  · intro valid
    have rowValid := valid.entriesValid ⟨id, predicate, .assumption predicate⟩ (by simp [Context.withSolvedRequirements])
    cases rowValid with
    | intro retained =>
      cases retained with
      | intro represents evidence =>
        cases represents with
        | assumption =>
          cases evidence with
          | assumption member => simp only [Context.withSolvedRequirements, Context.ofSignatures, List.not_mem_nil] at member
end Boundary


private def content : String := String.intercalate "\n" [
  "function bump(value: Word) returns (Word) { let extra: Word = 3; return value + extra; }",
  "function keep<T>(value: T) returns (T) { return value; }",
  "function fail(value: Word) returns (Word) { let missing: Word; return missing; }",
  "function wordRoot() returns (Word) { let kept: Word = 5; return bump(keep(kept)); }",
  "function boolRoot() returns (Bool) { return keep(true); }",
  "function faultRoot() returns (Word) { let kept: Word = 7; return fail(kept); }",
  "function empty() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word n)

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut rows := 0
  let mut inputs := 0
  for named in compiled.indexed.base.functions do
    let selected ← get "initial validity actual selected record"
      (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (selected == named.specialized) "initial validity changed the full selected record"
    let source := selected.function.typedBody
    let ledger := selected.function.solvedRequirements
    let context := (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram selected).context
    require (source.localSchemeTemplateIds.isEmpty && selected.assumptions.isEmpty)
      "initial validity ordinary fixture acquired templates or declaration assumptions"
    require (reprStr context.solvedRequirements == reprStr ledger &&
      reprStr context.assumptions == reprStr selected.assumptions && context.residualTypeVariables)
      "initial validity changed an ordered row, evidence or residual mode"
    require (decide (ledger.map (·.id)).Nodup) "initial validity duplicate requirement ID"
    require (reprStr source.inputs == reprStr (named.inputs.map Prod.fst))
      "initial validity prepared parameter order changed"
    for row in ledger do
      match row.evidence with
      | .implementation _ => pure ()
      | .assumption _ => throw (IO.userError "initial validity ordinary fixture retained an uncovered assumption")
    rows := rows + ledger.length
    inputs := inputs + source.inputs.length
  require (rows > 0 && inputs > 0) "initial validity did not exercise requirements and parameter installation"

/-- A real checked qualified local retains template assumption rows even when
its enclosing declaration has no assumptions. This is a checker-stage audit;
no full runtime compilation or Header is inferred for this fixture. -/
private def template_boundary : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "initial validity checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "initial validity qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "initial validity qualified body missing")
  let specialized ← get "initial validity actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let ids := specialized.function.typedBody.localSchemeTemplateIds
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "initial validity template boundary disappeared"
  require (specialized.function.solvedRequirements.map (·.id) == generic.solvedRequirements.map (·.id))
    "initial validity specialization removed or reordered template rows"
  for id in ids do
    let row ← match specialized.function.solvedRequirements.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "initial validity template row lost its unique original ID")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "initial validity template evidence was promoted to a declaration assumption"
    | _ => throw (IO.userError "initial validity unexpectedly rewrote a template to implementation evidence")

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected)
    s!"initial validity full source heap changed: {reprStr state.heap}"

def run : IO Unit := do
  template_boundary
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "initial context validity" content
    ["wordRoot", "boolRoot", "faultRoot", "empty"]
  inspect compiled
  let faultBinder ← match (compiled.indexed.base.functions.flatMap fun named =>
      SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == "missing") with
    | [binder] => pure binder.id
    | _ => throw (IO.userError "initial validity fault binder missing")
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("wordRoot", word 8, [(.word, some (word 5)), (.word, some (word 5)),
      (.word, some (word 5)), (.word, some (word 3))]),
    ("boolRoot", .bool true, [(.bool, some (.bool true))]),
    ("empty", .unit, [])]
  for budget in [0, 37, 151, 300000] do
    for (name, expected, heap) in successes do
      let started ← SourceCoreUnifiedCorpusSupport.execute compiled name [] budget
      let finished ← get "initial validity public resume" (started.resume 300000)
      match finished.observation with
      | .done actual state =>
        require (reprStr actual == reprStr expected) "initial validity completed value changed"
        cells state heap
      | other => throw (IO.userError s!"initial validity expected completion: {reprStr other}")
    let started ← SourceCoreUnifiedCorpusSupport.execute compiled "faultRoot" [] budget
    let finished ← get "initial validity public fault resume" (started.resume 300000)
    match finished.observation with
    | .fault (.uninitializedLocal actual) state =>
      require (actual == faultBinder) "initial validity first fault changed"
      cells state [(.word, some (word 7)), (.word, some (word 7)), (.word, none)]
    | other => throw (IO.userError s!"initial validity expected fault: {reprStr other}")
  IO.println "initial context validity actual ledger / templates / heaps / resume GREEN"

end Tests.SourceCoreRecursiveNamedInitialContextValidity
