import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The real specialization retains the complete stage analysis. Independent
source structural properties, rather than native runtime types, establish its
normative classification. Comptime values are not evaluated by these proofs. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationStageFacts
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedSpecializationStageFacts

section Formal
variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_analysis :
    SourceStageAnalysis.analyzeFunction specialized.function = .ok specialized.stageAnalysis := analyzed accepted

theorem actual_graph (closed : OccurrenceGraphClosed generic.typedBody) :
    OccurrenceGraphClosed specialized.function.typedBody := graph_closed accepted closed

theorem actual_local_identities (owned : LocalIdentityOwnership generic.typedBody) :
    LocalIdentityOwnership specialized.function.typedBody := local_identities accepted owned

theorem actual_source_stages (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    Staging.FunctionHasStages specialized.function := has_stages accepted closed owned

theorem actual_program_stages {program : CheckedProgram}
    (programTyped : ProgramWellFormed (Program.ofChecked program)) (member : generic ∈ program.functions) :
    Staging.FunctionHasStages specialized.function := has_stages_of_program programTyped member accepted

/-- This exposes the independent input and root derivations produced by the
actual pass. Neither a prior FunctionHasStages nor a stage-evaluation law is an input. -/
theorem independent_inputs_and_roots (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    ∃ inputScope finalScope,
      Staging.FunctionInputsStage specialized.function.typedBody specialized.function.returnComptime
        specialized.function.inferredBodyType inputScope ∧
      Staging.RootsStage specialized.function.typedBody inputScope specialized.function.typedBody.roots finalScope := by
  cases has_stages accepted closed owned with
  | intro _ _ _ inputs roots => exact ⟨_, _, inputs, roots⟩
end Formal

theorem raw_stage_marker_matters :
    Staging.ComptimeOnlyType (.comptime .word) ∧ ¬Staging.ComptimeOnlyType .word := by
  refine ⟨.marked _, ?_⟩
  intro marked
  cases marked

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function mutable(value: Word) returns (Word) { let saved = value; saved = saved + 1; return saved; }",
  "function identity(comptime value: Word) returns (Word) { return value; }",
  "function dec(comptime value: integer) returns (comptime<integer>) { return integerSub(value, 1); }",
  "function caller() returns (Word) { return wordFromInteger(dec(10)); }",
  "function normal(value: Word) returns (Word) { return mutable(value); }",
  "function empty() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let program ← get "specialization stages checked program" (Frontend.checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let mut rows := 0
  let mut genericRows := 0
  let mut stagedInputs := 0
  let mut stagedReturns := 0
  let mut runtimeRows := 0
  let mut deferredRows := 0
  for generic in program.functions do
    let signature ← match program.signatures.functions.find? (·.id == generic.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "specialization stage signature missing")
    let supplied := signature.scheme.parameters.map fun parameter =>
      (parameter, if parameter.index % 2 == 0 then TypeSystem.Ty.word else TypeSystem.Ty.bool)
    let specialized ← get "specialization stages actual pass"
      (SourceSpecialization.specializeFunction signature generic supplied.reverse)
    let analyzed ← get "specialization stages actual retained analysis"
      (SourceStageAnalysis.analyzeFunction specialized.function)
    require (reprStr analyzed == reprStr specialized.stageAnalysis)
      "specialization stages full actual stage table changed"
    require (specialized.parameterSubstitution.map Prod.fst == signature.scheme.parameters &&
      specialized.function.returnComptime == generic.returnComptime &&
      specialized.function.typedBody.inputs.map (·.comptime) == generic.typedBody.inputs.map (·.comptime))
      "specialization stages full domain/raw input and result flags changed"
    require (reprStr specialized.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource specialized.parameterSubstitution generic.typedBody))
      "specialization stages full independent source changed"
    require (specialized.function.typedBody.roots == generic.typedBody.roots &&
      specialized.function.typedBody.nodes.map (·.occurrenceId) == generic.typedBody.nodes.map (·.occurrenceId))
      "specialization stages original graph occurrence identities changed"
    if !supplied.isEmpty then genericRows := genericRows + 1
    if specialized.function.typedBody.inputs.any (·.comptime) then stagedInputs := stagedInputs + 1
    if specialized.function.returnComptime then stagedReturns := stagedReturns + 1
    if analyzed.expressions.any (fun row => row.stage == .runtime) then runtimeRows := runtimeRows + 1
    if analyzed.expressions.any (fun row => row.stage == .deferred) then deferredRows := deferredRows + 1
    rows := rows + 1
  require (rows == 7 && genericRows == 1 && stagedInputs == 2 && stagedReturns == 1 && runtimeRows ≥ 2 && deferredRows ≥ 1)
    s!"specialization stage fixture coverage changed {rows}/{genericRows}/{stagedInputs}/{stagedReturns}/{runtimeRows}/{deferredRows}"
  IO.println "named specialization stages: real retained analysis, independent source graph/identities and comptime/runtime/deferred classification GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationStageFacts
