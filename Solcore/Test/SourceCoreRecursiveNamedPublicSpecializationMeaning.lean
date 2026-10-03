import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Actual public worklist and cached receipts supply the generic source body,
complete dictionary and compiled roots. Formal consumers keep independent
source typing/raw range formation and arity. Runtime audits use actual parser,
checker, public compile and recipe preparation; they do not prove all staged
or constrained catalog execution from these source-only laws. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicSpecializationMeaning
open Solcore Frontend SourceInference TypeSystem SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPublicSpecializationMeaning

section Public
variable {program : CheckedProgram} {seeds : List SourceCompiler.Seed} {options : SourceCompiler.Options}
  {compiled : SourceCompiler.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
  (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
  (member : row ∈ recipe.compiled.validationPlan.specializations)

include accepted issued member

theorem actual_row : Nonempty (Prepared recipe.compiled row) :=
  of_public_compile accepted issued member

theorem actual_source_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures recipe.compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ prepared : Prepared recipe.compiled row,
      NamedCalls.SourceFrame (Program.ofChecked recipe.compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
        (RecursiveNamedSpecializationBodyFacts.bodyInstance recipe.compiled.sourceProgram row) prepared.view := by
  obtain ⟨prepared⟩ := actual_row accepted issued member
  exact ⟨prepared, prepared.source_frame wellFormed range⟩

end Public

section Meaning
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)

include prepared

theorem original_generic_body :
    ∃ signature generic supplied,
      signature ∈ compiled.sourceProgram.signatures.functions ∧ generic ∈ compiled.sourceProgram.functions ∧
      SourceSpecialization.specializeFunction signature generic supplied = .ok row ∧
      row.function.typedBody = StructuralSubstitution.applyTypedSource row.parameterSubstitution generic.typedBody ∧
      row.function.solvedRequirements = generic.solvedRequirements.map
        (StructuralSubstitution.applySolvedRequirement row.parameterSubstitution) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := prepared.origin
  exact ⟨signature, generic, request.parameterSubstitution, signatureMember, genericMember, accepted,
    RecursiveNamedSpecializationBodyFacts.body accepted, RecursiveNamedSpecializationBodyFacts.ledger accepted⟩

include wellFormed range

theorem generic_call_forward {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length)
    (executed : FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after) :
    NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after :=
  (prepared.call_outcome_iff wellFormed range arity).mp executed

theorem generic_call_backward {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length)
    (executed : NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after) :
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after :=
  (prepared.call_outcome_iff wellFormed range arity).mpr executed

theorem retained_source_frame :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view :=
  prepared.retained_frame wellFormed range

omit range in
theorem actual_stages : Staging.FunctionHasStages row.function := prepared.has_stages wellFormed

omit wellFormed range in
theorem full_dictionary {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence
      compiled.sourceProgram.signatures row.key row.assumptions actual = .ok ()) : actual = prepared.available :=
  prepared.authenticated_dictionary authenticated

end Meaning

section Boundaries
theorem budget_candidate_not_retained {program : CheckedProgram} {request : SourceSpecializationWorklist.Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (resolved : SourceSpecializationWorklist.resolveRequest program request = .ok specialized) :
    SourceSpecializationWorklist.run program [request] 0 = .ok
      (.budgetExhausted ⟨[specialized.key], [], [], []⟩ specialized.key [request]) :=
  SourceSpecializationWorklist.run_zero_single program request specialized resolved

theorem wrong_generic_declaration_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {row : SourceSpecialization.SpecializedFunction}
    (different : signature.id ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok row := by
  intro accepted
  exact different (RecursiveNamedSpecializationBodyFacts.identities accepted).1

end Boundaries

private def content : String := String.intercalate "\n" [
  "trait Marker<T> {}", "impl Marker<Word> {}",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
  "function relay<T>(value: T) returns (T) where T: Marker { return keep(value); }",
  "function recur<T>(value: T, count: Word) returns (T) { if (count == 0) { return value; } else { return recur(value, count - 1); } }",
  "function missing<T>(value: T) returns (T) { let absent: T; return absent; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function constrained(value: Word) returns (Word) where Word: Marker { return relay(value); }",
  "function recurRoot() returns (Word) { return recur(13, 3); }",
  "function faultRoot() returns (Word) { return missing(7); }"
]

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word := SourceCoreUnifiedCorpusSupport.word

private def inspect (program : CheckedProgram) (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut genericRows := 0
  let mut constrainedRows := 0
  let mut reverseRows := 0
  let mut fullLedger := 0
  for index in List.range cached.validationPlan.specializations.length do
    let row ← match cached.validationPlan.specializations[index]? with
      | some row => pure row | none => throw (IO.userError "original worklist row absent")
    let signature ← match program.signatures.functions.filter (·.id == row.declaration) with
      | [signature] => pure signature | _ => throw (IO.userError "original signature not singleton")
    let generic ← match program.functions.filter (·.declaration == row.declaration) with
      | [generic] => pure generic | _ => throw (IO.userError "original generic definition not singleton")
    let request : SourceSpecializationWorklist.Request := ⟨row.declaration, row.parameterSubstitution.reverse⟩
    let actual ← get "original full worklist resolution" (SourceSpecializationWorklist.resolveRequest program request)
    require (reprStr actual == reprStr row) "actual full specialization carrier changed"
    require (reprStr row.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution generic.typedBody))
      "independent generic source substitution changed"
    require (reprStr row.function.solvedRequirements == reprStr
      (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement row.parameterSubstitution)))
      "complete original ordered ledger changed"
    require (row.parameterSubstitution.map Prod.fst == signature.scheme.parameters)
      "canonical domain lost unused or ordered parameters"
    let retained ← match cached.indexed.base.plan.specializations[index]? with
      | some retained => pure retained | none => throw (IO.userError "original row was removed during method extension")
    require (reprStr retained == reprStr row) "method extension changed a full original carrier"
    let slot := cached.indexed.base.plan.specializations.length - 1 - index
    let named ← match cached.indexed.base.functions[slot]? with
      | some named => pure named | none => throw (IO.userError "original reverse mapM slot absent")
    require (reprStr named.specialized == reprStr row && named.signature.key == row.key)
      "cached native slot selected by key instead of complete row"
    require (named.inputs.map Prod.fst == row.function.typedBody.inputs)
      "actual named preparation changed original binder order"
    let available ← get "actual full dictionary resolver"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program row.key row.assumptions)
    let _ ← get "actual full dictionary authentication"
      (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures row.key row.assumptions available)
    require ((CallableNamedMetadata.environment available).map Prod.fst == row.assumptions)
      "actual full dictionary lost an assumption or its position"
    require (reprStr row.stageAnalysis == reprStr (← get "actual stage pass" (SourceStageAnalysis.analyzeFunction row.function)))
      "stored analysis was not produced by the actual specialization pass"
    fullLedger := fullLedger + row.function.solvedRequirements.length
    if !row.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if !row.assumptions.isEmpty then
      constrainedRows := constrainedRows + 1
      require (!available.isEmpty) "constrained source view acquired an empty dictionary"
    if row.parameterSubstitution.length == 2 then
      reverseRows := reverseRows + 1
      require (row.parameterSubstitution != row.parameterSubstitution.reverse) "distinct raw domain order collapsed"
  require (genericRows ≥ 5 && constrainedRows ≥ 3 && reverseRows == 2 && fullLedger > 0)
    s!"actual generic/dictionary/order coverage changed {genericRows}/{constrainedRows}/{reverseRows}/{fullLedger}"

/-- Read the complete original machine observation, including administrative
cells and every installed closure, beside its source export. -/
private def full_native (cached : SourceCoreUnifiedCompilation.Compiled)
    (root : SourceSpecialization.SpecializationKey) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) : IO (String × String × Bool) := do
  let first ← get "actual generic native startup" (cached.run root arguments 500 fuel)
  let final ← get "actual generic native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution
    | none => throw (IO.userError "actual generic native execution was rejected")
  let native := execution.completion.result.native.observation
  let failed ← match native with
    | .succeeded _ store =>
      require (!store.isEmpty) "actual installed closure store was empty"
      pure false
    | .failed _ store =>
      require (!store.isEmpty) "actual fault discarded the installed closure store"
      pure true
    | _ => throw (IO.userError "actual generic native run did not finish")
  pure (reprStr final.observation, reprStr native, failed)

def run : IO Unit := do
  let program ← get "public generic checked source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let names := ["wordRoot", "boolRoot", "constrained", "recurRoot", "faultRoot"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let seeds := roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration
  let options : SourceCompiler.Options := {specializationBudget := 512, compilationFuel := 1000}
  let facade ← get "actual public specialization compilation" (SourceCompiler.compileChecked program seeds options)
  let source ← get "same actual Core source compiler" (SourceCoreCompiler.compileChecked program seeds options)
  let cached ← match source.artifact? with
    | some cached => pure cached | none => throw (IO.userError "nonempty generic roots lost cache")
  let recipe ← get "actual generic recipe preparation" (SourceCoreIndexedSession.Recipe.prepare cached)
  require (facade.keys == source.keys && recipe.compiled.keys == roots) "actual public root order changed"
  inspect program recipe.compiled
  require (SourceCompiler.compileChecked program seeds {options with specializationBudget := 0}).toOption.isNone
    "zero budget treated a pending candidate as completed"
  for (name, arguments) in ([
      ("wordRoot", []), ("boolRoot", []), ("constrained", [.word (word 17)]),
      ("recurRoot", []), ("faultRoot", [])] : List (String × List SourceTypedRuntime.Value)) do
    let root ← SourceCoreUnifiedCorpusSupport.key program name
    let baseline ← full_native recipe.compiled root arguments 300000
    require (baseline.2.2 == (name == "faultRoot")) "actual generic native outcome changed"
    for fuel in [0, 1, 31, 300000] do
      let actual ← full_native recipe.compiled root arguments fuel
      require (actual == baseline) "actual generic full native store/source heap/fault resume changed"
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let initial ← match boot.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "actual generic bootstrap incomplete")
  for (name, arguments, expected) in [
      ("wordRoot", [], SourceCorePublicValues.Value.word (word 7)),
      ("boolRoot", [], .bool false),
      ("constrained", [.word (word 17)], .word (word 17)),
      ("recurRoot", [], .word (word 13))] do
    let root ← SourceCoreUnifiedCorpusSupport.key program name
    let baseline ← get "actual full generic checkpoint" (initial.start root arguments)
    let baselineResult ← baseline.resume 300000
    let baselineCompletion ← match baselineResult with
      | .succeeded completion => pure completion | _ => throw (IO.userError "actual generic baseline failed")
    let baselineSnapshot ← get "baseline full snapshot" (← baselineCompletion.session.snapshot)
    for fuel in [0, 1, 31, 300000] do
      let checkpoint ← get "actual generic startup" (initial.start root arguments)
      let first ← checkpoint.resume fuel
      let final ← match first with | .outOfFuel checkpoint => checkpoint.resume 300000 | other => pure other
      match final with
      | .succeeded completion =>
        let snapshot ← get "resumed full snapshot" (← completion.session.snapshot)
        require (completion.value == expected && completion.session.installedGlobalsPresent)
          "actual generic value or global prefix changed"
        require (reprStr snapshot.cells == reprStr baselineSnapshot.cells && snapshot.heapSize == baselineSnapshot.heapSize &&
          snapshot.nativeHeapSize == baselineSnapshot.nativeHeapSize)
          "actual generic ordered full heap or resume changed"
      | _ => throw (IO.userError "actual generic completion failed")
  let root ← SourceCoreUnifiedCorpusSupport.key program "faultRoot"
  let baseline ← get "actual generic fault startup" (initial.start root [])
  let baselineResult ← baseline.resume 300000
  let (expectedReason, expectedSession) ← match baselineResult with
    | .failed reason session => pure (reason, session) | _ => throw (IO.userError "actual generic missing fault absent")
  let expectedSnapshot ← get "fault baseline full snapshot" (← expectedSession.snapshot)
  for fuel in [0, 1, 31, 300000] do
    let checkpoint ← get "actual generic fault repeat" (initial.start root [])
    let first ← checkpoint.resume fuel
    let final ← match first with | .outOfFuel checkpoint => checkpoint.resume 300000 | other => pure other
    match final with
    | .failed reason session =>
      let snapshot ← get "fault resumed full snapshot" (← session.snapshot)
      require (reprStr reason == reprStr expectedReason && session.installedGlobalsPresent &&
        reprStr snapshot.cells == reprStr expectedSnapshot.cells &&
        snapshot.nativeHeapSize == expectedSnapshot.nativeHeapSize)
        "actual generic fault payload/full heap/resume changed"
    | _ => throw (IO.userError "actual generic fault was lost")
  IO.println "actual public worklist full carriers / generic source bodies / constrained complete dictionaries / native reverse slots / full heap and fault resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicSpecializationMeaning
