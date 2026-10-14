import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedInitialForward
import Solcore.Test.SourceCoreUnifiedCorpusSupport

set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedPrimitiveFixture
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

def wordOperators : List (String × String) := [
  ("mul", "*"), ("divide", "/"), ("modulo", "%"), ("add", "+"), ("sub", "-"),
  ("band", "&"), ("bxor", "^"), ("bor", "|")]
def comparisons : List (String × String) := [
  ("gt", ">"), ("eq", "==")]

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" (
    (wordOperators.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Word)" ++ " { return left " ++ operator ++ " right; }") ++
    (comparisons.map fun (name, operator) =>
      s!"function {name}(left: Word, right: Word) returns (Bool)" ++ " { return left " ++ operator ++ " right; }") ++ [
    "function conjunction(left: Bool, right: Bool) returns (Bool) { return left && right; }",
    "function disjunction(left: Bool, right: Bool) returns (Bool) { return left || right; }",
    "function negation(input: Bool) returns (Bool) { return !input; }",
    "function complement(input: Word) returns (Word) { return ~input; }",
    "function literal() returns (Word) { return 17; }",
    "function hugeLiteral() returns (Word) { return " ++ toString (Core.wordModulus + 5) ++ "; }",
    "function nested(flag: Bool, value: Word) returns (Word, Bool) {",
    "  return ((flag ? value + 2 : value * 3), (!flag || (value > 0)));",
    "}",
    "function builtin() returns (Word) { return wordFromInteger(1); }",
    "function lt(left: Word, right: Word) returns (Bool) { return right > left; }",
    "function lessCall(left: Word, right: Word) returns (Bool) { return left < right; }"
  ]) }]
}

def options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 1000, specializationBudget := 512}
def runOptions : SourceCoreExecution.RunOptions := {inputValidationFuel := 1000, executionFuel := 100000}

def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

/-- Only original checking, compilation and preparation receipts are retained. -/
structure Fixture where
  program : CheckedProgram
  checked : checkProgram workspace options.checkingFuel = .ok program
  seeds : List SourceCompiler.Seed
  facade : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facade
  recipe : SourceCoreIndexedSession.Recipe
  issued : RecursiveNamedPreparedStageContracts.PublicRecipe facade recipe
  sameProgram : recipe.compiled.sourceProgram = program

def fixture (names : List String) : IO Fixture := do
  match checked : checkProgram workspace options.checkingFuel with
  | .error errors => throw (IO.userError (reprStr errors))
  | .ok program =>
    let keys ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
    let seeds := keys.map (fun key => SourceCompiler.Seed.declaration key.declaration)
    match generated : SourceCoreCompiler.compileChecked program seeds options with
    | .error error => throw (IO.userError (reprStr error))
    | .ok source =>
      match selected : source.artifact? with
      | none => throw (IO.userError "primitive artifact missing")
      | some cached =>
        match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
        | .error error => throw (IO.userError (reprStr error))
        | .ok recipe =>
          match facade : SourceCoreExecution.prepare source with
          | .error error => throw (IO.userError (reprStr error))
          | .ok result =>
            have accepted : SourceCompiler.compileChecked program seeds options = .ok result := by
              simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError, bind, Except.bind] using facade
            return ⟨program, checked, seeds, result, accepted, recipe,
              RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade,
              (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
                ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))⟩

structure Row (fixture : Fixture) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  parameters : row.parameterSubstitution = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder ∈ row.function.typedBody.inputs, binder.comptime = false
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

def row (fixture : Fixture) (name : String) : IO (Row fixture) := do
  let key ← SourceCoreUnifiedCorpusSupport.key fixture.program name
  match found : fixture.recipe.compiled.validationPlan.specializations.find? (fun row => decide (row.key = key)) with
  | none => throw (IO.userError "primitive row missing")
  | some row =>
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "primitive substitution changed"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "primitive return changed"
    let ⟨inputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "primitive input changed"
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨keyEq⟩ ← observed (global.key = row.key) "primitive physical key changed"
      return ⟨row, List.mem_of_find?_eq_some found, parameters, ordinary,
        by intro binder member; have h := List.all_eq_true.mp inputs binder member; cases h' : binder.comptime <;> simp_all,
        global, index, by unfold CallableNamedMetadata.Slot; rw [keyEq]; exact slot, keyEq⟩
    | _ => throw (IO.userError "primitive slot is not unique")

theorem Row.eligible {fixture : Fixture} (row : Row fixture) :
    ∃ selected : CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row ∧ selected.named.signature = row.global := by
  obtain ⟨prepared⟩ := RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued row.member
  have cached := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈ fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = row.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr cached, ?_⟩
    simp only [row.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared, decide_true]
  rw [row.slot] at member
  obtain ⟨signatureEq, indexEq⟩ := Prod.mk.inj (List.mem_singleton.mp member)
  have eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled prepared.named.specialized := by
    rw [prepared.same]
    refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
    simp only [row.parameters, ParameterSubstitution.RangeWellFormed, List.not_mem_nil, false_implies, implies_true]
  exact ⟨⟨prepared.named, prepared.index, row.global, prepared.selected,
    by rw [indexEq]; exact row.slot, row.globalKey, eligible⟩, prepared.same, signatureEq⟩

structure Started (fixture : Fixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facade
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.StartedCall session key arguments runOptions

def start (fixture : Fixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facade.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "primitive bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint => return ⟨opened.val, opened.property, fresh.val, fresh.property.1,
        fresh.property.2, session, ready, checkpoint, started⟩

theorem initial {fixture : Fixture}
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (row : Row fixture) {arguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.row.key arguments) :
    ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled fixture.recipe,
      ∃ first : SelectedCompilationCertifiedPublicSession.Initial issued.toIssued started.call,
        first.header.named.specialized = row.row ∧ first.header.named.signature = row.global := by
  obtain ⟨selected, sameRow, sameSignature⟩ := row.eligible
  obtain ⟨issued, first, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile started.opened started.call started.bootstrap started.fresh started.authority
    (show started.bootstrap.ReadyAt 100000 started.session from .single started.ready) selected
  exact ⟨issued, first, (congrArg (·.specialized) namedEq).trans sameRow,
    (congrArg (·.signature) namedEq).trans sameSignature⟩

end Tests.SourceCoreSelectedPrimitiveFixture
