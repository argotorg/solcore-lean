import Solcore.Frontend.SourceCoreCallableContracts
import Solcore.Core.FuelResumptionProperties

#check_failure Solcore.Frontend.SourceCoreCallableContracts.Descriptor.mk
#check_failure Solcore.Frontend.SourceCoreCallableContracts.Callsite.mk
#check_failure fun (site : Solcore.Frontend.SourceCoreCallableContracts.Callsite) => { site with call := site.call }

set_option autoImplicit false

namespace Tests.SourceCoreCallableContracts

open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableContracts

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function before() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function after() returns (comptime<Word>) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function accepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }"
  ]}] }

private def prepare (program : CheckedProgram) (name : String) : IO (SourceCoreStageCodebook.Table × Key) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError "callable adapter root missing")
  let key : Key := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 16 with
    | .ok (.complete plan) => match SourceCompilationPlan.prepareExecutablePlanEvidence program plan with
      | .ok plan => pure plan
      | .error error => throw (IO.userError s!"callable adapter plan failed {reprStr error}")
    | other => throw (IO.userError s!"callable adapter discovery failed {reprStr other}")
  let types := [.word, TypeSystem.Ty.product .word .word, .function (.product .word .word) .word]
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 64 types with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"callable adapter catalog failed {reprStr error}")
  match SourceCoreStageCodebook.prepare program plan checked with
  | .ok table => pure (table, key)
  | .error error => throw (IO.userError s!"callable adapter codebook failed {reprStr error}")

private def reasonAt : ReasonAt := fun _ _ _ phase _ =>
  match phase with | .beforeArguments => word 71 | .beforeApplication => word 73

private def raw : Core.Expr :=
  Core.TaggedFunction.anonymous (.lambda (.product .word .word) (Core.LanguageResult.resultType .word)
    (.letE (.storeCell (.var 1) (.word (word 777))) (Core.LanguageResult.success (.word (word 7)))))

private def argument : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 22)))
    (Core.LanguageResult.success (.pair (.word (word 1)) (.word (word 2))))

private def native (site : Callsite) (id : Core.Word) (calleeFailure : Bool) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (.newCell .word (.word (word 0)))
    (site.lower (word 74) .word
      (.letE (.storeCell (.var 0) (.word (word 11)))
        (if calleeFailure then Core.LanguageResult.failure
          (Core.CallableContract.functionType (.product .word .word) .word) (.word (word 72))
         else Core.LanguageResult.success (Core.CallableContract.wrap id (raw.weakenAt 0))))
      argument)
}

private def testNative (site : Callsite) (id : Core.Word) (reason : Option Nat) (trace : Nat) : IO Unit := do
  for failure in [false, true] do
    let program := native site id failure
    assertTrue program.check "callable adapter native fixture failed checking"
    let result := if failure then Core.Value.inLeft .word (.word (word 72)) else
      match reason with | none => .inRight .word (.word (word 7)) | some reason => .inLeft .word (.word (word reason))
    let store := [Core.Value.word (word (if failure then 11 else trace))]
    assertTrue (program.runStateful 200 == .done result store)
      "callable adapter changed callee/stage/argument/arity/body order"
    match program.runStateful 12 with
    | .outOfFuel checkpoint =>
        assertTrue (Core.runStateful 188 checkpoint == .done result store)
          "callable adapter checkpoint changed guards or store"
    | _ => throw (IO.userError "callable adapter must suspend at fuel twelve")

example (site : Callsite) (phase : Phase) (unknown id : Core.Word) (row : Decision)
    (found : site.rowAt? id = some row) :
    Core.CallableContract.decision site.gates phase unknown id = reason row site.reasonAt phase :=
  site.decision_known phase unknown id row found

example (site : Callsite) (phase : Phase) (unknown id : Core.Word) (missing : site.rowAt? id = none) :
    Core.CallableContract.decision site.gates phase unknown id = some unknown :=
  site.decision_unknown phase unknown id missing

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"callable adapter source failed {reprStr error}")
  for (name, expectedReason, trace) in [("before", some 71, 11), ("after", some 73, 22), ("accepted", none, 777)] do
    let (table, key) ← prepare program name
    let entry ← match table.entries.filter (fun entry => match entry.origin with
      | .lambda owner _ [] => decide (owner = key) | _ => false) with
      | [entry] => pure entry | _ => throw (IO.userError "callable adapter lambda origin missing")
    let row ← match table.decisions.filter (fun row => decide (row.caller = key) && row.entry.id == entry.id) with
      | [row] => pure row | _ => throw (IO.userError "callable adapter callsite missing")
    let descriptor ← match SourceCoreCallableContracts.descriptor table entry.origin with
      | .ok descriptor => pure descriptor
      | .error error => throw (IO.userError s!"callable descriptor rejected {reprStr error}")
    assertTrue (descriptor.id == entry.id) "callable descriptor mismatched its sealed origin"
    let site ← match prepareCallsite table key row.call reasonAt with
      | .ok site => pure site | .error error => throw (IO.userError s!"callable callsite rejected {reprStr error}")
    testNative site descriptor.id expectedReason trace
    testNative site Core.Word.zero (some 74) 11
    for row in site.rows do
      for phase in [Core.CallableContract.Phase.beforeArguments, .beforeApplication] do
        assertTrue (Core.CallableContract.decision site.gates phase (word 74) row.entry.id ==
          reason row reasonAt phase) "callable gate altered the retained exact decision"
    let missing : Origin := .named ⟨key.declaration, [.bool]⟩
    assertTrue (match SourceCoreCallableContracts.descriptor table missing with
      | .error (.missingOrigin _) => true | _ => false) "unregistered origin acquired a descriptor"
    let absent := {row.call with occurrence := {row.call.occurrence with index := row.call.occurrence.index + 100000}}
    assertTrue (match prepareCallsite table key absent reasonAt with
      | .error (.missingCallsite _ _) => true | _ => false) "unregistered callsite acquired gates"

end Tests.SourceCoreCallableContracts
