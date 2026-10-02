import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation
import Solcore.Test.SourceCompilerFeatureSupport

/-! Actual helper acceptance supplies ordered static receipts. Native tests
observe saved captures, early failure, duplicate calls and hidden caller slots.
The public source fixture exercises coercion effects and failure/resumption;
source method selection/body correspondence remains a separate obligation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableCoercionSpine
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableCoercionSpine

/-- One real helper action supplies every selector, dictionary and code receipt,
and completed native execution supplies every actual saved-body trace. -/
theorem accepted_completed {program : CheckedProgram} {project : Projector} {context : CallableCoercionSpine.Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy} {input output : Lowered} {steps : List CoercionStep}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy input steps = .ok output)
    (ξ : Renaming) {environment : Environment} {before after : Store} {value : Value} :
    ∃ calls, Spine program project context caller available scope node policy input steps output calls ∧
      calls.length = steps.length ∧
      (Evaluates environment before (output.expression.rename ξ) value after ↔
        ∃ initial middle, Evaluates environment before (input.expression.rename ξ) initial middle ∧
          Runs environment context.internalReason middle initial (calls.map (Call.rename ξ)) value after) := by
  obtain ⟨calls, receipt⟩ := of_accepted accepted
  exact ⟨calls, receipt, receipt.length, receipt.renamed_completed_iff ξ⟩

theorem accepted_initial_failure {program : CheckedProgram} {project : Projector} {context : CallableCoercionSpine.Context}
    {caller : Specialized} {available : RuntimeEvidence} {scope : Scope} {node : ExpressionNode}
    {policy : SourceCoreFunctions.CallablePolicy} {input output : Lowered} {steps : List CoercionStep}
    (accepted : SourceCoreEvidence.applyCoercions program project context caller available scope node policy input steps = .ok output)
    {environment : Environment} {before reached after : Store} {reason : Word} {value : Value}
    (failed : Evaluates environment before input.expression (.inLeft input.type (.word reason)) reached)
    (completed : Evaluates environment before output.expression value after) :
    value = .inLeft output.type (.word reason) ∧ after = reached := by
  obtain ⟨_, receipt⟩ := of_accepted accepted
  exact evaluation_deterministic completed (receipt.input_failure failed)

private def writingBody (reason : Word) : Expr :=
  .letE (.storeCell (.var 1) (.word (Word.ofNatModulo 7))) (.inLeft .word (.word reason))
private def capturedClosure (reason : Word) : Value :=
  .closure .unit (LanguageResult.resultType .word) (writingBody reason) [.cellRef .word 0]
private def initialStore (reason : Word) : Store := [.word Word.zero, .inRight .unit (capturedClosure reason)]
private def finalStore (reason : Word) : Store := [.word (Word.ofNatModulo 7), .inRight .unit (capturedClosure reason)]
private def cellType : Ty := OptionalCell.cellType (.function .unit (LanguageResult.resultType .word))
private def firstCall (key : Key) (index : Nat) : Call := ⟨⟨key, .unit, .word⟩, index⟩
private def lastCall (key : Key) : Call := ⟨⟨key, .word, .bool⟩, 400⟩

/-- The first actual saved body writes through its captured cell and fails.
The nonexistent second global is never read; the returned store retains exactly
that first write and the same saved capture. -/
theorem captured_failure_skips_suffix (key : Key) (reason : Word)
    {environment : Environment} {index : Nat}
    (reference : environment[index]? = some (.cellRef cellType 1)) :
    Evaluates environment (initialStore reason)
      (emit Word.zero (LanguageResult.success .unit) [firstCall key index, lastCall key])
      (.inLeft .bool (.word reason)) (finalStore reason) := by
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (.applied reference rfl ?_) (.cons (Invoke.skipped (tag := .word)) .nil)⟩
  exact .letE (.storeCell (.var rfl) rfl .word (by simp [initialStore, finalStore, Store.write?])) (.inLeft .word)

/-- Moving the caller slot past two temporaries leaves the saved body and
capture unchanged; this is evaluation of the real renamed helper syntax. -/
theorem hidden_slots_same_capture (key : Key) (reason : Word) :
    Evaluates [.integer 3, .bool false, .cellRef cellType 1] (initialStore reason)
      ((emit Word.zero (LanguageResult.success .unit) [firstCall key 0, lastCall key]).rename (fun index => index + 2))
      (.inLeft .bool (.word reason)) (finalStore reason) := by
  rw [emit_rename]
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (.applied rfl rfl ?_) (.cons (Invoke.skipped (tag := .word)) .nil)⟩
  exact .letE (.storeCell (.var rfl) rfl .word (by simp [initialStore, finalStore, Store.write?])) (.inLeft .word)

/-- Two identical selected slots are still two calls. Their saved bodies both
allocate, so the native trace records two distinct heap extensions. -/
theorem duplicate_call_order (key : Key) :
    let signature : SourceCoreCalls.Signature := ⟨key, .unit, .unit⟩
    let body : Expr := .letE (.newCell .word (.word Word.zero)) (LanguageResult.success .unit)
    let closure : Value := .closure .unit (LanguageResult.resultType .unit) body []
    Evaluates [.cellRef (OptionalCell.cellType signature.functionType) 0] [.inRight .unit closure]
      (emit Word.zero (LanguageResult.success .unit) [⟨signature, 0⟩, ⟨signature, 0⟩])
      (.inRight .word .unit) [.inRight .unit closure, .word Word.zero, .word Word.zero] := by
  dsimp only
  apply emit_evaluates_iff.mpr
  refine ⟨_, _, .inRight .unit, .cons (middle := [.inRight .unit (.closure .unit (LanguageResult.resultType .unit) (.letE (.newCell .word (.word Word.zero)) (LanguageResult.success .unit)) []), .word Word.zero]) (result := .inRight .word .unit) (.applied rfl rfl ?_) (.cons (.applied rfl rfl ?_) .nil)⟩
  · exact .letE (.newCell .word) (.inRight .unit)
  · exact .letE (.newCell .word) (.inRight .unit)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, Word> { function coerce(value: Bool) returns (Word) { let table: mapping(Word => Word); table[0] = 7; if (value) { table[0] += 2; return table[0]; } let absent: Word; return absent; } }",
    "function converted(flag: Bool) returns (Word) { return flag; }",
    "function failed() returns (Word) { let result: Word = false; let skipped: mapping(Word => Word); skipped[8] = 90; return result; }",
    "function captured() returns (function() returns (Word)) { let result: Word = true; return lam() { return result; }; }"
  ]}] }

/-- Re-enter the actual compiler helper on reached checked coercion lists. Its
input is a literal of the actual raw projected type; method selection and the
ordered runtime dictionaries still come from the sealed prepared plan. -/
private def audit (entry : SourceCompilerFeatureSupport.Entry) : IO Nat := do
  let base := entry.cached.indexed.base
  let mut reached := 0
  for named in base.functions do
    let context : SourceCoreFunctions.Context := {
      plan := base.plan, owner := named.signature.key, globals := base.globals,
      administrativePrefix := 1, solvedRequirements := named.specialized.function.solvedRequirements,
      internalReason := Word.zero }
    let available ← SourceCompilerFeatureSupport.get "coercion caller evidence"
      (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment base.sourceProgram named.signature.key named.specialized.assumptions)
    for item in named.specialized.function.typedBody.nodes do
      match item with
      | .expression node =>
        if !node.coercions.isEmpty then
          let inputType ← SourceCompilerFeatureSupport.get "coercion raw input projection"
            (SourceCoreFunctionTypes.projectType (.occurrence node.id.occurrence) node.rawType)
          let input : Expr ← match inputType with
            | .bool => pure (.bool true)
            | .word => pure (.word Word.zero)
            | .integer => pure (.integer 0)
            | _ => throw (IO.userError "unexpected coercion fixture raw type")
          let lowered ← SourceCompilerFeatureSupport.get "actual ordered coercion helper"
            (SourceCoreEvidence.applyCoercions base.sourceProgram SourceCoreFunctionTypes.projectType context named.specialized available
              [] node {} ⟨inputType, LanguageResult.success input⟩ node.coercions)
          let outputType ← SourceCompilerFeatureSupport.get "coercion final projection"
            (SourceCoreFunctionTypes.projectType (.occurrence node.id.occurrence) node.type)
          let nativeContext := .unit :: base.globals.map SourceCoreCalls.Signature.referenceType
          SourceCompilerFeatureSupport.require (lowered.type == outputType &&
            Core.infer? nativeContext lowered.expression entry.cached.indexed.layouts.definitions == some (LanguageResult.resultType outputType))
              "coercion helper lost exact input/output or ordered global slots"
          reached := reached + 1
      | _ => pure ()
  pure reached

private def faultResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let baseline ← entry.invoke []
  let (reason, session) ← match baseline.outcome with
    | .failed reason session => pure (reason, session)
    | _ => throw (IO.userError "coercion body failure disappeared")
  let snapshot ← SourceCompilerFeatureSupport.get "coercion fault snapshot" (← session.snapshot 2048)
  entry.checkCells [] [
    (.bool, some (.bool false)),
    (.mapping .word .word, some (.mapping .word .word
      [(SourceCompilerFeatureSupport.scalar 0, SourceCompilerFeatureSupport.scalar 7)])),
    (.word, none)]
  for spent in [0, 13, 67] do
    let started ← SourceCompilerFeatureSupport.get "coercion fault suspend"
      (← baseline.initial.run baseline.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := spent})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed with
    | .failed actual session =>
      let observed ← SourceCompilerFeatureSupport.get "coercion fault resumed snapshot" (← session.snapshot 2048)
      SourceCompilerFeatureSupport.require (actual == reason && reprStr observed.cells == reprStr snapshot.cells)
        "coercion failed store or reason changed on resume"
    | _ => throw (IO.userError "coercion failure resume changed outcome")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "coercion spine checker" (checkProgram workspace)
  let converted ← SourceCompilerFeatureSupport.compileNamed program "converted"
  SourceCompilerFeatureSupport.require ((← audit converted) > 0) "actual coercion helper not reached"
  converted.checkResume [.bool true] (SourceCompilerFeatureSupport.scalar 9) 11
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  SourceCompilerFeatureSupport.require ((← audit failed) > 0) "failed coercion helper not reached"
  faultResume failed
  let captured ← SourceCompilerFeatureSupport.compileNamed program "captured"
  let created ← captured.invoke []
  let completed ← match created.outcome with
    | .succeeded completion => pure completion
    | _ => throw (IO.userError "coercion/capture fixture failed")
  let handle ← match completed.value with
    | .function handle => pure handle
    | _ => throw (IO.userError "coercion capture handle missing")
  let invoked ← SourceCompilerFeatureSupport.get "captured coercion result"
    (← completed.session.invokePacked handle .unit SourceCompilerFeatureSupport.executionOptions)
  match invoked with
  | .succeeded completion =>
    SourceCompilerFeatureSupport.require (completion.value == SourceCompilerFeatureSupport.scalar 9)
      "captured coerced cell changed"
  | _ => throw (IO.userError "captured coerced cell invocation failed")
  IO.println "coercion spine: actual helper, ordered calls, failure store, captures and resume GREEN"

end Tests.SourceCoreCallableCoercionSpine
