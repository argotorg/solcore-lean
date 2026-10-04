import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Test.SourceCompilerFeatureSupport

/-! Foundation consumers for actual indirect lowering and original Core child
grades. The runtime fixture audits the real prepared contract policy and all
stores. It does not provide source closure history or closed called-body meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndirectCallBounds
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CoreProof CallableIndirectCallCertificates CallableIndirectCallBounds

section Compiler
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Core.Word} {lowered : SourceCoreBasic.LoweredExpr}

abbrev actual_compiler := @CallableIndirectCallCertificates.of_functions
abbrev original_native := @CallableIndirectCallBounds.call_completed
abbrev actual_stage_rejection := @CallableIndirectCallBounds.stage_rejection

theorem actual_ordered_children
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    arguments.length = receipt.codes.length ∧ ∀ child code, (child, code) ∈ receipt.entries →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt = .ok code :=
  receipt.ordered_children

theorem original_and_read_metadata
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered) :
    source.lookupExpression? id = some receipt.original ∧
      receipt.original.form = .call callee arguments (.indirect metadata) ∧
      policy.readExpression source id = .ok (receipt.node, receipt.type) ∧
      receipt.node.form = .call callee arguments (.indirect metadata) ∧
      SourceCompilationPlan.validateIndirectCallMetadata source receipt.node callee arguments metadata = .ok () :=
  ⟨receipt.found, receipt.originalForm, receipt.read, receipt.form, receipt.validated⟩

theorem prepared_rows_and_code
    (receipt : Receipt policy body fuel compilation source scope id callee arguments metadata reasonAt lowered)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active) :
    ∃ site, SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id native.diagnostics.reasonAt = .ok site ∧
      site.table = native.table ∧ site.caller = compilation.owner ∧ site.call = receipt.node.id ∧
      receipt.expression = site.lower native.diagnostics.unknown receipt.resultType receipt.calleeCode.expression (SourceCoreCalls.packArguments receipt.codes).expression :=
  receipt.prepared_site native active actualPolicy

/-- Failure keeps the original effects before any later computation is entered. -/
theorem first_failure {size budget : Nat} {environment : Core.Environment} {before after : Core.Store}
    {input result : Core.Ty} {callee arguments : Core.Expr} {payload : Core.Value}
    {gates : List Core.CallableContract.Gate} {unknown : Core.Word}
    (original : EvaluationSize size environment before callee (.inLeft input payload) after)
    (strict : size < budget) :
    Completion budget gates unknown result callee arguments environment before (.inLeft result payload) after :=
  .calleeFailure original strict
end Compiler

namespace OriginalCompletions
open Solcore Core SourceSemantics.CoreLowering CoreProof

/-- Complete captured suffixes are retained in the actual function payload. -/
def carrier (contract : Word) (body : Expr) (captured : Core.Environment) : Value :=
  .pair (.pair (.inLeft .word .unit) (.closure .unit (.sum .word .unit) body captured)) (.word contract)

def callee : Expr := .inRight .word (.var 0)
def arguments : Expr := .inRight .word .unit

private theorem dispatch_original {environment : Core.Environment} {store : Store}
    {expression : Expr} (gate : CallableContract.Gate) (phase : CallableContract.Phase) (unknown : Word)
    (read : EvaluationSize 2 environment store expression (.word gate.contract) store) :
    EvaluationSize 7 environment store (CallableContract.dispatch [gate] phase unknown expression)
      (CallableContract.resultValue (gate.reason phase)) store := by
  unfold CallableContract.dispatch
  apply EvaluationSize.ifTrue (cost1 := 4) (cost2 := 2)
  · exact .binary read .word (by simp [BinaryOp.apply])
  · cases found : gate.reason phase <;>
      simp only [CallableContract.guardResult, CallableContract.resultValue,
        LanguageResult.success, LanguageResult.failure]
    · exact .inRight .unit
    · exact .inLeft .word

/-- A failed callee skips every guard and the arbitrary argument expression. -/
theorem callee_failure (environment : Core.Environment) (store : Store)
    (gates : List CallableContract.Gate) (unknown reason : Word) (args : Expr) :
    EvaluationSize 5 environment store
      (CallableContract.call gates unknown .unit (.inLeft .unit (.word reason)) args)
      (.inLeft .unit (.word reason)) store ∧
    CallableIndirectCallBounds.Completion 5 gates unknown .unit (.inLeft .unit (.word reason)) args environment store
      (.inLeft .unit (.word reason)) store := by
  have original : EvaluationSize 5 environment store
      (CallableContract.call gates unknown .unit (.inLeft .unit (.word reason)) args)
      (.inLeft .unit (.word reason)) store := by
    simp only [CallableContract.call, LanguageResult.bind]
    exact .caseLeft (.inLeft .word) (.inLeft (.var rfl))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

/-- The first actual guard rejects before the arbitrary argument expression. -/
theorem stage_rejection (environment captured : Core.Environment) (store : Store)
    (contract unknown reason : Word) (body args : Expr) :
    let gates := [CallableContract.Gate.mk contract (some reason) none]
    let env := carrier contract body captured :: environment
    EvaluationSize 13 env store (CallableContract.call gates unknown .unit callee args)
      (.inLeft .unit (.word reason)) store ∧
    CallableIndirectCallBounds.Completion 13 gates unknown .unit callee args env store (.inLeft .unit (.word reason)) store := by
  dsimp only
  have gate := dispatch_original (environment := carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract (some reason) none) .beforeArguments unknown
    (expression := .second (.var 0)) (.second (.var rfl))
  have original : EvaluationSize 13 (carrier contract body captured :: environment) store
      (CallableContract.call [.mk contract (some reason) none] unknown .unit callee args)
      (.inLeft .unit (.word reason)) store := by
    simp only [CallableContract.call, LanguageResult.bind, callee]
    exact .caseRight (.inRight (.var rfl)) (.caseLeft gate (.inLeft (.var rfl)))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

/-- The first guard succeeds; an argument fault skips the second guard and body. -/
theorem argument_failure (environment captured : Core.Environment) (store : Store)
    (contract unknown reason : Word) (body : Expr) :
    let gates := [CallableContract.Gate.mk contract none none]
    let args := Expr.inLeft .unit (.word reason)
    let env := carrier contract body captured :: environment
    EvaluationSize 16 env store (CallableContract.call gates unknown .unit callee args)
      (.inLeft .unit (.word reason)) store ∧
    CallableIndirectCallBounds.Completion 16 gates unknown .unit callee args env store (.inLeft .unit (.word reason)) store := by
  dsimp only
  have gate := dispatch_original (environment := carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract none none) .beforeArguments unknown
    (expression := .second (.var 0)) (.second (.var rfl))
  have original : EvaluationSize 16 (carrier contract body captured :: environment) store
      (CallableContract.call [.mk contract none none] unknown .unit callee (.inLeft .unit (.word reason)))
      (.inLeft .unit (.word reason)) store := by
    simp only [CallableContract.call, LanguageResult.bind, callee, Expr.weakenAt]
    exact .caseRight (.inRight (.var rfl)) (.caseRight gate
      (.caseLeft (.inLeft .word) (.inLeft (.var rfl))))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

/-- The second actual guard rejects after successful callee and argument evaluation. -/
theorem arity_rejection (environment captured : Core.Environment) (store : Store)
    (contract unknown reason : Word) (body : Expr) :
    let gates := [CallableContract.Gate.mk contract none (some reason)]
    let env := carrier contract body captured :: environment
    EvaluationSize 24 env store (CallableContract.call gates unknown .unit callee arguments)
      (.inLeft .unit (.word reason)) store ∧
    CallableIndirectCallBounds.Completion 24 gates unknown .unit callee arguments env store (.inLeft .unit (.word reason)) store := by
  dsimp only
  have gate := dispatch_original (environment := carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract none (some reason)) .beforeArguments unknown
    (expression := .second (.var 0)) (.second (.var rfl))
  have arity := dispatch_original (environment := .unit :: .unit :: carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract none (some reason)) .beforeApplication unknown
    (expression := .second (.var 2)) (.second (.var rfl))
  have original : EvaluationSize 24 (carrier contract body captured :: environment) store
      (CallableContract.call [.mk contract none (some reason)] unknown .unit callee arguments)
      (.inLeft .unit (.word reason)) store := by
    simp only [CallableContract.call, LanguageResult.bind, callee, arguments, Expr.weakenAt]
    exact .caseRight (.inRight (.var rfl)) (.caseRight gate (.caseRight (.inRight .unit)
      (.caseLeft arity (.inLeft (.var rfl)))))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

/-- Application enters the original closure with its complete captured suffix. -/
theorem application_success (environment captured : Core.Environment) (store : Store)
    (contract unknown : Word) :
    let gates := [CallableContract.Gate.mk contract none none]
    let body := Expr.inRight .word .unit
    let env := carrier contract body captured :: environment
    EvaluationSize 29 env store (CallableContract.call gates unknown .unit callee arguments)
      (.inRight .word .unit) store ∧
    CallableIndirectCallBounds.Completion 29 gates unknown .unit callee arguments env store (.inRight .word .unit) store := by
  dsimp only
  have gate := dispatch_original (environment := carrier contract (.inRight .word .unit) captured :: carrier contract (.inRight .word .unit) captured :: environment)
    (store := store) (.mk contract none none) .beforeArguments unknown
    (expression := .second (.var 0)) (.second (.var rfl))
  have arity := dispatch_original (environment := .unit :: .unit :: carrier contract (.inRight .word .unit) captured :: carrier contract (.inRight .word .unit) captured :: environment)
    (store := store) (.mk contract none none) .beforeApplication unknown
    (expression := .second (.var 2)) (.second (.var rfl))
  have original : EvaluationSize 29 (carrier contract (.inRight .word .unit) captured :: environment) store
      (CallableContract.call [.mk contract none none] unknown .unit callee arguments) (.inRight .word .unit) store := by
    simp only [CallableContract.call, LanguageResult.bind, callee, arguments, Expr.weakenAt]
    exact .caseRight (.inRight (.var rfl)) (.caseRight gate (.caseRight (.inRight .unit)
      (.caseRight arity (.apply (.second (.first (.var rfl))) (.var rfl) (.inRight .unit)))))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

/-- A body fault retains its real allocation and every cell in the original store. -/
theorem body_fault_after_allocation (environment captured : Core.Environment) (store : Store)
    (contract unknown reason : Word) :
    let gates := [CallableContract.Gate.mk contract none none]
    let body := Expr.letE (.newCell .unit .unit) (.inLeft .unit (.word reason))
    let env := carrier contract body captured :: environment
    EvaluationSize 32 env store (CallableContract.call gates unknown .unit callee arguments)
      (.inLeft .unit (.word reason)) (store ++ [.unit]) ∧
    CallableIndirectCallBounds.Completion 32 gates unknown .unit callee arguments env store
      (.inLeft .unit (.word reason)) (store ++ [.unit]) := by
  dsimp only
  let body := Expr.letE (.newCell .unit .unit) (.inLeft .unit (.word reason))
  have gate := dispatch_original (environment := carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract none none) .beforeArguments unknown
    (expression := .second (.var 0)) (.second (.var rfl))
  have arity := dispatch_original (environment := .unit :: .unit :: carrier contract body captured :: carrier contract body captured :: environment)
    (store := store) (.mk contract none none) .beforeApplication unknown
    (expression := .second (.var 2)) (.second (.var rfl))
  have original : EvaluationSize 32 (carrier contract body captured :: environment) store
      (CallableContract.call [.mk contract none none] unknown .unit callee arguments)
      (.inLeft .unit (.word reason)) (store ++ [.unit]) := by
    simp only [CallableContract.call, LanguageResult.bind, callee, arguments, Expr.weakenAt]
    exact .caseRight (.inRight (.var rfl)) (.caseRight gate (.caseRight (.inRight .unit)
      (.caseRight arity (.apply (.second (.first (.var rfl))) (.var rfl)
        (.letE (.newCell .unit) (.inLeft .word))))))
  exact ⟨original, CallableIndirectCallBounds.call_completed original (Nat.le_refl _)⟩

end OriginalCompletions


private def word := Core.Word.ofNatModulo
private def require := SourceCompilerFeatureSupport.require
private def get {α ε : Type} [Repr ε] := @SourceCompilerFeatureSupport.get α ε _

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function before() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function after() returns (comptime<Word>) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f(1, 2); }",
    "function accepted() returns (Word) { let f = lam(value: (Word, Word)) -> Word { return 7; }; return f((1, 2)); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError s!"indirect root missing {name}")
  pure ⟨signature.id, []⟩

private def complete (code : Core.Expr) (environment : Core.Environment) (before : Core.Store) : IO Core.StatefulRunResult := do
  let expected := Core.runStateful 300000 (.initial code environment before)
  for fuel in [0, 1, 19, 300000] do
    let actual := match Core.runStateful fuel (.initial code environment before) with
      | .outOfFuel checkpoint => Core.runStateful 300000 checkpoint
      | done => done
    require (actual == expected) s!"indirect exact whole store/resume {fuel}"
  pure expected

private def inspect : IO Unit := do
  let program ← get "indirect checked program" (checkProgram workspace)
  let keys ← ["before", "after", "accepted"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun k => ⟨k.declaration, []⟩)) 64 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"indirect worklist {reprStr other}")
  let automatic ← get "indirect actual compatible" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "indirect actual indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let representation := SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts
  let native := prepared.ancestry.graph.inputs.callable
  let policy := {representation.expressions with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
  let mut seen := 0
  for (name, root) in ["before", "after", "accepted"].zip keys do
    let caller ← get "indirect retained source" (SourceCompilationPlan.exactSpecialization prepared.base.plan root)
    let source := caller.function.typedBody
    let compilation : SourceCoreFunctions.Context := ⟨prepared.base.plan, root, prepared.base.globals, 1, caller.function.solvedRequirements, Core.Word.zero⟩
    let mut scope : SourceCoreBasic.Scope := []
    for raw in source.nodes do
      match raw with
      | .statement node => match node.form with
        | .letDecl binder _ =>
          let type ← get "indirect actual binder projection" (policy.projectType (.occurrence node.id.occurrence) binder.scheme.body)
          scope := (binder.id, type) :: scope
        | _ => pure ()
      | _ => pure ()
    for raw in source.nodes do
      match raw with
      | .expression node => match node.form with
        | .call callee arguments (.indirect metadata) =>
          let (readNode, type) ← get "indirect actual parent read" (policy.readExpression source node.id)
          require (readNode == node && metadata.argumentCoercions.isEmpty) "indirect original metadata"
          let body : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ =>
            .error (.traversalExhausted (.occurrence node.id.occurrence))
          let lower := SourceCoreFunctions.lowerExpressionWithPolicy policy body
          let calleeCode ← get "indirect original callee child" (lower 499 compilation source scope callee (fun _ => Core.Word.zero))
          let codes ← get "indirect ordered child vector" (arguments.mapM fun id => lower 499 compilation source scope id (fun _ => Core.Word.zero))
          let output ← get "indirect actual parent compiler" (lower 500 compilation source scope node.id (fun _ => Core.Word.zero))
          let site ← get "indirect actual prepared callsite" (SourceCoreCallableContracts.prepareCallsite native.table root node.id native.diagnostics.reasonAt)
          require (output.type == type && output.expression == site.lower native.diagnostics.unknown type calleeCode.expression (SourceCoreCalls.packArguments codes).expression)
            "indirect exact emitted call/ordered vector/same fuel"
          require (codes.length == arguments.length && site.rows.map (fun row => row.entry.id) == (native.table.casesAt root node.id).map (fun row => row.entry.id)) "indirect ordered retained table IDs"
          -- Retained IR may repeat a child ID. This static compiler check keeps
          -- the untouched node ledger; it does not claim a parser-produced forest.
          if name == "before" then
            let first ← match arguments with
              | first :: _ => pure first | [] => throw (IO.userError "indirect repeated child missing")
            let repeated := [first, first]
            let retained : TypedSource := { source with nodes := source.nodes.map fun raw =>
              match raw with
              | .expression original => if original.id == node.id then
                  .expression { original with form := .call callee repeated (.indirect metadata) }
                else raw
              | _ => raw }
            require (retained.owner == source.owner && retained.inputs == source.inputs &&
              retained.roots == source.roots && retained.nodes.length == source.nodes.length &&
              retained.nodes.filter (fun raw => raw.id != .expression node.id) ==
                source.nodes.filter (fun raw => raw.id != .expression node.id))
              "indirect repeated IR retains full unused ledger"
            let repeatedCallee ← get "indirect repeated callee" (lower 499 compilation retained scope callee (fun _ => Core.Word.zero))
            let repeatedCodes ← get "indirect repeated ordered children" (repeated.mapM fun child => lower 499 compilation retained scope child (fun _ => Core.Word.zero))
            let repeatedOutput ← get "indirect repeated parent accepted" (lower 500 compilation retained scope node.id (fun _ => Core.Word.zero))
            require (repeatedCodes.length == 2 && repeatedCodes[0]? == repeatedCodes[1]? &&
              repeatedOutput.expression == site.lower native.diagnostics.unknown type repeatedCallee.expression
                (SourceCoreCalls.packArguments repeatedCodes).expression)
              "indirect same-fuel ordered duplicate children"
          let entry ← match site.rows.find? (fun row => match row.entry.origin with | .lambda owner _ [] => decide (owner = root) | _ => false) with
            | some row => pure row.entry | none => throw (IO.userError "indirect actual lambda descriptor")
          let calleeExpression : Core.Expr :=
            .letE (.storeCell (.var 0) (.word (word 11)))
              (Core.LanguageResult.success (Core.CallableContract.wrap entry.id
                (Core.TaggedFunction.anonymous (.lambda (.product .word .word) (Core.LanguageResult.resultType .word)
                  (.letE (.storeCell (.var 2) (.word (word 33))) (Core.LanguageResult.success (.word (word 7))))))))
          let argumentsExpression : Core.Expr :=
            .letE (.storeCell (.var 0) (.word (word 22)))
              (Core.LanguageResult.success (.pair (.word (word 1)) (.word (word 2))))
          let unused : Core.Value := .closure .unit .unit (.var 0) [.bool true, .unit]
          let before : Core.Store := [.word (word 0), .bool false, unused]
          let actualCall := site.lower native.diagnostics.unknown .word calleeExpression argumentsExpression
          let actualProgram : Core.Program := ⟨Core.LanguageResult.resultType .word, actualCall, []⟩
          require (actualProgram.checkIn [.cell .word]) "indirect actual harness native typing"
          let result ← complete actualCall [.cellRef .word 0] before
          let row ← match site.rowAt? entry.id with
            | some row => pure row | none => throw (IO.userError "indirect selected row")
          -- One lambda parameter receives two separate arguments in before/after.
          -- The ordinary caller checks stage arity first; the comptime caller
          -- skips that stage check and reaches full arity after both arguments.
          -- accepted supplies one tuple argument, so both guards must succeed.
          let effectfulStaging := caller.function.returnComptime ||
            SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType
          require (row.entry.parameterCount == 1) "indirect actual lambda parameter count"
          match name with
          | "before" =>
            require (!effectfulStaging && arguments.length == 2) "indirect ordinary caller metadata"
            require (match row.beforeArguments, row.afterArguments with
              | .error (.argumentArityMismatch 0 1), .error (.argumentArityMismatch 1 2) => true
              | _, _ => false) "indirect first stage-guard branch required"
          | "after" =>
            require (effectfulStaging && arguments.length == 2) "indirect comptime caller metadata"
            require (match row.beforeArguments, row.afterArguments with
              | .ok (), .error (.argumentArityMismatch 1 2) => true
              | _, _ => false) "indirect second arity-guard branch required"
          | "accepted" =>
            require (!effectfulStaging && arguments.length == 1) "indirect tuple caller metadata"
            require (match row.beforeArguments, row.afterArguments with
              | .ok (), .ok () => true | _, _ => false) "indirect accepted-body branch required"
          | _ => throw (IO.userError "unexpected indirect fixture")
          let expected ← match row.beforeArguments with
            | .error error => pure (.inLeft .word (.word (site.reasonAt row.caller row.call row.entry.id .beforeArguments error)), [.word (word 11), .bool false, unused])
            | .ok () => match row.afterArguments with
              | .error error => pure (.inLeft .word (.word (site.reasonAt row.caller row.call row.entry.id .beforeApplication error)), [.word (word 22), .bool false, unused])
              | .ok () => pure (.inRight .word (.word (word 7)), [.word (word 33), .bool false, unused])
          require (result == .done expected.1 expected.2) s!"indirect actual callee/guard/args/body order {name}"
          seen := seen + 1
        | _ => pure ()
      | _ => pure ()
  require (seen == 3) "indirect actual source compiler coverage"

def run : IO Unit := do
  inspect
  IO.println "indirect call foundations: actual compiler/table, original guard order, full stores and four-fuel resume GREEN"
end Tests.SourceCoreCallableIndirectCallBounds
