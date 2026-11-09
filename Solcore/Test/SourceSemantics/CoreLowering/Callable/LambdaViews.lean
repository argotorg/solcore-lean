import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionMethods
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.Frontend.ProgramChecking

/-!
# Lambda view tests

Lambda views, indirect calls and method bodies.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndirectCallBounds
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndirectCallSourceBounds
/-! Original source call constructors are consumed by the new inversions.
The stage boundary tests below use an independent boundary grade. This unit
has no runtime runner or closed callable body meaning. -/

set_option autoImplicit false
namespace Tests.SourceCoreCallableIndirectCallSourceBounds
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open RecursiveNamedCallBounds CallableIndirectCallSourceBounds

section OriginalIndirect
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {call callee : ExpressionId} {arguments : List ExpressionId} {node : ExpressionNode}
  {metadata : IndirectCallResolution}

theorem original_callee_missing
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (missing : Dynamic.ExpressionMissing source callee) :
    IndirectTraceAt program 3 context evidence source environment before callee arguments metadata node.requirements
      (.fault (.missingExpression callee)) before := by
  have raw : SourceExecutionSize.ExpressionFormFaults program 2 context evidence source environment before
      node.form node.requirements node.coercions (.missingExpression callee) before := by
    rw [form]
    exact .indirectCallee (.missing missing)
  exact indirect_inv_sized found form coercions unique (.fault (.form (lookupExpression?_sound found) raw))

theorem original_not_callable {childSize : Nat} {callable : Dynamic.Value}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before callee callable after)
    (invalid : ¬ Dynamic.CallableValue callable) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [childSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault .notCallable) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectNotCallable child invalid

theorem original_arguments_fault {calleeSize argumentsSize : Nat} {callable : Dynamic.Value}
    {calleeHeap : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (callableShape : Dynamic.CallableValue callable)
    (children : SourceExecutionSize.ExpressionsFault program argumentsSize context evidence source environment calleeHeap arguments reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectArguments first callableShape children

theorem original_source_arity {calleeSize argumentsSize : Nat} {callable : Dynamic.Value}
    {calleeHeap : Dynamic.Heap} {values : List Dynamic.Value}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values after)
    (mismatch : metadata.argumentCount ≠ arguments.length) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]])
      context evidence source environment before callee arguments metadata node.requirements
      (.fault (.argumentArityMismatch metadata.argumentCount arguments.length)) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectSourceArity first children mismatch

theorem original_coercion_fault {calleeSize argumentsSize coercionSize : Nat} {callable packed : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {values : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (arity : arguments.length = metadata.argumentCount) (pack : Dynamic.ValuesPack values packed)
    (failed : SourceExecutionSize.CoercionPathFaults program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectArgumentCoercion first children arity pack failed

theorem original_application_fault {calleeSize argumentsSize coercionSize callSize : Nat}
    {callable packed coerced : Dynamic.Value} {values appliedArguments : List Dynamic.Value}
    {calleeHeap argumentsHeap coercedHeap : Dynamic.Heap} {invocationEvidence : Dynamic.EvidenceEnvironment}
    {reason : Dynamic.SemanticFault}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (packBefore : Dynamic.ValuesPack values packed)
    (converted : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
    (packAfter : Dynamic.ValuesPack appliedArguments coerced)
    (arity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
    (failed : SourceExecutionSize.CallableFaults program callSize context evidence invocationEvidence coercedHeap callable appliedArguments reason after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize, callSize]])
      context evidence source environment before callee arguments metadata node.requirements (.fault reason) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.fault
  apply SourceExecutionSize.ExpressionFaults.form (lookupExpression?_sound found)
  rw [form]
  exact .indirectApply first children packBefore converted packAfter arity appliedArity failed

theorem original_application_value {calleeSize argumentsSize coercionSize callSize : Nat}
    {callable packed coerced result : Dynamic.Value} {values appliedArguments : List Dynamic.Value}
    {calleeHeap argumentsHeap coercedHeap : Dynamic.Heap} {invocationEvidence : Dynamic.EvidenceEnvironment}
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (coercions : node.coercions = []) (unique : NodeOccurrencesUnique source)
    (layout : node.requirements = coercionRequirementIds metadata.argumentCoercions)
    (first : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee callable calleeHeap)
    (children : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment calleeHeap arguments values argumentsHeap)
    (packBefore : Dynamic.ValuesPack values packed)
    (converted : SourceExecutionSize.CoercionPathExecutes program coercionSize context evidence argumentsHeap metadata.argumentCoercions packed coerced coercedHeap)
    (packAfter : Dynamic.ValuesPack appliedArguments coerced)
    (arity : arguments.length = metadata.argumentCount) (appliedArity : appliedArguments.length = metadata.argumentCount)
    (application : SourceExecutionSize.CallableApplies program callSize context evidence invocationEvidence coercedHeap callable appliedArguments result after) :
    IndirectTraceAt program (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, coercionSize, callSize], 1])
      context evidence source environment before callee arguments metadata node.requirements (.value result) after := by
  apply indirect_inv_sized found form coercions unique
  apply ExpressionOutcome.value
  apply SourceExecutionSize.ExpressionEvaluates.intro (lookupExpression?_sound found)
  · rw [form]
    exact .indirectCall (by simpa [coercions, coercionRequirementIds] using layout)
      first children packBefore converted packAfter arity appliedArity application
  · rw [coercions]
    exact .nil
end OriginalIndirect

section OriginalClosure
variable {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
  {before bound after : Dynamic.Heap} {function : Dynamic.Closure} {arguments : List Dynamic.Value}
  {bodySize : Nat} {parameterTypes : List TypeSystem.Ty} {callContext finalContext : SourceSemantics.Context}
  {entry environment finalEnvironment : Dynamic.Environment} {copied : Dynamic.Heap}

theorem original_closure_arity (mismatch : function.parameters.length ≠ arguments.length) :
    ClosureCompletion program context caller invocation before function arguments 1
      (.fault (.argumentArityMismatch function.parameters.length arguments.length)) before :=
  closure_completed_sized (.fault (.closureArity mismatch))

theorem original_closure_returned {value : Dynamic.Value}
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.returned value) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.value value) after :=
  closure_completed_sized (.value (.closure same frame parameters copy allocation executed rfl))

theorem original_closure_unit
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function) (unit : function.resultType = .unit)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.fallthrough finalEnvironment) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.value .unit) after :=
  closure_completed_sized (.value (.closureUnit same frame unit parameters copy allocation executed ⟨finalEnvironment, rfl⟩))

theorem original_closure_fault {reason : Dynamic.SemanticFault}
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (failed : SourceExecutionSize.FunctionStatementsFault program bodySize callContext function.evidence function.source
      environment bound function.body finalContext reason after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.fault reason) after :=
  closure_completed_sized (.fault (.closureBody same frame parameters copy allocation failed))

theorem original_closure_control_escape
    (same : invocation = function.evidence) (frame : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes callContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocation : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (executed : SourceExecutionSize.FunctionStatementsExecute program bodySize callContext function.evidence function.source
      environment bound function.body finalContext (.breaking finalEnvironment) after) :
    ClosureCompletion program context caller invocation before function arguments (SourceExecutionSize.stepSize [bodySize]) (.fault .controlEscapedFunction) after :=
  closure_completed_sized (.fault (.closureControlEscape same frame parameters copy allocation executed (Or.inl ⟨finalEnvironment, rfl⟩)))

/-- A reached closure application retains the copies of its captures, made
from the call's heap, and the parameter allocation over the copies. -/
theorem retained_captured_allocation {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (original : CallOutcome program size context caller invocation before (.closure function) arguments outcome after)
    (arity : function.parameters.length = arguments.length) :
    ∃ child types childContext entry copied childEnvironment allocated,
      invocation = function.evidence ∧ Dynamic.ClosureFrame program function ∧
      MonoBindersExtend function.source.owner function.context function.parameters types childContext ∧
      Dynamic.EnvironmentCopies function.source function.captured before entry copied ∧
      Dynamic.BindersAllocate entry copied function.parameters arguments childEnvironment allocated ∧
      BodyTrace program child function childContext childEnvironment allocated outcome after ∧ child < size := by
  cases closure_completed_sized original with
  | arity mismatch => exact False.elim (mismatch arity)
  | reached same frame parameters copy allocation body smaller _ =>
    exact ⟨_, _, _, _, _, _, _, same, frame, parameters, copy, allocation, body, smaller⟩

/-- With no parameters the body runs in the copies of the captures, from the
heap the copies end in. Both bindings of a shadowed name are copied and keep
their order. -/
theorem empty_arity_keeps_shadowed_captures {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    {name : Resolved.LocalId} {first second : Dynamic.Location} {unused : Dynamic.Environment}
    (parameters : function.parameters = [])
    (captured : function.captured = (name, first) :: (name, second) :: unused)
    (original : CallOutcome program size context caller invocation before (.closure function) [] outcome after) :
    ∃ child types childContext firstCopy secondCopy unusedCopies copied,
      invocation = function.evidence ∧ Dynamic.ClosureFrame program function ∧
      MonoBindersExtend function.source.owner function.context [] types childContext ∧
      Dynamic.EnvironmentCopies function.source ((name, first) :: (name, second) :: unused) before
        ((name, firstCopy) :: (name, secondCopy) :: unusedCopies) copied ∧
      BodyTrace program child function childContext ((name, firstCopy) :: (name, secondCopy) :: unusedCopies)
        copied outcome after ∧ child < size := by
  obtain ⟨child, types, childContext, entry, copied, childEnvironment, allocated, same, frame, typed, copy,
    allocation, body, smaller⟩ := retained_captured_allocation original (by simp [parameters])
  rw [parameters] at typed allocation
  rw [captured] at copy
  cases allocation
  have shape : ∃ firstCopy secondCopy unusedCopies,
      entry = (name, firstCopy) :: (name, secondCopy) :: unusedCopies := by
    cases copy with
    | shared _ tail =>
      cases tail with
      | shared _ _ => exact ⟨_, _, _, rfl⟩
      | copied _ _ _ _ => exact ⟨_, _, _, rfl⟩
    | copied _ _ _ tail =>
      cases tail with
      | shared _ _ => exact ⟨_, _, _, rfl⟩
      | copied _ _ _ _ => exact ⟨_, _, _, rfl⟩
  obtain ⟨firstCopy, secondCopy, unusedCopies, rfl⟩ := shape
  exact ⟨child, types, childContext, firstCopy, secondCopy, unusedCopies, copied, same, frame, typed, copy, body,
    smaller⟩
end OriginalClosure

section ExistingNamedAndBuiltin
theorem original_global_child {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program instantiation body function)
    {size : Nat} {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (original : CallOutcome program size context caller function.evidence before
      (.global ⟨instantiation, function.evidence⟩) arguments outcome after) :
    ∃ child, BodyOutcome program child body function.evidence before arguments outcome after ∧ child < size :=
  source_call_body unique frame arity original

theorem original_builtin_pure {program : Program} {context : SourceSemantics.Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {heap : Dynamic.Heap}
    {function : Dynamic.BuiltinFunction} {arguments : List Dynamic.Value} {result : Dynamic.Value}
    (applied : Dynamic.BuiltinApplies function.id arguments result) :
    CallOutcome program 1 context caller invocation heap (.builtin function) arguments (.value result) heap :=
  .value (.builtin applied)
end ExistingNamedAndBuiltin

section Boundaries
theorem boundary_grade_differs_from_wrapped_parent :
    SourceExecutionSize.stepSize [1] ≠ SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [1]] := by decide

theorem full_captured_suffix {function : Dynamic.Closure} {tail : Dynamic.Environment}
    (nonempty : tail ≠ []) : function.captured ++ tail ≠ function.captured := by
  intro equal
  have lengths := congrArg List.length equal
  have : tail.length = 0 := by simp only [List.length_append] at lengths; omega
  exact nonempty (by simpa only [List.length_eq_zero_iff] using this)
end Boundaries

end Tests.SourceCoreCallableIndirectCallSourceBounds

namespace Tests.SourceCoreCallableIndirectCallSourceBounds.Stage
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open Staging.CallBoundary CallableIndirectCallStageBounds

/-- An actual rejected guard uses only the completed callee prefix. -/
theorem rejected_prefix {program : Program} {frame : Frame} {calleeSize : Nat}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {callable : Dynamic.Value}
    {contract : Staging.CallGuard.Contract} {reason : Staging.CallGuard.Fault}
    (evaluated : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence
      source environment before callee callable after)
    (bound : frame.Binds callable contract)
    (rejected : Staging.CallGuard.Rejects frame.stages contract call arguments reason) :
    ExecutesAt program frame (SourceExecutionSize.stepSize [calleeSize]) context evidence source
      environment before call callee arguments metadata (.stageFault reason) after ∧
    Executes program frame context evidence source environment before call callee arguments
      metadata (.stageFault reason) after ∧
    calleeSize < SourceExecutionSize.stepSize [calleeSize] := by
  have boundary := ExecutesAt.stageRejected (metadata := metadata) evaluated (.contract bound rejected)
  exact ⟨boundary, boundary.sound, SourceExecutionSize.child_lt_stepSize (by simp)⟩

/-- Inversion retains the same callee witness and exact post-callee heap. -/
theorem rejected_original_child {program : Program} {frame : Frame} {size : Nat}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {reason : Staging.CallGuard.Fault}
    (boundary : ExecutesAt program frame size context evidence source environment before
      call callee arguments metadata (.stageFault reason) after) :
    ∃ calleeSize callable, calleeSize < size ∧
      SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment
        before callee callable after ∧ GuardRejects frame call arguments callable reason := by
  obtain ⟨calleeSize, callable, _, below, evaluated, rejected⟩ := boundary.stageFault_inv
  exact ⟨calleeSize, callable, below, evaluated, rejected⟩

/-- A missing callee has boundary size two and enclosing expression size three. -/
theorem missing_callee_sizes {program : Program} {frame : Frame}
    {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {call callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {node : ExpressionNode}
    (contains : ContainsExpression source call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (absent : Dynamic.ExpressionMissing source callee) :
    ExecutesAt program frame 2 context evidence source environment heap call callee arguments metadata
      (.semanticFault (.missingExpression callee)) heap ∧
    SourceExecutionSize.ExpressionFaults program 3 context evidence source environment heap call
      (.missingExpression callee) heap ∧ (2 : Nat) ≠ 3 := by
  have child : SourceExecutionSize.ExpressionFaults program 1 context evidence source environment
      heap callee (.missingExpression callee) heap := .missing absent
  have boundary : ExecutesAt program frame 2 context evidence source environment heap call callee
      arguments metadata (.semanticFault (.missingExpression callee)) heap := .calleeFault child
  have raw := boundary.semanticFault_plain_sized node.requirements node.coercions
  have original : SourceExecutionSize.ExpressionFaults program 3 context evidence source environment
      heap call (.missingExpression callee) heap :=
    .form contains (by simpa only [form] using raw)
  exact ⟨boundary, original, by decide⟩

end Tests.SourceCoreCallableIndirectCallSourceBounds.Stage
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewBodyTree
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewBodyTree
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericLexicalStatements

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_body_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_body_view.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean : ExpressionNode := {id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def returned : StatementNode := ⟨⟨⟨owner, 1⟩⟩, span, .bool, .returnStmt (some boolean.id)⟩
private def parent : ExpressionNode := {
  id := id 2, span, type := .function .unit .bool, form := .lambda [] .bool [returned.id]}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression parent.id], nodes := [.expression boolean, .statement returned, .expression parent]}
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def roots : List NodeId := [.statement returned.id]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem edited : LocalView source view [parent.id] := withNode unique (by rfl) rfl rfl

private theorem reached_shape {node : NodeId} (reached : Reaches source roots node) :
    node = .statement returned.id ∨ node = .expression boolean.id := by
  induction reached with
  | root member => exact .inl (by simpa [roots] using member)
  | @expression expression node child parent found edge ih =>
    rcases ih with incompatible | equal
    · cases incompatible
    · have same : expression = boolean.id := NodeId.expression.inj equal
      subst expression
      have nodeEq : boolean = node := Option.some.inj ((show source.lookupExpression? boolean.id = some boolean from rfl).symm.trans found)
      subst node
      cases edge
  | @statement statement node child parent found edge ih =>
    rcases ih with equal | incompatible
    · have same : statement = returned.id := NodeId.statement.inj equal
      subst statement
      have nodeEq : returned = node := Option.some.inj ((show source.lookupStatement? returned.id = some returned from rfl).symm.trans found)
      subst node
      exact .inr (by simpa [returned, StatementForm.references] using edge)
    · cases incompatible

private theorem avoids : Avoids source roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  rcases reached_shape reached with incompatible | equal
  · cases incompatible
  · cases equal

/-- The parent header really changes; the disjoint body proof retains the
literal's complete original metadata and the same generated return code. -/
theorem literal_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {context : SourceSemantics.Context} {scope : Scope} :
    source ≠ view ∧ Tree layouts ⟨owner, []⟩ [] frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate [] view)
      context scope true [returned.id] .bool .bool (LocalLoop.returnValue .bool (LanguageResult.success (.bool true))) := by
  refine ⟨by decide, ?_⟩
  apply CallableLambdaViewBodyTree.literals (statements := [returned.id]) (solved := []) edited (by exact avoids)
  exact GenericLexicalStatements.Tree.returnValue (node := returned) (expressionNode := boolean)
    (lowered := ⟨.bool, LanguageResult.success (.bool true)⟩) [] (by rfl) rfl (by rfl) rfl
    ⟨boolean, rfl, .bool true rfl rfl rfl rfl⟩

private def literalPolicy : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt =>
    SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id) }

/-- An accepted actual flow expression at the changed view yields the original
source's static Tree. The expression callback is the real basic literal path. -/
theorem accepted_original {layouts : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {context : SourceSemantics.Context} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy literalPolicy 4 view []
      [returned.id] .bool (fun _ => Word.zero) true Word.zero = .ok code) :
    Tree layouts ⟨owner, []⟩ [] frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate [] source)
      context [] true [returned.id] .bool .bool code := by
  have emitted : SourceCoreLoops.lowerFlowStatementsWithPolicy literalPolicy 4 view []
      [returned.id] .bool (fun _ => Word.zero) true Word.zero =
      .ok (LocalLoop.returnValue .bool (LanguageResult.success (.bool true))) := by rfl
  have same := Except.ok.inj (emitted.symm.trans accepted)
  cases same
  exact CallableLambdaViewBodyTree.literals_original edited (by exact avoids) literal_body.2

/-- A direct body reference to an edited parent violates the necessary
freshness premise. No tree/acyclicity assumption is silently added. -/
theorem parent_reference_forbidden {original : TypedSource} {bodyRoots : List NodeId}
    {changed : ExpressionId} {statement : StatementId} {node : StatementNode}
    (root : NodeId.statement statement ∈ bodyRoots)
    (found : original.lookupStatement? statement = some node)
    (edge : NodeId.expression changed ∈ node.form.references) :
    ¬Avoids original bodyRoots [changed] :=
  fun avoids => avoids changed (by simp) (.statement (.root root) found edge)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make() returns (function() returns (Word)) { return lam() -> Word { let x: Word = 1; { 2; } if (true) { 3; } else { 4; } return 5; }; }"}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "body view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "body view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"body view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "body view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "body view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let template ← match prepared.ancestry.templates.lambdas with
    | template :: _ => pure template
    | [] => throw (IO.userError "body view template missing")
  let statements ← match template.node.form with
    | .lambda [] _ statements => pure statements
    | _ => throw (IO.userError "body view zero-parameter lambda missing")
  let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
    | some caller => pure caller
    | none => throw (IO.userError "body view actual caller missing")
  let original := template.context.inventory.source
  let edited := SourceCoreEvidence.withNode original {template.node with type := .bool}
  let compilation : SourceCoreFunctions.Context := {
    plan, globals := automatic.prepared.globals, owner := template.owner, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
  let values := SourceCoreCompatibleValues.Context.initial automatic.checked
  let expressions := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let allocate := prepared.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
  let policy : SourceCoreLoops.Policy := {
    lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
      (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
    readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
    lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder values.checked
    sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
      automatic.prepared.globals.length allocate)}
  let before ← SourceCompilerFeatureSupport.get "original lexical body"
    (SourceCoreLoops.lowerStatementsWithPolicy policy 300 original [] statements .word (fun _ => Word.zero) Word.zero Word.zero)
  let after ← SourceCompilerFeatureSupport.get "edited lexical body"
    (SourceCoreLoops.lowerStatementsWithPolicy policy 300 edited [] statements .word (fun _ => Word.zero) Word.zero Word.zero)
  SourceCompilerFeatureSupport.require (before == after) "parent header edit changed actual lexical body allocation/control code"
  SourceCompilerFeatureSupport.require
    (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders edited)
    "parent header edit changed original binder metadata"
  IO.println "lambda body views: disjoint literal Tree and actual let/block/if compiler code preserved GREEN"
end Tests.SourceCoreCallableLambdaViewBodyTree
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewBuiltinBodyTree
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewBuiltinBodyTree
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability
abbrev Scope := SourceCoreLocalCell.Scope

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source view : TypedSource} {changed : List ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- The compiler really accepts the view body. The recovered canonical Tree
has the exact finished code, but canonical typing, syntax and acceptance are
not conclusions. No static child transformation premise remains. -/
theorem contextual_original
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope} {context : SourceSemantics.Context}
    (edited : LocalView source view changed)
    (ordinary : CompatibleExpressionBuiltins.Ordinary view locals compilation.owner)
    (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation (some native) parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (syntaxTree : BuiltinLexicalStatements.Syntax view context true statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel view scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt
        context scope true statements expected type flow := by
  obtain ⟨flow, same, tree⟩ := BuiltinLexicalStatements.tree_of_contextual_body ordinary unique closed residual
    sourceSignatures declarations readExpression lowerRead leafLowerer readStatement representationBinder lowerBinder sourceCells
    lowerExpression syntaxTree projection accepted
  exact ⟨flow, same, CallableLambdaViewBuiltinBodyTree.original edited avoids tree⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require

/-- Existing integer-result admission is used without changing stage rules.
The explicit local function type keeps each real emitted lambda monomorphic. -/
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed(seed: Word, branch: Bool) returns (integer) { let f: function() returns (integer) = lam() -> integer { let missing: Word; let x: Word = wordFromInteger(integerAdd(wordToInteger(seed), 2)); { let nested: Word = wordFromInteger(integerSub(wordToInteger(x), 1)); wordToInteger(nested); } if (branch) { let delta: Word = wordFromInteger(integerSub(wordToInteger(x), wordToInteger(seed))); return wordToInteger(delta); } else { integerEq(wordToInteger(x), wordToInteger(seed)); } return wordToInteger(x); }; return f(); }",
    "function returned(seed: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { wordToInteger(seed); return integerSub(wordToInteger(seed), 1); }; return f(); }",
    "function unit(seed: Word) returns (integer) { let f: function() = lam() { { wordToInteger(seed); } return; }; f(); return wordToInteger(seed); }",
    "function empty() returns (integer) { let f: function() = lam() { }; f(); return 0; }",
    "function failed(seed: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping(Bool => Word); let warm: Word = m[false]; let missing: Word; { wordToInteger(seed); } return integerAdd(wordToInteger(warm), wordToInteger(missing)); }; return f(); }"]}] }

private def inspect (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let checked := entry.cached.compatible.checked
  let values := SourceCoreCompatibleValues.Context.initial checked
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let original := template.context.inventory.source
    let .lambda [] _ statements := template.node.form | throw (IO.userError "builtin body view zero-parameter lambda missing")
    let caller ← get "builtin body view owner" (SourceCompilationPlan.exactSpecialization base.plan template.owner)
    let changed := SourceCoreEvidence.withNode original {template.node with type := .unit}
    let compilation : SourceCoreFunctions.Context := {
      plan := base.plan, globals := base.globals, owner := template.owner, administrativePrefix := 1,
      solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
    let scope ← original.inputs.reverse.mapM fun binder => do
      pure (binder.id, ← get "builtin body view scope" (checked.catalog.project binder.scheme.body))
    let expressions := {SourceCoreCompatibleDataExpressions.functionPolicy 200 values with
      callables := SourceCoreGeneralFunctions.callablePolicy (some indexed.ancestry.graph.inputs.callable) template.active}
    let allocate := indexed.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
    let policy : SourceCoreLoops.Policy := {
      lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
        (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
      readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
      lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
      sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator indexed.ancestry.layout.frame
        base.globals.length allocate) }
    let before ← get "original builtin lexical body" (SourceCoreLoops.lowerStatementsWithPolicy policy 500 original scope
      statements template.resultType (fun _ => Word.zero) Word.zero Word.zero)
    let after ← get "view builtin lexical body" (SourceCoreLoops.lowerStatementsWithPolicy policy 500 changed scope
      statements template.resultType (fun _ => Word.zero) Word.zero Word.zero)
    require (before == after) "lambda header view changed builtin body/control/marked allocation code"
    require (original != changed) "builtin body view failed to change the actual lambda header"
    require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders changed)
      "builtin body view changed the original binding metadata"
    count := count + 1
  require (count == 1) s!"builtin body view expected one emitted lambda, found {count}"

def run : IO Unit := do
  let program ← get "builtin body view checker" (checkProgram workspace)
  let seed := SourceCompilerFeatureSupport.scalar 7
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("mixed", [seed, .bool true], .integer 2), ("mixed", [seed, .bool false], .integer 9),
    ("returned", [seed], .integer 6), ("unit", [seed], .integer 7), ("empty", [], .integer 0)]
  for (name, arguments, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    inspect entry
    require ((← entry.run arguments) == expected) s!"builtin body view {name} changed lexical result"
    for fuel in [0, 10, 100] do
      entry.checkResume arguments expected fuel
  let entry ← SourceCompilerFeatureSupport.compileNamed program "failed"
  inspect entry
  let complete ← entry.invoke [seed]
  let (reason, heapSize) ← match complete.outcome with
    | .failed reason session => pure (reason, session.heapSize)
    | _ => throw (IO.userError "builtin body view failure did not remain a language fault")
  let audited ← entry.audit [seed]
  let cells := (SourceCompilerFeatureSupport.sourceState audited).heap
  require (cells.any fun cell => match cell.value with
    | some (.mapping .bool .word []) => true | _ => false)
    "builtin body view lost lazy mapping initialization before failure"
  require (cells.any fun cell => match cell.value with
    | some (.word value) => value == Word.zero | _ => false)
    "builtin body view lost initialized local before failure"
  require ((cells.filter fun cell => cell.type == .word && cell.value.isNone).length == 1)
    "builtin body view changed the uninitialized faulting cell"
  for fuel in [0, 10, 100] do
    let suspended ← entry.invoke [seed] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel}
    let checkpoint ← match suspended.outcome with
      | .outOfFuel checkpoint => pure checkpoint
      | _ => throw (IO.userError "builtin body view fault fixture did not suspend")
    match ← checkpoint.resume 300000 1024 with
    | .failed resumed session =>
      require (resumed == reason && session.heapSize == heapSize) "builtin body view resumed fault/effects changed"
    | _ => throw (IO.userError "builtin body view fault checkpoint changed completion")
  IO.println "lambda builtin body views: same marked let/block/if/discard/return/Unit code, scoped results, failure effects and resume GREEN"

end Tests.SourceCoreCallableLambdaViewBuiltinBodyTree
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewBuiltinTrees
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewBuiltinTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionBuiltins CallableLambdaViewEdits CallableLambdaBodyReachability
namespace Nested
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_builtin_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_builtin_view.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def parentNode : ExpressionNode := {id := id 6, span, type := .function .unit .word, form := .lambda [] .word []}
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 5)], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .expression parentNode]}
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax
private theorem noCoercions : ∀ expression node, source.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem certified (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  tree_of_functions unique (by intro actual declared index native selected; cases selected) rfl rfl rfl
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxTree (by cbv) groupTyped accepted

private def view := SourceCoreEvidence.withNode source {parentNode with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parentNode.id] := withNode unique (by rfl) rfl rfl
private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode,
      ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl <;> simp [footprint, id]
private theorem reached_member {node : NodeId} (reached : Reaches source source.roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression (id 5) := by simpa [source] using member
    rw [same]
    simp [footprint]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih
private theorem avoids : Avoids source source.roots [parentNode.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parentNode, footprint, id] at impossible

/-- The actual builtin lowering retains both ordered conversions and contracted
callee code while the enclosing lambda header really changes. -/
theorem accepted_nested (native : SourceCoreGeneralFunctions.CallableContext) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody 6 compilation source [] (id 5) reasonAt = .ok code) :
    source ≠ view ∧ Tree 100 values view context [] reasonAt [] (id 5) code :=
  ⟨by decide, CallableLambdaViewBuiltinTrees.builtins edited avoids (certified native accepted) (.root (by simp [source]))⟩

theorem original_nested {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 100 values view context [] reasonAt [] (id 5) code) :
    Tree 100 values source context [] reasonAt [] (id 5) code :=
  CallableLambdaViewBuiltinTrees.builtins_original edited avoids tree (.root (by simp [source]))

/-- Actual argument/callee reachability cannot be silently excluded. -/
theorem changed_operand_rejected : ¬ Avoids source source.roots [literalNode.id] := by
  intro fresh
  have grouped : Reaches source source.roots (.expression (id 5)) := .root (by simp [source])
  have outer : Reaches source source.roots (.expression (id 4)) :=
    .expression grouped (by rfl) (by simp [groupNode, ExpressionForm.references])
  have inner : Reaches source source.roots (.expression (id 2)) :=
    .expression outer (by rfl) (by simp [outerNode, ExpressionForm.references])
  have argument : Reaches source source.roots (.expression literalNode.id) :=
    .expression inner (by rfl) (by simp [innerNode, ExpressionForm.references, literalNode])
  exact fresh literalNode.id (by simp) argument

end Nested

/-- Actual ordinary typed lowering at a view yields the canonical Tree under
reachability. Independent typing and syntax refer to that actual view; the
conclusion does not assert canonical compiler acceptance or canonical typing. -/
theorem builtin_original_from_contextual
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {values : SourceCoreCompatibleValues.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {compilation : SourceCoreFunctions.Context} {native : SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}
    (ordinary : CompatibleExpressionBuiltins.Ordinary view locals compilation.owner) (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (signatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id) (found : view.lookupExpression? id = some node)
    (typed : ExpressionHasType view context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
      assignments diagnostics compilation (some native) parent skip fuel view scope id reasonAt = .ok code) :
    CompatibleExpressionBuiltins.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code :=
  CallableLambdaViewBuiltinTrees.builtins_original edited avoids
    (CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
      readPolicy lowerPolicy leafPolicy accepted) reached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require
/-- The enclosing integer result uses the existing staged admission profile.
Each lambda is explicitly monomorphic and really emitted by the indexed factory. -/
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function nested(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { return integerSub(integerAdd(wordToInteger(a), wordToInteger(b)), wordToInteger(b)); }; return 0; }",
    "function parents(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { return integerSub(wordToInteger(a), wordToInteger(b)); }; return 0; }",
    "function compared(a: Word, b: Word) returns (integer) { let f: function() returns (Bool) = lam() -> Bool { return integerEq(wordToInteger(a), wordToInteger(a)) && !integerLt(wordToInteger(a), wordToInteger(b)); }; return 0; }",
    "function construct(a: Word, b: Word) returns (integer) { let f: function() returns (Box<integer>) = lam() -> Box<integer> { return Box(integerSub(wordToInteger(a), wordToInteger(b))); }; return 0; }",
    "function member(a: Word, b: Word) returns (integer) { let f: function() returns (Box<integer>) = lam() -> Box<integer> { return Box(integerSub(wordToInteger(a), wordToInteger(b))); }; return 0; }",
    "function key(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping((Bool, Bool) => Word); return wordToInteger(m[(integerEq(wordToInteger(b), wordToInteger(b)), integerLt(wordToInteger(b), wordToInteger(b)))]); }; return 0; }",
    "function skipped(a: Word, b: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let n: mapping(Bool => Word); return integerEq(wordToInteger(a), wordToInteger(a)) ? integerSub(wordToInteger(a), wordToInteger(b)) : wordToInteger(n[true]); }; return 0; }",
    "function failed() returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping(Bool => Word); let missing: Word; return integerSub(wordToInteger(m[false]), wordToInteger(missing)); }; return 0; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids | .call _ ids _ => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (callables : SourceCoreGeneralFunctions.CallableContext) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (originalExpression : ExpressionId) : IO Unit := do
  let originalRoot ← match original.lookupExpression? originalExpression with
    | some node => pure node | none => throw (IO.userError "builtin view original root missing")
  let (source, expression) := if name == "member" then
    let member : ExpressionNode := {id := ⟨⟨original.owner, 100000⟩⟩, span := originalRoot.span, type := .integer, form := .member originalExpression "0" 0}
    ({original with roots := [.expression member.id], nodes := original.nodes ++ [.expression member]}, member.id)
    else if name == "parents" then
      let negated : ExpressionNode := {id := ⟨⟨original.owner, 100000⟩⟩, span := originalRoot.span, type := .integer, form := .unary .bitNot originalExpression}
      let pair : ExpressionNode := {id := ⟨⟨original.owner, 100001⟩⟩, span := originalRoot.span, type := .product .integer .integer, form := .tuple [negated.id, originalExpression]}
      let group : ExpressionNode := {id := ⟨⟨original.owner, 100002⟩⟩, span := originalRoot.span, type := pair.type, form := .group pair.id}
      ({original with roots := [.expression group.id], nodes := original.nodes ++ [negated, pair, group].map Node.expression}, group.id)
    else (original, originalExpression)
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "builtin view binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "builtin view binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "builtin view empty mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .word =>
        if binder.name == "missing" then pure (OptionalCell.allocate native, none)
        else
          let word := Word.ofNatModulo (if binder.name == "a" then 7 else 3)
          pure (OptionalCell.allocateInitialized native (.word word), some (.word word))
      | other => throw (IO.userError s!"builtin view unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "builtin view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let policy := {SourceCoreCompatibleDataExpressions.functionPolicy 150 values with
    callables := SourceCoreGeneralFunctions.callablePolicy (some callables) []}
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
  let before := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation source scope expression reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation modified scope expression reasonAt
  let lowered ← get s!"builtin view actual compiler {name}" before
  let same ← get s!"builtin view modified compiler {name}" after
  require (reprStr lowered == reprStr same) "builtin view changed code, operand order or contract"
  require (source != modified) "builtin view header was unchanged"
  let rootNode ← match source.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "builtin view selected root missing")
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  require native.check s!"builtin view {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      require (store.length ≥ bindings.length + 1) "builtin view lost the retained input store prefix"
      require (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "builtin view changed ambient closure"
      if name == "failed" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "builtin view missing first fault")
        require (result == .inLeft lowered.type (.word (reasonAt failed.id))) "builtin view first fault changed"
      else
        let payload ← match result with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"builtin view {name} did not succeed: {reprStr result}")
        let decoded ← get "builtin view decoded output" (SourceCoreCompatibleValues.decode 100 values rootNode.type payload)
        match name, decoded with
        | "nested", .integer 7 | "member", .integer 4 | "skipped", .integer 4 | "key", .integer 0
        | "parents", .product (.integer (-5)) (.integer 4) | "compared", .bool true => pure ()
        | "construct", .constructed retained [.integer 4] =>
          let .constructor instantiation _ := originalRoot.form | throw (IO.userError "builtin view constructor source missing")
          require (retained == instantiation) "builtin view erased raw constructor metadata"
        | _, other => throw (IO.userError s!"builtin view {name} changed output: {reprStr other}")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let expectedCell := match expected with
          | some value => if binder.name == "n" then Value.inLeft type .unit else .inRight .unit value
          | none => .inLeft type .unit
        require (store[bindings.length - position]? == some expectedCell)
          s!"builtin view {name} changed ordered/lazy effects at {binder.name}"
    | other => throw (IO.userError s!"builtin view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "builtin view checker" (checkProgram workspace)
  let requests := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"builtin view specialization: {reprStr other}")
  let automatic ← get "builtin view base factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let indexed ← get "builtin view indexed factory" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let source := template.context.inventory.source
    let .lambda _ _ statements := template.node.form | throw (IO.userError "builtin view lambda form missing")
    let expression ← match statements.findSome? fun id => match source.lookupStatement? id with
      | some node => match node.form with | .returnStmt (some expression) => some expression | _ => none
      | none => none with
      | some expression => pure expression | none => throw (IO.userError "builtin view lambda return missing")
    let name := (program.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared indexed.ancestry.graph.inputs.callable source template.owner template.node name expression
    count := count + 1
  require (count == 8) s!"builtin view lambda cases missing: {count}"
  IO.println "lambda builtin views: nested ordered calls, operator/constructor/member/product-key parents, raw headers, lazy/fault effects, actual typed slots and resume GREEN"

end Tests.SourceCoreCallableLambdaViewBuiltinTrees
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewDataTrees
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewDataTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionRecursive
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_data_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_data_view.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sourceType : TypeSystem.Ty := .nominal owner []
private def firstSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 0⟩, "First", [.bool, .bool], ⟨span, ⟨[], ⟨span, "First"⟩, none⟩⟩⟩
private def secondSignature : ProgramDataConstructorSignature :=
  ⟨⟨owner, 1⟩, "Second", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Second"⟩, none⟩⟩⟩
private def signature : ProgramDataSignature := {
  id := owner, name := "Row", parameters := [], constructors := [firstSignature, secondSignature]
  source := ⟨span, ⟨none, ⟨span, "Row"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def instantiation : DataConstructorInstantiation := ⟨secondSignature.id, [], [.bool, .bool], sourceType⟩
private def boolean : ExpressionNode := { id := id 0, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def constructorNode : ExpressionNode := { id := id 1, span, type := sourceType, form := .constructor instantiation [id 0, id 0] }
private def memberNode : ExpressionNode := { id := id 2, span, type := .bool, form := .member (id 1) "1" 1 }
private def unaryNode : ExpressionNode := { id := id 3, span, type := .bool, form := .unary .logicalNot (id 2) }
private def wrappedNode : ExpressionNode := { id := id 4, span, type := sourceType, form := .constructor instantiation [id 3, id 2] }
private def selectedNode : ExpressionNode := { id := id 5, span, type := .bool, form := .member (id 4) "0" 0 }
private def conditionalNode : ExpressionNode := { id := id 6, span, type := sourceType, form := .conditional (id 5) (id 4) (id 1) }
private def pairedNode : ExpressionNode := { id := id 7, span, type := .product sourceType .bool, form := .tuple [id 6, id 5] }
private def parent : ExpressionNode := {id := id 8, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource :=
  { owner, inputs := [], roots := [.expression (id 7)], nodes := [.expression boolean, .expression constructorNode, .expression memberNode,
      .expression unaryNode, .expression wrappedNode, .expression selectedNode, .expression conditionalNode, .expression pairedNode, .expression parent] }
private def context : SourceSemantics.Context := .ofSignatures signatures
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index native selected; cases selected
private theorem instanceValid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation := by
  refine .intro signature secondSignature (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    (by simp [signature]) rfl rfl ⟨by simp [signature], by simp [ParameterSubstitution.domain, instantiation, signature]⟩ ?_ rfl rfl
  intro parameter replacement member; cases member
private theorem nominalAdmitted : TypeAdmissible context sourceType :=
  ⟨TypeParameterBindersWellFormed.ofSignatures signatures,
    .nominal signature [] (by simp [context, SourceSemantics.Context.ofSignatures, signatures]) rfl .nil⟩
private theorem boolAdmitted : TypeAdmissible context .bool := .bool (TypeParameterBindersWellFormed.ofSignatures signatures)
private theorem boolTyped : ExpressionHasType source context (id 0) .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem constructorTyped : ExpressionHasType source context (id 1) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := constructorNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons boolTyped (.cons boolTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem projection (index : Nat) (inBounds : index = 0 ∨ index = 1) : UniformMemberProjection context sourceType index .bool := by
  refine .intro (dataType := signature) (substitution := []) (by simp [context, SourceSemantics.Context.ofSignatures, signatures])
    ⟨by simp [signature], by simp [ParameterSubstitution.domain, signature]⟩ rfl nominalAdmitted boolAdmitted (by simp [signature]) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rcases inBounds with rfl | rfl <;> rfl
  · intro actual admissible resultType
    cases admissible with
    | intro dataType constructor dataMember constructorMember _ _ _ _ payloads _ =>
      have same : dataType = signature := by simpa [context, SourceSemantics.Context.ofSignatures, signatures] using dataMember
      subst dataType
      simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at constructorMember
      rcases constructorMember with rfl | rfl <;> rw [payloads] <;> rcases inBounds with rfl | rfl <;> rfl
private theorem memberTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := memberNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member constructorTyped (projection 1 (.inr rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 3) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary memberTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem wrappedTyped : ExpressionHasType source context (id 4) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := wrappedNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.constructor instanceValid.toAdmissible (.cons unaryTyped (.cons memberTyped (.nil _)))) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem selectedTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := selectedNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.member wrappedTyped (projection 0 (.inl rfl))) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem conditionalTyped : ExpressionHasType source context (id 6) sourceType := by
  apply ExpressionHasType.ofOrdinary (node := conditionalNode) (rawType := sourceType)
    (lookupExpression?_sound (by cbv)) (.conditional selectedTyped wrappedTyped constructorTyped) nominalAdmitted nominalAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem pairedTyped : ExpressionHasType source context (id 7) (.product sourceType .bool) := by
  have admitted : TypeAdmissible context (.product sourceType .bool) := .product nominalAdmitted boolAdmitted
  apply ExpressionHasType.ofOrdinary (node := pairedNode) (rawType := .product sourceType .bool)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons conditionalTyped (.cons selectedTyped (.nil _)))) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem originalSyntax : Syntax source (id 1) := by
  refine .constructor (node := constructorNode) (by cbv) rfl ?_
  intro child member
  have same : child = id 0 := by simpa using member
  subst child
  exact .fragment (.fragment (.fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ _))))))
private theorem memberSyntax : Syntax source (id 2) :=
  .member (node := memberNode) (by cbv) rfl originalSyntax
private theorem wrappedSyntax : Syntax source (id 4) := by
  refine .constructor (node := wrappedNode) (by cbv) rfl ?_
  intro child member
  have alternatives : child = id 3 ∨ child = id 2 := by simpa using member
  rcases alternatives with rfl | rfl
  · exact .unary (node := unaryNode) (by cbv) rfl memberSyntax
  · exact memberSyntax
private theorem selectedSyntax : Syntax source (id 5) :=
  .member (node := selectedNode) (by cbv) rfl wrappedSyntax
private theorem syntaxTree : Syntax source (id 7) :=
  .pair (node := pairedNode) (by cbv) rfl
    (.conditional (node := conditionalNode) (by cbv) rfl selectedSyntax wrappedSyntax originalSyntax)
    selectedSyntax
variable {checked : SourceCoreCompatibleCatalog.Checked}
private abbrev values (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleValues.Context.initial checked
private abbrev policy (checked : SourceCoreCompatibleCatalog.Checked) := SourceCoreCompatibleDataExpressions.functionPolicy 20 (values checked)
private theorem certified (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  tree_of_functions (values := values checked) unique declarations catalogSignatures.symm rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) pairedTyped accepted

private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parent.id] :=
  withNode unique (by rfl) rfl rfl

private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [boolean, constructorNode, memberNode, unaryNode, wrappedNode, selectedNode,
      conditionalNode, pairedNode, ExpressionForm.references,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id]

private theorem reached_member {node : NodeId} (reached : Reaches source source.roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression (id 7) := by simpa [source] using member
    rw [same]
    simp [footprint]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih

private theorem avoids : Avoids source source.roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parent, footprint, id] at impossible

/-- Actual accepted lowering, independently supplied typing and catalog
metadata build the original tree before the unrelated header is edited. -/
theorem accepted_view (catalogSignatures : checked.signatures = signatures) {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (policy checked) noBody 30 compilation source [] (id 7) (fun _ => reason) = .ok code) :
    source ≠ view ∧ Tree 20 (values checked) view context [] (fun _ => reason) [] (id 7) code :=
  ⟨by decide, CallableLambdaViewRecursiveTrees.recursive edited avoids
    (certified catalogSignatures accepted) (.root (by simp [source]))⟩

theorem recover_original {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 20 (values checked) view context [] (fun _ => reason) [] (id 7) code) :
    Tree 20 (values checked) source context [] (fun _ => reason) [] (id 7) code :=
  CallableLambdaViewRecursiveTrees.recursive_original edited avoids tree (.root (by simp [source]))

/-- A reached constructor cannot be listed as an irrelevant header edit. -/
theorem reached_constructor : ¬ Avoids source source.roots [constructorNode.id] := by
  intro fresh
  have pairReached : Reaches source source.roots (.expression pairedNode.id) := .root (by simp [source, pairedNode])
  have conditionReached : Reaches source source.roots (.expression conditionalNode.id) :=
    .expression pairReached (by rfl) (by simp [pairedNode, ExpressionForm.references, conditionalNode])
  have constructorReached : Reaches source source.roots (.expression constructorNode.id) :=
    .expression conditionReached (by rfl) (by simp [conditionalNode, ExpressionForm.references, constructorNode])
  exact fresh constructorNode.id (by simp) constructorReached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Row { First(Bool, Bool), Second(Bool, Bool) }",
    "function make(seed: Bool) returns (function() returns (Row)) { return lam() -> Row { return .Second(seed, true); }; }",
    "function fail() returns (function() returns (Row)) { return lam() -> Row { let missing: Bool; return .First(missing, true); }; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | fuel + 1, source, expression => match source.lookupExpression? expression with
    | none => []
    | some node => node :: (match node.form with
      | .unary _ operand => reached fuel source operand
      | .binary left _ right => reached fuel source left ++ reached fuel source right
      | .conditional condition thenId elseId => reached fuel source condition ++ reached fuel source thenId ++ reached fuel source elseId
      | .member base _ _ => reached fuel source base
      | .group inner => reached fuel source inner
      | .tuple ids | .constructor _ ids => ids.flatMap (reached fuel source)
      | _ => [])

private def inspect {catalog : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared catalog) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (expression : ExpressionId) : IO Unit := do
  let contextValues := SourceCoreCompatibleValues.Context.initial catalog
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "data view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let originalRoot ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "data view original root missing")
  let .constructor constructor _ := originalRoot.form | throw (IO.userError "data view original constructor missing")
  let newId := fun index => (⟨⟨original.owner, 100000 + index⟩⟩ : ExpressionId)
  let member : ExpressionNode := {id := newId 0, span := originalRoot.span, type := .bool, form := .member expression "0" 0}
  let negated : ExpressionNode := {id := newId 1, span := originalRoot.span, type := .bool, form := .unary .logicalNot member.id}
  let wrapped : ExpressionNode := {id := newId 2, span := originalRoot.span, type := originalRoot.type, form := .constructor constructor [negated.id, member.id]}
  let selected : ExpressionNode := {id := newId 3, span := originalRoot.span, type := .bool, form := .member wrapped.id "0" 0}
  let selectedRow : ExpressionNode := {id := newId 4, span := originalRoot.span, type := originalRoot.type, form := .conditional selected.id wrapped.id originalRoot.id}
  let disjunction : ExpressionNode := {id := newId 5, span := originalRoot.span, type := .bool, form := .binary selected.id .logicalOr member.id}
  let paired : ExpressionNode := {id := newId 6, span := originalRoot.span, type := .product originalRoot.type .bool, form := .tuple [selectedRow.id, disjunction.id]}
  let grouped : ExpressionNode := {id := newId 7, span := originalRoot.span, type := paired.type, form := .group paired.id}
  let source := {original with roots := [.expression grouped.id], nodes := original.nodes ++
    [member, negated, wrapped, selected, selectedRow, disjunction, paired, grouped].map Node.expression}
  let ids := ((reached 100 source grouped.id).filterMap fun node =>
    match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let bindings ← ids.mapM fun binder => do
    let declared ← get "data view binder" (SourceCoreDataPlaces.rootBinder source binder)
    let type ← get "data view binder type" (catalog.catalog.project declared.scheme.body)
    assertTrue (type == .bool) "data view fixture binder is not Boolean"
    let initializer := if declared.name == "missing" then OptionalCell.allocate type
      else OptionalCell.allocateInitialized type (.bool true)
    pure (binder, type, initializer)
  let scope := bindings.map fun (binder, type, _) => (binder, type)
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let actualPolicy := SourceCoreCompatibleDataExpressions.functionPolicy 150 contextValues
  let before := SourceCoreFunctions.lowerExpressionWithPolicy actualPolicy noBody 150 compilation source scope grouped.id reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy actualPolicy noBody 150 compilation modified scope grouped.id reasonAt
  let lowered ← get s!"data view lowering {name}" before
  let same ← get s!"data view modified lowering {name}" after
  assertTrue (reprStr lowered == reprStr same) "data view changed accepted code, type or metadata header"
  assertTrue (source != modified) "data view fixture did not change the source header"
  let frameLayout : SourceCoreCallableIndexedFrames.Layout := ⟨⟨catalog.catalog.definitions.length⟩⟩
  let definitions := catalog.catalog.definitions ++ [frameLayout.definition]
  let adminType := Ty.function .unit frameLayout.type
  let adminExpr := Expr.lambda .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout)
  let body := bindings.foldl (fun body (_, _, initializer) => .letE initializer body) lowered.expression
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type, .letE (.newCell adminType adminExpr) body, definitions⟩
  assertTrue native.check s!"data view {name} failed native checker"
  for fuel in [0, 3, 15, 1000] do
    let finished := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 10000 checkpoint
      | other => other
    match finished with
    | .done value store =>
      assertTrue (store.length == bindings.length + 1) "data view composition allocated unexpected cells"
      assertTrue (store[0]? == some (.closure .unit frameLayout.type (SourceCoreCallableIndexedFrames.empty frameLayout) []))
        "data view composition changed administrative closure"
      if name == "fail" then
        let faultNode ← match original.nodes.findSome? fun
          | .expression node => match node.form with | .reference "missing" (.local _) => some node | _ => none
          | _ => none with
          | some node => pure node | none => throw (IO.userError "data view fault occurrence missing")
        assertTrue (value == .inLeft lowered.type (.word (reasonAt faultNode.id))) "data view composition changed first fault"
      else
        let payload ← match value with
          | .inRight .word payload => pure payload
          | _ => throw (IO.userError s!"data view {name} did not succeed: {reprStr value}")
        let decoded ← get "data view decode" (SourceCoreCompatibleValues.decode 100 contextValues grouped.type payload)
        match decoded with
        | .product (.constructed retained [.bool true, .bool true]) (.bool true) =>
            assertTrue (retained == constructor) "data view composition erased raw constructor metadata"
        | other => throw (IO.userError s!"data view result changed: {reprStr other}")
    | other => throw (IO.userError s!"data view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let checkedProgram ← get "data view checker" (checkProgram workspace)
  let requests := checkedProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run checkedProgram requests 512 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"data view specialization: {reprStr other}")
  let automatic ← get "data view factory" (SourceCoreCompatibleFunctions.prepare checkedProgram plan 500)
  let indexed ← get "data view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut seen := 0
  for template in indexed.ancestry.templates.lambdas do
    let original := template.context.inventory.source
    let name := (checkedProgram.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    let constructor ← match original.nodes.findSome? fun
      | .expression node => match node.form with | .constructor _ _ => some node.id | _ => none
      | _ => none with
      | some expression => pure expression | none => throw (IO.userError "data view original constructor missing")
    inspect automatic.prepared original template.owner template.node name constructor
    seen := seen + 1
  assertTrue (seen == 2) "data view actual lambda fixtures missing"
  IO.println "lambda data views: exact constructor/member/control trees, raw headers, accepted code, fault order, ambient store and resume GREEN"

end Tests.SourceCoreCallableLambdaViewDataTrees
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewEdits
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames.Annotated.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewEdits
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits

/-- Every complete child header in a disjoint footprint survives an actual raw
view. The freshness condition is supplied per occurrence, not inferred from
ownership or from an arbitrary graph being a tree. -/
theorem raw_body_lookups {source : TypedSource} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (ordinary : List RequirementId) (footprint : List ExpressionId)
    (fresh : ∀ id ∈ footprint, id ≠ node.id) :
    ∀ id ∈ footprint, source.lookupExpression? id =
      (SourceCoreEvidence.withNode source
        {node with type := node.rawType, requirements := ordinary, coercions := []}).lookupExpression? id := by
  exact (raw unique found ordinary).expressions (by simpa only [List.mem_singleton] using fresh)

theorem normalized_body_lookups {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source view : TypedSource} {id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id = .ok view)
    (footprint : List ExpressionId) (fresh : ∀ child ∈ footprint, child ≠ id) :
    ∀ child ∈ footprint, source.lookupExpression? child = view.lookupExpression? child := by
  exact (normalized unique accepted).expressions (by simpa only [List.mem_singleton] using fresh)

/-- The edit list composes for successive actual normalizations. -/
theorem successive_normalizations {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source middle final : TypedSource} {first second child : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (left : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source first = .ok middle)
    (right : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent middle second = .ok final)
    (freshFirst : child ≠ first) (freshSecond : child ≠ second) :
    source.lookupExpression? child = final.lookupExpression? child := by
  have before := normalized unique left
  have after := normalized (before.metadata.unique unique) right
  exact (before.trans after).unchanged child (by simp [freshFirst, freshSecond])

/-- An accepted actual allocator equation can be moved to the edited source;
no caller-provided allocation or evaluation relation is needed. -/
theorem accepted_allocation {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {view : TypedSource} {changed : List ExpressionId} {code : Expr}
    (edited : LocalView request.source view changed)
    (accepted : SourceCoreAllocationLayouts.allocate layouts owner active request = .ok code) :
    SourceCoreAllocationLayouts.allocate layouts owner active {request with source := view} = .ok code :=
  (CallableLambdaViewAllocations.allocate_eq (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata)).symm.trans accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }",
    "function qualified(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
  ]}] }

private def checkOtherLookups (source view : TypedSource) (changed : ExpressionId) : IO Unit := do
  for node in source.nodes do
    match node with
    | .expression expression =>
      unless expression.id == changed do
        SourceCompilerFeatureSupport.require (source.lookupExpression? expression.id == view.lookupExpression? expression.id)
          "local edit changed complete metadata at a different expression"
    | .statement statement =>
      SourceCompilerFeatureSupport.require (source.lookupStatement? statement.id == view.lookupStatement? statement.id)
        "local edit changed a statement"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "local edit checker" (checkProgram workspace)
  let roots ← ["make", "qualified"].mapM fun name => do
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"local edit signature missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"local edit worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "local edit base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "local edit indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let lambda ← match prepared.ancestry.templates.lambdas.find? (fun row =>
      match row.node.form with | .lambda (binder :: _) _ _ => binder.name == "item" && binder.scheme.body == .word | _ => false) with
    | some lambda => pure lambda
    | none => throw (IO.userError "ordinary lambda template missing")
  let parameter ← match lambda.node.form with
    | .lambda (parameter :: _) _ _ => pure parameter
    | _ => throw (IO.userError "lambda parameter missing")
  let site ← match prepared.layouts.entries.find? (fun site => decide
      (site.key.owner = lambda.owner ∧ site.key.active = lambda.active ∧ site.key.binder = parameter ∧ site.key.initialized = true)) with
    | some site => pure site
    | none => throw (IO.userError "actual lambda allocation site missing")
  let source := lambda.context.inventory.source
  let originalNode ← match source.lookupExpression? lambda.node.id with
    | some node => pure node
    | none => throw (IO.userError "original lambda occurrence missing")
  let view := SourceCoreEvidence.withNode source {originalNode with type := .bool}
  SourceCompilerFeatureSupport.require (decide (source ≠ view)) "fixture did not change the parent metadata"
  checkOtherLookups source view originalNode.id
  SourceCompilerFeatureSupport.require (source.lookupExpression? originalNode.id != view.lookupExpression? originalNode.id)
    "changed parent was incorrectly included in the unchanged footprint"
  let request : SourceCoreSourceCells.Request :=
    ⟨source, site.key.scope, Renaming.insertion 2, parameter, site.key.payloadType, some (.var 1)⟩
  let allocate := prepared.layouts.allocatorAt lambda.owner lambda.active (fun error => .sourceAllocation (reprStr error))
  let old ← SourceCompilerFeatureSupport.get "original annotated allocation"
    (SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt prepared.ancestry.layout.frame automatic.prepared.globals.length allocate request)
  let new ← SourceCompilerFeatureSupport.get "view annotated allocation"
    (SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt prepared.ancestry.layout.frame automatic.prepared.globals.length allocate {request with source := view})
  SourceCompilerFeatureSupport.require (old.original == new.original && old.expression == new.expression)
    "local edit changed the real capture/payload/snapshot expression"
  let malformed := {request with payloadType := .unit}
  match allocate malformed, allocate {malformed with source := view} with
  | .error before, .error after =>
    SourceCompilerFeatureSupport.require (reprStr before == reprStr after) "metadata edit changed allocator rejection"
  | _, _ => throw (IO.userError "invalid payload type unexpectedly allocated")
  let changedForm := SourceCoreEvidence.withNode source {originalNode with form := .proxy .word}
  match allocate {request with source := changedForm} with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "altered source form bypassed allocation authentication")
  let binding ← match automatic.prepared.locals.bindings.find? (·.binder.name == "f") with
    | some binding => pure binding
    | none => throw (IO.userError "qualified local binding missing")
  let ids := binding.source.nodes.filterMap fun
    | .expression {id, form := .reference _ (.local binderId), ..} => if binderId == binding.binder.id then some id else none
    | _ => none
  SourceCompilerFeatureSupport.require (ids.length == 2) "qualified fixture lost either read occurrence"
  let mut accumulated := binding.source
  for id in ids do
    let view ← SourceCompilerFeatureSupport.get "qualified local normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none binding.source id)
    checkOtherLookups binding.source view id
    SourceCompilerFeatureSupport.require (binding.source.lookupExpression? id != view.lookupExpression? id)
      "qualified normalization did not change its owned requirements"
    let repeated ← SourceCompilerFeatureSupport.get "repeated qualified normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none view id)
    SourceCompilerFeatureSupport.require (view == repeated) "repeated normalization changed a stable source"
    let next ← SourceCompilerFeatureSupport.get "composed qualified normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none accumulated id)
    checkOtherLookups accumulated next id
    accumulated := next
  for id in ids do
    let normalized ← SourceCompilerFeatureSupport.get "original reference authentication"
      (SourceCoreLocalEvidence.authenticateReference program plan binding none id)
    SourceCompilerFeatureSupport.require (accumulated.lookupExpression? id == some normalized.normalized)
      "successive normalizations failed to retain either read's authenticated metadata"
  IO.println "lambda local metadata edits: disjoint lookups, exact snapshot allocation and qualified normalization GREEN"
end Tests.SourceCoreCallableLambdaViewEdits
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewIndexedTrees
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewIndexedTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionGeneral
open CallableLambdaViewEdits CallableLambdaBodyReachability
namespace ProductKey

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_index_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_index_view.solc"⟩, 0, 4⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def keyType : TypeSystem.Ty := .product .bool .bool
private def mappingType : TypeSystem.Ty := .mapping keyType .bool
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "table", .mono mappingType, [], false, none⟩
private def baseNode : ExpressionNode := { id := id 0, span, type := mappingType, form := .reference "table" (.local binder.id) }
private def trueNode : ExpressionNode := { id := id 1, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def falseNode : ExpressionNode := { id := id 2, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def keyNode : ExpressionNode := { id := id 3, span, type := keyType, form := .tuple [id 1, id 2] }
private def indexNode : ExpressionNode := { id := id 4, span, type := .bool, form := .index (id 0) (id 3) }
private def unaryNode : ExpressionNode := { id := id 5, span, type := .bool, form := .unary .logicalNot (id 4) }
private def parentNode : ExpressionNode := {id := id 6, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression (id 5)], nodes := [.expression baseNode, .expression trueNode, .expression falseNode, .expression keyNode, .expression indexNode, .expression unaryNode, .expression parentNode] }
private def context : SourceSemantics.Context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reason : Word := Word.ofNatModulo 17
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem metadata {expression : ExpressionId} {node : ExpressionNode} (found : source.lookupExpression? expression = some node) :
    node.requirements = CompatibleExpressionLiterals.owned node.form ∧ node.coercions = [] := by
  have member := (lookupExpression?_sound found).1
  simp only [source, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
private theorem boolAdmitted : TypeAdmissible context .bool :=
  .bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme)
private theorem keyAdmitted : TypeAdmissible context keyType := .product boolAdmitted boolAdmitted
private theorem mappingAdmitted : TypeAdmissible context mappingType := .mapping keyAdmitted boolAdmitted
private theorem baseTyped : ExpressionHasType source context (id 0) mappingType := by
  apply ExpressionHasType.ofOrdinary (node := baseNode) (rawType := mappingType) (lookupExpression?_sound (by rfl))
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) (SchemeWellFormed.monoAdmissible mappingAdmitted) []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply mappingType)
      (by simp) (by intro _ member; cases member) (.nil)))) mappingAdmitted mappingAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem trueTyped : ExpressionHasType source context (id 1) .bool := by
  apply ExpressionHasType.ofOrdinary (node := trueNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean true)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem falseTyped : ExpressionHasType source context (id 2) .bool := by
  apply ExpressionHasType.ofOrdinary (node := falseNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.reference (.builtinBoolean false)) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem keyTyped : ExpressionHasType source context (id 3) keyType := by
  apply ExpressionHasType.ofOrdinary (node := keyNode) (rawType := keyType)
    (lookupExpression?_sound (by cbv)) (.tuple (.cons trueTyped (.cons falseTyped (.nil _)))) keyAdmitted keyAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexTyped : ExpressionHasType source context (id 4) .bool := by
  apply ExpressionHasType.ofOrdinary (node := indexNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.index baseTyped keyTyped) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem unaryTyped : ExpressionHasType source context (id 5) .bool := by
  apply ExpressionHasType.ofOrdinary (node := unaryNode) (rawType := .bool)
    (lookupExpression?_sound (by cbv)) (.unary indexTyped .logicalNot) boolAdmitted boolAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem indexSyntax : CompatibleExpressionGeneral.Syntax source (id 4) :=
  .index (node := indexNode) (keyNode := keyNode) (by cbv) rfl (by cbv)
    (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read (node := baseNode) (by cbv) rfl)))))))
    (.pair (node := keyNode) (by cbv) rfl
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := trueNode) (by cbv) (.bool _ _))))))))
      (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := falseNode) (by cbv) (.bool _ _)))))))))
private theorem syntaxTree : CompatibleExpressionGeneral.Syntax source (id 5) :=
  .unary (node := unaryNode) (by cbv) rfl indexSyntax
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [mappingType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private theorem nativeExists : (checked.catalog.project mappingType).toOption.isSome = true := by cbv
private def nativeType := (checked.catalog.project mappingType).toOption.get nativeExists
private theorem projected : checked.catalog.project mappingType = .ok nativeType := by cbv
private def scope : SourceCoreLocalCell.Scope := [(binder.id, nativeType)]
private theorem declarations : CompatibleExpressionReads.ScopeDeclarations source scope context := by
  intro actual declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst actual
    have actual : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := by rfl
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected
private abbrev policy := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
private theorem certified {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  tree_of_functions unique declarations (by rfl) rfl rfl ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩
    (fun _ _ _ found => (metadata found).2) syntaxTree (by cbv) unaryTyped accepted

private def view := SourceCoreEvidence.withNode source {parentNode with type := .unit}
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parentNode.id] :=
  withNode unique (by rfl) rfl rfl
private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [baseNode, trueNode, falseNode, keyNode, indexNode, unaryNode,
      ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl <;> simp [footprint, id]
private theorem reached_member {node : NodeId} (reached : Reaches source source.roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression (id 5) := by simpa [source] using member
    rw [same]
    simp [footprint]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih
private theorem avoids : Avoids source source.roots [parentNode.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parentNode, footprint, id] at impossible

/-- The product-key comparator is retained exactly; no scalar-key premise is
introduced when transporting a successfully compiled general expression. -/
theorem accepted_product_key {code : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 5 compilation source scope (id 5) (fun _ => reason) = .ok code) :
    source ≠ view ∧ Tree 100 values view context [] (fun _ => reason) scope (id 5) code :=
  ⟨by decide, CallableLambdaViewIndexedTrees.general edited avoids (certified accepted) (.root (by simp [source]))⟩

theorem original_product_key {code : SourceCoreBasic.LoweredExpr}
    (tree : Tree 100 values view context [] (fun _ => reason) scope (id 5) code) :
    Tree 100 values source context [] (fun _ => reason) scope (id 5) code :=
  CallableLambdaViewIndexedTrees.general_original edited avoids tree (.root (by simp [source]))

theorem product_key_is_not_scalar : ¬ CompatibleExpressionIndices.SourceScalar keyType := by
  intro scalar
  cases scalar

end ProductKey

/-- Actual ordinary typed lowering at a view yields the canonical Tree under
reachability. Independent typing and syntax refer to that actual view; the
conclusion does not assert canonical compiler acceptance or canonical typing. -/
theorem typed_original_from_contextual
    {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    {values : SourceCoreCompatibleValues.Context} {readFuel : Nat} {context : SourceSemantics.Context}
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {compilation : SourceCoreFunctions.Context} {native : Option SourceCoreGeneralFunctions.CallableContext}
    {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {code : SourceCoreBasic.LoweredExpr}
    (ordinary : CompatibleExpressionTyped.Ordinary view locals compilation.owner) (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (signatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionTyped.Syntax view id) (found : view.lookupExpression? id = some node)
    (typed : ExpressionHasType view context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (reached : Reaches source roots (.expression id))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
      assignments diagnostics compilation native parent skip fuel view scope id reasonAt = .ok code) :
    CompatibleExpressionTyped.Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code :=
  CallableLambdaViewIndexedTrees.typed_original edited avoids
    (CompatibleExpressionTyped.tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
      readPolicy lowerPolicy leafPolicy accepted) reached

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function scalar() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); return !m[true]; }; }",
    "function product() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping((Bool, Bool) => Bool); return m[(true, false)] || !m[(false, true)]; }; }",
    "function skipped() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return true ? !m[false] : n[true]; }; }",
    "function before_fault() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(Bool => Bool); let missing: Bool; return m[false] || missing; }; }",
    "function no_default() returns (function() returns (Box<Word>)) { return lam() -> Box<Word> { let m: mapping(Bool => Box<Word>); return m[true]; }; }",
    "function proxy() returns (function() returns (Bool)) { return lam() -> Bool { let m: mapping(@Word => Bool); return m[@Word]; }; }"]}] }

private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (header : ExpressionNode)
    (name : String) (expression : ExpressionId) : IO Unit := do
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "index view binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "index view binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "index view empty mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .bool => pure (OptionalCell.allocate native, none)
      | other => throw (IO.userError s!"index view unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "index view diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := [], internalReason := Word.zero }
  let reasonAt := diagnostics.reasonAt owner
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let policy := SourceCoreCompatibleDataExpressions.functionPolicy 150 values
  let modified := SourceCoreEvidence.withNode source {header with type := .unit}
  let noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
  let before := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation source scope expression reasonAt
  let after := SourceCoreFunctions.lowerExpressionWithPolicy policy noBody 150 compilation modified scope expression reasonAt
  let lowered ← get s!"index view actual compiler {name}" before
  let same ← get s!"index view modified compiler {name}" after
  require (reprStr lowered == reprStr same) "index view changed accepted code/header/comparator"
  require (source != modified) "index view header was unchanged"
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  require native.check s!"index view {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      require (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "index view comparator changed ambient closure"
      if name == "before_fault" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "index view missing first fault")
        require (result == .inLeft lowered.type (.word (reasonAt failed.id))) "index view first fault changed"
      else if name == "no_default" then
        let indexed ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "index view indexed root missing")
        let .index base _ := indexed.form | throw (IO.userError "index view root is not index")
        let baseNode ← match source.lookupExpression? base with
          | some node => pure node | none => throw (IO.userError "index view mapping metadata missing")
        let .mapping key value := baseNode.type | throw (IO.userError "index view raw mapping type missing")
        let tag ← match values.registry.id? (.mapping key value) with
          | some tag => pure tag | none => throw (IO.userError "index view raw mapping header missing")
        require (result == .inLeft lowered.type (.word ((reasonAt expression).add tag))) "index view missing-default token changed"
      else
        require (result == .inRight .word (.bool (name != "proxy"))) "index view success changed"
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let expectedCell := match expected with
          | some value => if binder.name == "n" then Value.inLeft type .unit else .inRight .unit value
          | none => .inLeft type .unit
        require (store[bindings.length - position]? == some expectedCell)
          s!"index view {name} changed lazy initialization at {binder.name}"
    | other => throw (IO.userError s!"index view {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "index view checker" (checkProgram workspace)
  let requests := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"index view specialization: {reprStr other}")
  let automatic ← get "index view base factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let indexed ← get "index view indexed factory" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let source := template.context.inventory.source
    let .lambda _ _ statements := template.node.form | throw (IO.userError "index view lambda form missing")
    let expression ← match statements.findSome? fun id => match source.lookupStatement? id with
      | some node => match node.form with | .returnStmt (some expression) => some expression | _ => none
      | none => none with
      | some expression => pure expression | none => throw (IO.userError "index view lambda return missing")
    let name := (program.signatures.functions.find? (·.id == template.owner.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared source template.owner template.node name expression
    count := count + 1
  require (count == 6) s!"index view lambda cases missing: {count}"
  IO.println "lambda indexed views: scalar/product/proxy keys, exact comparator/default metadata, lazy effects, failures, typed hidden slot and resume GREEN"

end Tests.SourceCoreCallableLambdaViewIndexedTrees
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewScalarTrees
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewScalarTrees
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_scalar_view", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_scalar_view.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def boolean (index : Nat) (value : Bool) : ExpressionNode :=
  {id := id index, span, type := .bool, form := .reference "boolean" (.builtinBoolean value)}
private def negated : ExpressionNode := {id := id 2, span, type := .bool, form := .unary .logicalNot (id 0)}
private def binary : ExpressionNode := {id := id 3, span, type := .bool, form := .binary (id 2) .logicalOr (id 1)}
private def conditional : ExpressionNode := {id := id 4, span, type := .bool, form := .conditional (id 3) (id 0) (id 1)}
private def grouped : ExpressionNode := {id := id 5, span, type := .bool, form := .group (id 4)}
private def paired : ExpressionNode := {id := id 6, span, type := .product .bool .bool, form := .tuple [id 5, id 1]}
private def parent : ExpressionNode := {id := id 7, span, type := .function .unit .bool, form := .lambda [] .bool []}
private def source : TypedSource := {owner, inputs := [], roots := [.expression parent.id], nodes :=
  [.expression (boolean 0 true), .expression (boolean 1 false), .expression negated,
    .expression binary, .expression conditional, .expression grouped, .expression paired, .expression parent]}
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def roots : List NodeId := [.expression paired.id]
private def footprint : List NodeId := ([0, 1, 2, 3, 4, 5, 6] : List Nat).map (fun n => .expression (id n))
private theorem edited : LocalView source view [parent.id] :=
  withNode (by cbv; decide) (by rfl) rfl rfl

private theorem reference_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp only [footprint, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, NodeId.expression.injEq] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [boolean, negated, binary, conditional, grouped, paired, ExpressionForm.references,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id]

private theorem reached_member {node : NodeId} (reached : Reaches source roots node) : node ∈ footprint := by
  induction reached with
  | @root rootId member =>
    have same : rootId = NodeId.expression paired.id := by simpa [roots] using member
    rw [same]
    simp [footprint, paired, id]
  | expression _ found edge ih => exact reference_closed ih found edge
  | statement _ _ _ ih => simp [footprint] at ih

private theorem avoids : Avoids source roots [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [parent, footprint, id] at impossible

private def unaryCode := LocalPrimitiveResults.unary .boolNot (LanguageResult.success (.bool true))
private def binaryCode := SourceCorePrimitive.binary .logicalOr unaryCode (LanguageResult.success (.bool false))
private def conditionalCode := LocalControl.choose .bool binaryCode
  (LanguageResult.success (.bool true)) (LanguageResult.success (.bool false))
private def code : SourceCoreBasic.LoweredExpr :=
  ⟨.product .bool .bool, LocalSequence.pair .bool .bool conditionalCode (LanguageResult.success (.bool false))⟩

private theorem originalTree {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} :
    CompatibleExpressionConditionals.Tree 10 values source context [] (fun _ => Word.zero) [] paired.id code := by
  apply CompatibleExpressionConditionals.Tree.pair (node := paired) (leftNode := grouped)
    (rightNode := boolean 1 false) (first := ⟨.bool, conditionalCode⟩) (second := ⟨.bool, LanguageResult.success (.bool false)⟩)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl
  · apply CompatibleExpressionConditionals.Tree.group (node := grouped) (innerNode := conditional)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl
    apply CompatibleExpressionConditionals.Tree.conditional (node := conditional)
      (conditionNode := binary) (thenNode := boolean 0 true) (elseNode := boolean 1 false)
      ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl rfl
    · apply CompatibleExpressionConditionals.Tree.primitive
      apply CompatibleExpressionPrimitives.Tree.binary (node := binary) (leftNode := negated)
        (rightNode := boolean 1 false) (mode := .word)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl rfl .logicalOr
      · apply CompatibleExpressionPrimitives.Tree.unary (node := negated) (childNode := boolean 0 true)
          ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl .logicalNot
        exact .product (.literal ⟨boolean 0 true, rfl, .bool true rfl rfl rfl rfl⟩)
      · exact .product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩)
    · exact .primitive (.product (.literal ⟨boolean 0 true, rfl, .bool true rfl rfl rfl rfl⟩))
    · exact .primitive (.product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩))
  · exact .primitive (.product (.literal ⟨boolean 1 false, rfl, .bool false rfl rfl rfl rfl⟩))

/-- Real operator profiles and all three conditional children survive the
changed parent header. The complete sources remain different. -/
theorem scalar_view {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context} :
    source ≠ view ∧ CompatibleExpressionConditionals.Tree 10 values view context []
      (fun _ => Word.zero) [] paired.id code :=
  ⟨by decide, CallableLambdaViewScalarTrees.conditionals edited avoids originalTree (.root (by simp [roots]))⟩

theorem scalar_original {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    (tree : CompatibleExpressionConditionals.Tree 10 values view context [] (fun _ => Word.zero) [] paired.id code) :
    CompatibleExpressionConditionals.Tree 10 values source context [] (fun _ => Word.zero) [] paired.id code :=
  CallableLambdaViewScalarTrees.conditionals_original edited avoids tree (.root (by simp [roots]))

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() -> Word { let table: mapping(Word => Word); let missing: Word; @Word; false ? missing : table[1]; return ((!false && true) ? (seed + 2) : (seed * 3)); }; }"}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "scalar view checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "make") with
    | some signature => pure signature
    | none => throw (IO.userError "scalar view signature missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"scalar view worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "scalar view base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "scalar view indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let template ← match prepared.ancestry.templates.lambdas with
    | template :: _ => pure template
    | [] => throw (IO.userError "scalar view template missing")
  let statements ← match template.node.form with
    | .lambda [] _ statements => pure statements
    | _ => throw (IO.userError "scalar view lambda missing")
  let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
    | some caller => pure caller
    | none => throw (IO.userError "scalar view caller missing")
  let original := template.context.inventory.source
  let modified := SourceCoreEvidence.withNode original {template.node with type := .bool}
  let compilation : SourceCoreFunctions.Context := {
    plan, globals := automatic.prepared.globals, owner := template.owner, administrativePrefix := 1,
    solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
  let values := SourceCoreCompatibleValues.Context.initial automatic.checked
  let expressions := SourceCoreCompatibleDataExpressions.functionPolicy 100 values
  let mut scope : SourceCoreLocalCell.Scope := []
  for binder in SourceCoreDataPlaces.declaredBinders original do
    match values.checked.catalog.project binder.scheme.body with
    | .ok type => scope := (binder.id, type) :: scope
    | .error _ => pure ()
  let mut acceptedCount := 0
  let mut reads := 0
  let mut choices := 0
  let mut proxies := 0
  for node in original.nodes do
    match node with
    | .expression node =>
      if node.id != template.node.id then
        let before := SourceCoreFunctions.lowerExpressionWithPolicy expressions
          (fun _ _ _ _ _ _ _ _ _ => .ok .unit) 100 compilation original scope node.id (fun _ => Word.zero)
        let after := SourceCoreFunctions.lowerExpressionWithPolicy expressions
          (fun _ _ _ _ _ _ _ _ _ => .ok .unit) 100 compilation modified scope node.id (fun _ => Word.zero)
        SourceCompilerFeatureSupport.require (reprStr before == reprStr after) "view changed actual scalar lowering or diagnostic"
        match before with
        | .ok _ =>
          acceptedCount := acceptedCount + 1
          match node.form with
          | .reference _ (.local _) => reads := reads + 1
          | .conditional _ _ _ => choices := choices + 1
          | .proxy _ => proxies := proxies + 1
          | _ => pure ()
        | .error _ => pure ()
    | .statement _ => pure ()
  SourceCompilerFeatureSupport.require (!statements.isEmpty) "scalar view body missing"
  SourceCompilerFeatureSupport.require (acceptedCount ≥ 10 && reads ≥ 3 && choices ≥ 2 && proxies ≥ 1)
    "scalar view regression did not exercise accepted reads, choices and proxy"
  IO.println "lambda scalar views: static compound tree, raw read metadata and actual lowering equality GREEN"
end Tests.SourceCoreCallableLambdaViewScalarTrees
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewSemanticReceipt
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.BuiltinNamedBody.SemanticReceipt.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt.Receipt.mk
/-! Actual view compilation supplies a certificate; independent canonical
source traces and completed native runs consume its transported semantic
receipt. No canonical compiler equation or body meaning is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewSemanticReceipt
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatiblePayload GeneralHeap ReadOnly CompatibleExpressionBuiltins CallableIndexedHistory
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_view_semantics", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_view_semantics.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def returned : StatementNode := ⟨⟨⟨owner, 10⟩⟩, span, .word, .returnStmt (some (id 5))⟩
private def parent : ExpressionNode := {
  id := id 6, span, type := .function .unit .word,
  form := .lambda [] .word [returned.id]}
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement returned.id], nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .statement returned, .expression parent]}
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .integer]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreFunctions.Context := ⟨⟨[], [], [], []⟩, ⟨owner, []⟩, [], 0, [], Word.zero⟩
private def noBody : SourceCoreFunctions.BodyLowerer := fun _ _ _ _ _ _ _ _ _ => .ok .unit
private def reasonAt : ExpressionId → Word := fun _ => Word.zero
private def policy (native : SourceCoreGeneralFunctions.CallableContext) : SourceCoreFunctions.Policy :=
  {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private def view : TypedSource := SourceCoreEvidence.withNode source {parent with type := .unit}
private theorem edited : CallableLambdaViewEdits.LocalView source view [parent.id] :=
  CallableLambdaViewEdits.withNode unique (by cbv) rfl rfl
private def footprint : List NodeId := [.expression (id 0), .expression (id 1), .expression (id 2),
  .expression (id 3), .expression (id 4), .expression (id 5), .statement returned.id]
private theorem avoids : CallableLambdaBodyReachability.Avoids source [.statement returned.id] [parent.id] := by
  have subset {node : NodeId} (reached : CallableLambdaBodyReachability.Reaches source [.statement returned.id] node) :
      node ∈ footprint := by
    induction reached with
    | root member =>
      simp only [List.mem_singleton] at member
      subst_vars
      simp [footprint]
    | expression _ found edge ih =>
      simp [footprint] at ih
      rcases ih with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
        subst_vars
        simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode,
          ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
          rcases edge with rfl | rfl <;> simp [footprint, id]
    | statement _ found edge ih =>
      simp [footprint] at ih
      subst_vars
      have selected := Option.some.inj ((by rfl : source.lookupStatement? returned.id = some returned).symm.trans found)
      subst_vars
      simp [returned, StatementForm.references] at edge
      subst_vars
      simp [footprint]
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := subset reached
  simp [footprint, parent, id] at impossible
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax
private theorem noCoercions : ∀ expression node, view.lookupExpression? expression = some node → node.coercions = [] := by
  intro expression node found
  have member := (lookupExpression?_sound found).1
  have shape : view.nodes = [.expression literalNode, .expression toNode, .expression innerNode,
    .expression fromNode, .expression outerNode, .expression groupNode, .statement returned,
    .expression {parent with type := .unit}] := by rfl
  simp only [shape, List.mem_cons, List.not_mem_nil, or_false, Node.expression.injEq, reduceCtorEq, false_or] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private def functions (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful identities := ⟨fun impossible => False.elim impossible, fun impossible => False.elim impossible⟩
private theorem functionLeaves (ambient : AmbientDefinitions checked.catalog.definitions) : CompatibleEquality.FunctionObservations checked.catalog (functions ambient) identities := fun impossible => False.elim impossible
private theorem functionTypes (ambient : AmbientDefinitions checked.catalog.definitions) : FunctionRuntimeViews (functions ambient) := fun impossible => False.elim impossible
private def faults : FunctionCalls.FaultRep := fun reason token =>
  ((∃ location, reason = .uninitializedLocation location ∧ token = Word.zero) ∨
   (∃ key value tag, MetadataRep values.registry (.mapping key value) tag ∧ reason = .missingMappingDefault value ∧ token = Word.zero.add tag)) ∨
  ∃ code, reason = .panic code ∧ token = Solcore.Frontend.SourceCorePanics.reason code
/-- Every panic fails with its code's reason. -/
private instance : FunctionCalls.FaultTokens faults := ⟨fun code => .inr ⟨code, rfl, rfl⟩⟩
private theorem uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id) :=
  fun _ location => .inl (.inl ⟨location, rfl, rfl⟩)
private theorem missing : ∀ id key value tag, MetadataRep values.registry (.mapping key value) tag →
  faults (.missingMappingDefault value) ((reasonAt id).add tag) :=
  fun _ key value tag owned => .inl (.inr ⟨key, value, tag, owned, rfl, rfl⟩)
private theorem valid : CompatibleExpressionLiterals.ContextValid [] context [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, context, Context.ofSignatures]
  · intro requirement member; cases member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member; cases member
private theorem innerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 2) (.value (.integer 7)) ⟨[]⟩ :=
  BuiltinCalls.source_intro (checked := checked) (type := .integer) ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl
    (.apply (.cons (.intro (lookupExpression?_sound (node := literalNode) (by rfl))
      (.literal rfl (.word (numericLiteralValue?_sound (value := 7) (by rfl)))) .nil) .nil)
      (.value (.builtin (.wordToInteger (Word.ofNatModulo 7)))))
private theorem outerTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 4) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases innerTrace with
  | value evaluated =>
    exact BuiltinCalls.source_intro (checked := checked) (type := .word)
      ⟨by cbv, rfl, rfl, rfl, rfl⟩ rfl (.apply (.cons evaluated .nil) (.value (.builtin (.wordFromInteger 7))))
private theorem sourceTrace : Dynamic.ExpressionEvaluatesOutcome program context [] source [] ⟨[]⟩ (id 5) (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases outerTrace with
  | value evaluated => exact .value (.intro (lookupExpression?_sound (node := groupNode) (by cbv)) (.group rfl evaluated) .nil)

private def statements : List StatementId := [returned.id]
private theorem statementSyntax : BuiltinLexicalStatements.Syntax source context true statements .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private theorem viewSyntax : BuiltinLexicalStatements.Syntax view context true statements .word :=
  CallableLambdaViewSourceTyping.body_syntax edited avoids unique statementSyntax

private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def loopPolicy (native : SourceCoreGeneralFunctions.CallableContext)
    (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun fuel source scope id reasonAt => SourceCoreFunctions.lowerExpressionWithPolicy (policy native) noBody fuel compilation source scope id reasonAt
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

private theorem certified (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout} {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel view []
      statements .word reasonAt true Word.zero = .ok code) :
    BuiltinLexicalStatements.Tree layouts ⟨owner, []⟩ [] frame globals onError 100 values view [] reasonAt context [] true statements .word .word code := by
  apply GenericLexicalStatements.tree_of_flow rfl (by intros; rfl) rfl ?_ viewSyntax rfl rfl rfl
    (by intro actual declared index native selected; cases selected) rfl accepted
  intro current currentClosed currentResidual currentSignatures scope budget expression expressionNode lowered declarations syntaxValue found typed generated
  exact CompatibleExpressionBuiltins.tree_of_functions (edited.metadata.unique unique) declarations currentSignatures currentClosed currentResidual
    ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩ native [] rfl
    (fun _ _ _ found => noCoercions _ _ found) syntaxValue found typed generated

private theorem statementTrace : TypedScopedStatements.Executes true program context [] source [] ⟨[]⟩
    statements context (.returned (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases sourceTrace with
  | value child =>
    exact TypedScopedStatements.terminal_intro true [] (lookupStatement?_sound (node := returned) (by cbv))
      (by intro expression; simp [returned]) (.returnValue (lookupStatement?_sound (by cbv)) rfl child) (.returned _)

private def closure : Dynamic.Closure := ⟨[], .word, statements, source, [], context, []⟩
private theorem bodyTrace : FunctionCallBody.Trace program closure context [] ⟨[]⟩
    (.value (.word (Word.ofNatModulo 7))) ⟨[]⟩ := by
  cases statementTrace with
  | control executed => exact .returned executed

/-- The real finish/body traversal supplies the sealed static certificate.
The independent source trace is not a field of that certificate. -/
theorem accepted_view_certificate (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code) :
    Nonempty (BuiltinNamedBody.Certificate layouts ⟨owner, []⟩ [] frame globals onError 100 values view context []
      reasonAt [] statements .word .word (loopPolicy native layouts frame globals) fuel Word.zero Word.zero code) := by
  have original := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  cases generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt true Word.zero with
  | error error =>
    rw [generated] at accepted
    change (Except.error error : Except SourceCoreLoops.Error Expr) = .ok code at accepted
    cases accepted
  | ok flow =>
    simp [generated] at accepted
    cases accepted
    exact BuiltinNamedBody.of_tree original rfl viewSyntax rfl (certified native generated)

theorem accepted_view_preserves (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults (.value (.word (Word.ofNatModulo 7))) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld ⟨[]⟩ finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.SemanticReceipt.preserves (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) receipt.canonical environments heaps .nil agrees typed reference read unmapped bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, preserved⟩

/-- Whole finish completion constructs its independent source body trace.
Neither a native child evaluation nor a universal body meaning is assumed. -/
theorem accepted_view_reflects (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code)
    {mapping world administrative actualContext canonical actual store ξ contextLocation current value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) mapping world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) mapping world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame current))
    (unmapped : contextLocation ∉ mapping)
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program closure context [] ⟨[]⟩ outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked values.registry (functions ambient))
        finalMap finalWorld .word .word faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry (functions ambient) finalMap finalWorld after finalStore ∧
      AdministrativePreserved mapping store finalMap finalStore := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, preserved, metadata, reached⟩ :=
    BuiltinNamedBody.SemanticReceipt.reflects (function := closure) (values := values) (ambient := ambient) (registry := values.registry) (functions ambient) (.refl _) definitions registered program valid unique uninitialized missing
      faithful (functionLeaves ambient) (functionTypes ambient) receipt.canonical environments heaps .nil agrees typed reference read unmapped completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, preserved⟩


/-- The actual accepted equation is still at the changed view. -/
theorem actual_view_retained (native : SourceCoreGeneralFunctions.CallableContext)
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
      view [] statements .word reasonAt Word.zero Word.zero = .ok code) :
    source ≠ view ∧ ∃ receipt : CallableLambdaViewSemanticReceipt.Receipt layouts ⟨owner, []⟩ [] frame globals onError
      100 values source view context [] reasonAt [] statements .word .word (loopPolicy native layouts frame globals)
      fuel Word.zero Word.zero code,
      SourceCoreLoops.lowerStatementsWithPolicy (loopPolicy native layouts frame globals) fuel
        view [] statements .word reasonAt Word.zero Word.zero = .ok code ∧
      receipt.canonical.flow = receipt.actual.flow := by
  obtain ⟨actual⟩ := accepted_view_certificate native accepted
  let receipt := CallableLambdaViewSemanticReceipt.of_certificate (statements := statements) edited avoids unique actual
  exact ⟨by decide, receipt, receipt.accepted, receipt.sameFlow⟩

def run : IO Unit := do
  Tests.SourceCoreCallableLambdaViewBuiltinBodyTree.run
  IO.println "lambda view semantic receipts: canonical builtin body preservation/reflection retain actual view acceptance GREEN"

end Tests.SourceCoreCallableLambdaViewSemanticReceipt
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewSourceTyping
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewSourceTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability CompatibleExpressionBuiltins

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_view_source_typing", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_view_source_typing.solc"⟩, 0, 1⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def literalNode : ExpressionNode := {
  id := id 0, span, type := .word, form := .literal (.decimal "7")}
private def toNode : ExpressionNode := {
  id := id 1, span, type := BuiltinFunctionId.wordToInteger.type,
  form := .reference "wordToInteger" (.builtinFunction .wordToInteger)}
private def innerNode : ExpressionNode := {
  id := id 2, span, type := .integer, form := .call (id 1) [id 0] (.builtinFunction .wordToInteger)}
private def fromNode : ExpressionNode := {
  id := id 3, span, type := BuiltinFunctionId.wordFromInteger.type,
  form := .reference "wordFromInteger" (.builtinFunction .wordFromInteger)}
private def outerNode : ExpressionNode := {
  id := id 4, span, type := .word, form := .call (id 3) [id 2] (.builtinFunction .wordFromInteger)}
private def groupNode : ExpressionNode := {id := id 5, span, type := .word, form := .group (id 4)}
private def boolean : ExpressionNode := {id := id 7, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def discarded : StatementNode := ⟨⟨⟨owner, 10⟩⟩, span, .unit, .expression (id 5) true⟩
private def block : StatementNode := ⟨⟨⟨owner, 11⟩⟩, span, .unit, .block [discarded.id]⟩
private def returned : StatementNode := ⟨⟨⟨owner, 12⟩⟩, span, .word, .returnStmt (some (id 5))⟩
private def conditional : StatementNode := ⟨⟨⟨owner, 13⟩⟩, span, .unit, .ifThen boolean.id [returned.id] (some [returned.id])⟩
private def body : List StatementId := [block.id, conditional.id, returned.id]
private def parent : ExpressionNode := {id := id 6, span, type := .function .unit .word, form := .lambda [] .word body}
private def source : TypedSource := {
  owner, inputs := [], roots := body.map NodeId.statement, nodes := [.expression literalNode, .expression toNode,
    .expression innerNode, .expression fromNode, .expression outerNode, .expression groupNode, .expression boolean, .statement discarded, .statement block, .statement returned, .statement conditional, .expression parent]}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem wordAdmitted : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem integerAdmitted : TypeAdmissible context .integer := .integer (.ofSignatures signatures)
private theorem literalTyped : ExpressionHasType source context (id 0) .word := by
  apply ExpressionHasType.ofOrdinary (node := literalNode) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem innerTyped : ExpressionHasType source context (id 2) .integer := by
  apply ExpressionHasType.ofOrdinary (node := innerNode) (rawType := .integer) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := toNode) (by cbv)) rfl rfl rfl rfl)
      (.cons literalTyped (.nil _))) integerAdmitted integerAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem outerTyped : ExpressionHasType source context (id 4) .word := by
  apply ExpressionHasType.ofOrdinary (node := outerNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.builtinCall (.intro (lookupExpression?_sound (node := fromNode) (by cbv)) rfl rfl rfl rfl)
      (.cons innerTyped (.nil _))) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem groupTyped : ExpressionHasType source context (id 5) .word := by
  apply ExpressionHasType.ofOrdinary (node := groupNode) (rawType := .word) (lookupExpression?_sound (by cbv))
    (.group outerTyped) wordAdmitted wordAdmitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem literalSyntax : CompatibleExpressionGeneral.Syntax source (id 0) :=
  .fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := literalNode) (by rfl) (.word _)))))))
private theorem innerSyntax : Syntax source (id 2) :=
  .builtin (node := innerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact .fragment literalSyntax)
private theorem outerSyntax : Syntax source (id 4) :=
  .builtin (node := outerNode) (by cbv) rfl (by intro child member; simp only [List.mem_singleton] at member; subst child; exact innerSyntax)
private theorem syntaxTree : Syntax source (id 5) := .group (node := groupNode) (by cbv) rfl outerSyntax

private theorem booleanTyped : ExpressionHasType source context boolean.id .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by cbv))
    (.reference (.builtinBoolean true)) (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem booleanSyntax : CompatibleExpressionBuiltins.Syntax source boolean.id :=
  .fragment (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.literal (node := boolean) (by cbv) (.bool _ true))))))))
private theorem returnSyntax (mode : Bool) : BuiltinLexicalStatements.Syntax source context mode [returned.id] .word :=
  .returnValue (node := returned) [] (by cbv) rfl rfl (by cbv) rfl groupTyped syntaxTree
private theorem bodySyntax : BuiltinLexicalStatements.Syntax source context true body .word := by
  apply GenericLexicalStatements.Syntax.block (node := block) (by cbv) rfl rfl
  · exact .discard (node := discarded) (expressionNode := groupNode) (by cbv) rfl rfl rfl (by cbv)
      groupTyped syntaxTree (.nil (.inl rfl))
  · exact .ifThen (node := conditional) (conditionNode := boolean) (by cbv) rfl rfl (by cbv) rfl
      booleanTyped booleanSyntax (returnSyntax false) (returnSyntax false) (returnSyntax true)
private def view := SourceCoreEvidence.withNode source {parent with type := .unit}
private def footprint : List NodeId :=
  [.expression (id 0), .expression (id 1), .expression (id 2), .expression (id 3), .expression (id 4),
    .expression (id 5), .expression (id 7), .statement discarded.id, .statement block.id, .statement returned.id, .statement conditional.id]
private theorem edited : LocalView source view [parent.id] := withNode unique (by cbv) rfl rfl
private theorem expression_closed {expression : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression expression ∈ footprint) (found : source.lookupExpression? expression = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp only [literalNode, toNode, innerNode, fromNode, outerNode, groupNode, boolean,
      ExpressionForm.references, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at edge <;>
      rcases edge with rfl | rfl <;> simp [footprint, id]
private theorem statement_closed {statement : StatementId} {node : StatementNode}
    (member : NodeId.statement statement ∈ footprint) (found : source.lookupStatement? statement = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    have selected := Option.some.inj ((by rfl : source.lookupStatement? _ = some _).symm.trans found)
    subst node
    simp [discarded, block, returned, conditional, StatementForm.references] at edge <;>
      rcases edge with rfl | rfl | rfl <;> simp [footprint, id, discarded, block, returned, conditional, boolean]
private theorem reached_member {node : NodeId}
    (reached : Reaches source (body.map NodeId.statement) node) : node ∈ footprint := by
  induction reached with
  | root member =>
    simp only [body, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [footprint]
  | expression _ found edge ih => exact expression_closed ih found edge
  | statement _ found edge ih => exact statement_closed ih found edge
private theorem avoids : Avoids source (body.map NodeId.statement) [parent.id] := by
  intro expression member reached
  simp only [List.mem_singleton] at member
  subst expression
  have impossible := reached_member reached
  simp [footprint, parent, id] at impossible
private theorem groupReached : Reaches source (body.map NodeId.statement) (.expression groupNode.id) :=
  .statement (.root (by simp [body])) (by cbv : source.lookupStatement? returned.id = some returned)
    (by simp [returned, StatementForm.references, groupNode])

/-- The enclosing header really changes while independent nested builtin
source typing retains the exact Word result and all original metadata. -/
theorem independent_nested_view : source ≠ view ∧ ExpressionHasType view context groupNode.id .word :=
  ⟨by decide, CallableLambdaViewSourceTyping.expression_typing edited avoids unique syntaxTree groupReached groupTyped⟩

/-- Canonical typing is recovered from actual view typing, with no canonical
compiler success or source execution supplied to the transport. -/
theorem independent_nested_original : ExpressionHasType source context groupNode.id .word :=
  CallableLambdaViewSourceTyping.expression_typing_original edited avoids unique
    (CallableLambdaViewSourceTyping.expression_syntax edited avoids unique syntaxTree groupReached)
    groupReached independent_nested_view.2

theorem lexical_view : BuiltinLexicalStatements.Syntax view context true body .word :=
  CallableLambdaViewSourceTyping.body_syntax edited avoids unique bodySyntax

theorem lexical_original : BuiltinLexicalStatements.Syntax source context true body .word :=
  CallableLambdaViewSourceTyping.body_syntax_original edited avoids unique lexical_view

/-- Even a builtin callee has an actual reachability edge. Excluding only the
argument expression syntax is insufficient for this source-typing theorem. -/
theorem changed_callee_rejected : ¬Avoids source (body.map NodeId.statement) [toNode.id] := by
  intro fresh
  have outerReached : Reaches source (body.map NodeId.statement) (.expression outerNode.id) :=
    .expression (node := groupNode) groupReached (by cbv) (by simp [groupNode, ExpressionForm.references, outerNode, id])
  have innerReached : Reaches source (body.map NodeId.statement) (.expression innerNode.id) :=
    .expression (node := outerNode) outerReached (by cbv) (by simp [outerNode, ExpressionForm.references, innerNode, id])
  have calleeReached : Reaches source (body.map NodeId.statement) (.expression toNode.id) :=
    .expression (node := innerNode) innerReached (by cbv) (by simp [innerNode, ExpressionForm.references, toNode, id])
  exact fresh toNode.id (by simp) calleeReached

/-- A metadata view alone permits changed output metadata at a reached parent.
The freshness hypothesis is therefore a real source boundary. -/
theorem parent_reached_rejected : ¬Avoids source [.expression parent.id] [parent.id] :=
  fun fresh => fresh parent.id (by simp) (.root (by simp))

private def changedChild := SourceCoreEvidence.withNode source {groupNode with type := .bool}
private theorem childEdited : LocalView source changedChild [groupNode.id] :=
  withNode unique (by cbv) rfl rfl

/-- Preserved owner/forms/statement metadata cannot establish the original
source type at an edited, reached expression. Complete lookup equality is
strictly stronger than that metadata relation. -/
theorem metadata_alone_insufficient :
    LambdaMetadataViews.MetadataView source changedChild ∧
      ¬ExpressionHasType changedChild context groupNode.id .word := by
  refine ⟨childEdited.metadata, ?_⟩
  intro typed
  obtain ⟨selected, rawType, contains, output, _⟩ := typed.raw_type_and_output_path
  have found : changedChild.lookupExpression? groupNode.id = some {groupNode with type := .bool} := by rfl
  have same := Option.some.inj ((lookupExpression?_complete (childEdited.metadata.unique unique) contains).symm.trans found)
  subst selected
  cases output

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function nested() returns (integer) { let f: function() returns (integer) = lam() -> integer { let x: Word = 7; { integerEq(wordToInteger(x), wordToInteger(x)); } if (integerLt(wordToInteger(x), wordToInteger(x))) { return wordToInteger(x); } else { x; } return integerSub(wordToInteger(x), wordToInteger(3)); }; return 0; }",
    "function indexed() returns (integer) { let f: function() returns (Word) = lam() -> Word { let table: mapping((Bool, Bool) => Word); let spare: Word; { @Word; } if (integerEq(wordToInteger(2), wordToInteger(2))) { 3; } else { 4; } return table[(integerEq(wordToInteger(2), wordToInteger(2)), integerLt(wordToInteger(2), wordToInteger(2)))]; }; return 0; }",
    "function branch() returns (integer) { let f: function() returns (Bool) = lam() -> Bool { let x: Word = 3; if (integerEq(wordToInteger(x), wordToInteger(x))) { let y: Word = 7; y; } else { let y: Word; y; } return integerLt(wordToInteger(x), integerSub(wordToInteger(x), wordToInteger(1))); }; return 0; }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "source typing checker" (checkProgram workspace)
  let seeds := program.signatures.functions.map fun signature => ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program seeds 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"source typing worklist {reprStr result}")
  let base ← SourceCompilerFeatureSupport.get "source typing base" (SourceCoreCompatibleFunctions.prepare program plan 800)
  let prepared ← SourceCompilerFeatureSupport.get "source typing indexed" (SourceCoreCallableIndexedPrograms.prepare base.prepared 800)
  let native ← match base.prepared.callableContext with
    | some native => pure native | none => throw (IO.userError "source typing actual callable context missing")
  let mut bodies := 0
  for template in prepared.ancestry.templates.lambdas do
    let statements ← match template.node.form with
      | .lambda [] _ body => pure body | _ => throw (IO.userError "source typing lambda shape")
    let original := template.context.inventory.source
    let modified := SourceCoreEvidence.withNode original {template.node with type := .unit}
    let caller ← match plan.specializations.find? (fun caller => decide (caller.key = template.owner)) with
      | some caller => pure caller | none => throw (IO.userError "source typing caller missing")
    let compilation : SourceCoreFunctions.Context := {
      plan, globals := base.prepared.globals, owner := template.owner, administrativePrefix := 1,
      solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero}
    let values := SourceCoreCompatibleValues.Context.initial base.checked
    let expressions : SourceCoreFunctions.Policy :=
      {SourceCoreCompatibleDataExpressions.functionPolicy 100 values with
        callables := SourceCoreGeneralFunctions.callablePolicy (some native) []}
    let allocate := prepared.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
    let policy : SourceCoreLoops.Policy := {
      lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
        (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
      readStatement := SourceCoreCompatibleDataExpressions.readStatement values.checked
      lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder values.checked
      sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame
        base.prepared.globals.length allocate)}
    let before ← SourceCompilerFeatureSupport.get "source typing canonical body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy 400 original [] statements template.resultType
        (fun _ => Word.zero) Word.zero Word.zero)
    let after ← SourceCompilerFeatureSupport.get "source typing actual view body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy 400 modified [] statements template.resultType
        (fun _ => Word.zero) Word.zero Word.zero)
    SourceCompilerFeatureSupport.require (original != modified) "source typing header did not change"
    SourceCompilerFeatureSupport.require (before == after) "source typing view changed ordinary lexical/builtin code"
    SourceCompilerFeatureSupport.require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders modified)
      "source typing view changed exact local declarations"
    bodies := bodies + 1
  SourceCompilerFeatureSupport.require (bodies == 3) "source typing did not inspect all checked lambda bodies"
  IO.println "lambda source typing: independent nested builtin/lexical transport, changed-callee rejection, actual three body receipts GREEN"
end Tests.SourceCoreCallableLambdaViewSourceTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableLambdaViewStaticTyping
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewStaticTyping
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"lambda_full_static", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "lambda_full_static.solc"⟩, 0, 1⟩
private def eid (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def sid (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private def control : ControlContext := ⟨.word, 0⟩
private def word : ExpressionNode := {id := eid 0, span, type := .word, form := .literal (.decimal "7")}
private def boolean : ExpressionNode := {id := eid 1, span, type := .bool, form := .reference "false" (.builtinBoolean false)}
private def returned : StatementNode := {id := sid 10, span, type := .word, form := .returnStmt (some word.id)}
private def lambda : ExpressionNode := {id := eid 2, span, type := .function .unit .word, form := .lambda [] .word [returned.id]}
private def indirect : IndirectCallResolution := ⟨0, .unit, .unit, []⟩
private def called : ExpressionNode := {id := eid 3, span, type := .word, form := .call lambda.id [] (.indirect indirect)}
private def discarded : StatementNode := {id := sid 11, span, type := .unit, form := .expression called.id true}
private def breaking : StatementNode := {id := sid 12, span, type := .unit, form := .breakStmt}
private def continuing : StatementNode := {id := sid 13, span, type := .unit, form := .continueStmt}
private def whileNode : StatementNode := {id := sid 14, span, type := .unit, form := .whileLoop boolean.id [breaking.id]}
private def forNode : StatementNode := {
  id := sid 15
  span
  type := .unit
  form := .forLoop [.expression called.id] boolean.id [.expression word.id] [continuing.id]}
private def arm : TypedMatchCase := ⟨span, ⟨.wildcard span span, .word, .wildcard, []⟩, [returned.id]⟩
private def resolution : MatchResolution := ⟨word.id, ⟨owner, 0⟩, [arm], some [returned.id], []⟩
private def matched : StatementNode := {id := sid 16, span, type := .word, form := .matchWith resolution}
private def body : List StatementId := [discarded.id, whileNode.id, forNode.id, matched.id, returned.id]
private def cycle : ExpressionNode := {id := eid 98, span, type := .word, form := .group (eid 98)}
private def outer : ExpressionNode := {id := eid 99, span, type := .function .unit .word, form := .lambda [] .word body}
private def source : TypedSource := {
  owner
  inputs := []
  roots := body.map NodeId.statement
  nodes := [.expression word, .expression boolean, .expression lambda, .expression called,
    .statement returned, .statement discarded, .statement breaking, .statement continuing,
    .statement whileNode, .statement forNode, .statement matched, .expression cycle, .expression outer]}
private def view : TypedSource := SourceCoreEvidence.withNode source {outer with type := .bool}
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem edited : LocalView source view [outer.id] := withNode unique (by rfl) rfl rfl
private theorem wordAdmissible : TypeAdmissible context .word := .word (.ofSignatures signatures)
private theorem wordTyped : ExpressionHasType source context word.id .word := by
  apply ExpressionHasType.ofOrdinary (node := word) (rawType := .word) (lookupExpression?_sound (by rfl))
    (.literal (.intro (numericLiteralValue?_sound (value := 7) (by rfl)))) wordAdmissible wordAdmissible
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem boolTyped : ExpressionHasType source context boolean.id .bool := by
  apply ExpressionHasType.ofOrdinary (node := boolean) (rawType := .bool) (lookupExpression?_sound (by rfl))
    (.reference (.builtinBoolean false)) (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private def returnedFacts : StatementFacts := ⟨.word, true, true, .returned⟩
private def emptyFacts : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
private def breakFacts : StatementFacts := ⟨.unit, false, false, .breaking⟩
private def continueFacts : StatementFacts := ⟨.unit, false, false, .continuing⟩
private theorem returnedTyped : StatementHasType source control context returned.id context returnedFacts :=
  .returnValue (lookupStatement?_sound (node := returned) (by rfl)) rfl wordTyped rfl
private theorem lambdaTyped : ExpressionHasType source context lambda.id (.function .unit .word) := by
  have admitted : TypeAdmissible context (.function .unit .word) :=
    .function (.unit (.ofSignatures signatures)) wordAdmissible
  apply ExpressionHasType.ofOrdinary (node := lambda) (rawType := .function .unit .word) (lookupExpression?_sound (by rfl))
    (.lambda (by simp) (.nil _) (.singleton returnedTyped) (by unfold BodyCompletes; decide)) admitted admitted
  · intro requirement member; cases member
  · exact .nil _
  · rfl
private theorem calledTyped : ExpressionHasType source context called.id .word :=
  .intro (lookupExpression?_sound (node := called) (by rfl))
    (.indirectCall lambdaTyped (.nil _) (.intro rfl rfl rfl (.nil _))) rfl
    wordAdmissible wordAdmissible (.indirectCall (by intro id member; cases member) (.nil _) rfl)
private theorem discardedTyped : StatementHasType source control context discarded.id context emptyFacts :=
  .expressionDiscard (lookupStatement?_sound (node := discarded) (by rfl)) rfl calledTyped rfl
private theorem breakingTyped : StatementHasType source control.enterLoop context breaking.id context breakFacts :=
  .breakStmt (lookupStatement?_sound (node := breaking) (by rfl)) rfl (by change 0 < 1; decide) rfl
private theorem continuingTyped : StatementHasType source control.enterLoop context continuing.id context continueFacts :=
  .continueStmt (lookupStatement?_sound (node := continuing) (by rfl)) rfl (by change 0 < 1; decide) rfl
private def whileFacts : StatementFacts := ⟨.unit, false, false, .loop .breaking⟩
private def forFacts : StatementFacts := ⟨.unit, false, false, .loop .continuing⟩
private theorem whileTyped : StatementHasType source control context whileNode.id context whileFacts :=
  .whileLoop (lookupStatement?_sound (node := whileNode) (by rfl)) rfl boolTyped (.singleton breakingTyped) rfl
private theorem forTyped : StatementHasType source control context forNode.id context forFacts :=
  .forLoop (lookupStatement?_sound (node := forNode) (by rfl)) rfl
    (.cons (.expression calledTyped) (.nil _ _)) boolTyped (.singleton continuingTyped)
    (.cons (.expression wordTyped) (.nil _ _)) rfl
private theorem patternTyped : TypedMatchPatternHasType context arm.pattern .word [] 0 :=
  ⟨rfl, .wildcard, .wildcard, ⟨by simp, by simp⟩⟩
private theorem armTyped : MatchCaseHasType source control context .word arm (.singleton returnedFacts) :=
  .intro patternTyped (.nil _) (.singleton returnedTyped)
private theorem matchTyped : StatementHasType source control context matched.id context returnedFacts := by
  exact .matchWithDefault (show ContainsStatement source matched.id matched from lookupStatement?_sound (by rfl)) rfl rfl wordTyped
    (.cons armTyped (.nil _ _ _)) (.singleton returnedTyped) rfl (by rfl) rfl
private def bodyFacts : BodyFacts := .cons emptyFacts (.cons whileFacts (.cons forFacts
  (.cons returnedFacts (.singleton returnedFacts))))
private theorem bodyTyped : StatementsHaveType source control context body context bodyFacts :=
  .cons discardedTyped (.cons whileTyped (.cons forTyped (.cons matchTyped (.singleton returnedTyped))))

private def footprint : List NodeId := [.expression word.id, .expression boolean.id, .expression lambda.id, .expression called.id,
  .statement returned.id, .statement discarded.id, .statement breaking.id, .statement continuing.id,
  .statement whileNode.id, .statement forNode.id, .statement matched.id]
private theorem expression_closed {id : ExpressionId} {node : ExpressionNode}
    (member : NodeId.expression id ∈ footprint) (found : source.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    have same := Option.some.inj ((by rfl : source.lookupExpression? _ = some _).symm.trans found)
    subst node
    simp [word, boolean, lambda, called, ExpressionForm.references] at edge <;>
      subst child <;> simp [footprint, lambda, returned]
private theorem statement_closed {id : StatementId} {node : StatementNode}
    (member : NodeId.statement id ∈ footprint) (found : source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : child ∈ footprint := by
  simp [footprint] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    have same := Option.some.inj ((by rfl : source.lookupStatement? _ = some _).symm.trans found)
    subst node
    simp [returned, discarded, breaking, continuing, whileNode, forNode, matched, resolution, arm,
      StatementForm.references, MatchResolution.references, TypedMatchCase.references, ForItemForm.references] at edge <;>
      rcases edge with rfl | rfl | rfl | rfl <;> simp [footprint, returned, continuing, breaking]
private theorem reached_member {id : NodeId} (reached : Reaches source (body.map NodeId.statement) id) : id ∈ footprint := by
  induction reached with
  | root member =>
    simp [body] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [footprint]
  | expression _ found edge ih => exact expression_closed ih found edge
  | statement _ found edge ih => exact statement_closed ih found edge
private theorem avoids : Avoids source (body.map NodeId.statement) [outer.id] := by
  intro id member reached
  simp only [List.mem_singleton] at member
  subst id
  have impossible := reached_member reached
  simp [footprint, outer, word, boolean, lambda, called, eid] at impossible
private theorem calledReached : Reaches source (body.map NodeId.statement) (.expression called.id) :=
  .statement (.root (by simp [body])) (by rfl : source.lookupStatement? discarded.id = some discarded)
    (by simp [discarded, StatementForm.references])

/-- The occurrence table contains an actual cycle outside the retained body;
the transport does not assume a global acyclic source graph. -/
theorem unrelated_cycle : source.lookupExpression? cycle.id = some cycle ∧
    NodeId.expression cycle.id ∈ cycle.form.references := by
  exact ⟨rfl, by simp [cycle, ExpressionForm.references]⟩

/-- This body contains an indirect lambda call, while/break, for/continue and
match. No expression Syntax or static lowering Tree appears in the transport. -/
theorem full_body : source ≠ view ∧ StatementsHaveType view control context body context bodyFacts :=
  ⟨by decide, (CallableLambdaViewStaticTyping.body_iff edited avoids unique).mp bodyTyped⟩

theorem full_body_original : StatementsHaveType source control context body context bodyFacts :=
  (CallableLambdaViewStaticTyping.body_iff edited avoids unique).mpr full_body.2

theorem nested_lambda_call : ExpressionHasType view context called.id .word :=
  CallableLambdaViewStaticTyping.expression edited avoids unique calledTyped calledReached

theorem nested_lambda_call_original : ExpressionHasType source context called.id .word :=
  CallableLambdaViewStaticTyping.expression_original edited avoids unique nested_lambda_call calledReached

/-- The lambda body is part of the actual reference closure; changing its
returned expression is rejected even when the outer occurrence is unchanged. -/
theorem reached_lambda_body_rejected : ¬Avoids source (body.map NodeId.statement) [word.id] := by
  intro fresh
  have lambdaReached : Reaches source (body.map NodeId.statement) (.expression lambda.id) :=
    .expression calledReached (by rfl : source.lookupExpression? called.id = some called)
      (by simp [called, ExpressionForm.references])
  have returnReached : Reaches source (body.map NodeId.statement) (.statement returned.id) :=
    .expression lambdaReached (by rfl : source.lookupExpression? lambda.id = some lambda)
      (by simp [lambda, ExpressionForm.references])
  exact fresh word.id (by simp) (.statement returnReached (by rfl : source.lookupStatement? returned.id = some returned)
    (by simp [returned, StatementForm.references]))

/- Direct callee metadata and indexed assignment keys are transported under
source-static premises, retaining the exact instantiation and requirement plan. -/
theorem direct_call {canonical changedSource : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (localView : LocalView canonical changedSource changed) (fresh : Avoids canonical roots changed)
    (unique : NodeOccurrencesUnique canonical) {context : SourceSemantics.Context}
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    {parameters : List TypeSystem.Ty} {result : TypeSystem.Ty} {predicates : List ProgramPredicate}
    (calleeTyped : DirectDeclarationCalleeValid context canonical callee instantiation)
    (application : DeclarationApplicationValid context instantiation parameters result predicates)
    (argumentTypes : ExpressionsHaveTypes canonical context arguments parameters)
    (reached : CallableLambdaViewStaticTyping.Within canonical roots
      (ExpressionForm.call callee arguments (.declaration instantiation)).references) :
    ExpressionFormHasRawType changedSource context (.call callee arguments (.declaration instantiation)) result (.directCall predicates) :=
  CallableLambdaViewStaticTyping.form localView fresh unique (.directCall calleeTyped application argumentTypes) reached

theorem indexed_assignment {canonical changedSource : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    (localView : LocalView canonical changedSource changed) (fresh : Avoids canonical roots changed)
    (unique : NodeOccurrencesUnique canonical) {context : SourceSemantics.Context}
    {root : Resolved.LocalId} {key value : ExpressionId} {keyType valueType : TypeSystem.Ty}
    (rootTyped : WritableLocal context root (.mapping keyType valueType))
    (keyTyped : ExpressionHasType canonical context key keyType)
    (valueTyped : ExpressionHasType canonical context value valueType)
    (reached : CallableLambdaViewStaticTyping.Within canonical roots [.expression key, .expression value]) :
    SourceAssignmentHasType changedSource context ⟨⟨root, [.index key], valueType⟩, []⟩ .equal value := by
  apply CallableLambdaViewStaticTyping.assignment localView fresh unique
    (.equal (.intro rootTyped (.index keyTyped (.nil _)) rfl) valueTyped rfl)
  exact reached

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function identity(value: Word) returns (Word) { return value; }",
    "function mixed() returns (Word) { let fn: function() returns (Word) = lam() -> Word { let nested: function() returns (Word) = lam() -> Word { return identity(7); }; let table: mapping(Bool => Word); let count = 0; while (count < 2) { count += 1; if (count == 1) { continue; } table[false] = count; } for (let i = 0; i < 2; i += 1) { match (i) { case 0 { table[true] = nested(); } default { table[true] += 1; } } } return table[true] + table[false]; }; return fn(); }",
    "function failed() returns (Word) { let fn: function() returns (Word) = lam() -> Word { let seen: mapping(Bool => Word); seen[false]; let missing: Word; return missing; }; return fn(); }"
  ]}] }

/- This executable audit uses actual checked lambda inventory. It visits the
reference closure and compares full nodes, including raw metadata. It makes no
claim that metadata equality supplies a canonical compiler success equation. -/
private def auditView (original : TypedSource) (parent : ExpressionNode) : IO Unit := do
  let roots ← match parent.form with
    | .lambda _ _ statements => pure (statements.map NodeId.statement)
    | _ => throw (IO.userError "static view expected lambda inventory")
  let modified := SourceCoreEvidence.withNode original {parent with type := .bool}
  SourceCompilerFeatureSupport.require (original != modified) "static view did not change its enclosing header"
  let mut pending := roots
  let mut seen : List NodeId := []
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | next :: rest =>
      pending := rest
      if !(seen.contains next) then
        SourceCompilerFeatureSupport.require (next != .expression parent.id) "static view reached edited parent"
        let node ← match original.lookupNode? next.occurrenceId with
          | some node => pure node
          | none => throw (IO.userError "static view missing reached occurrence")
        SourceCompilerFeatureSupport.require (modified.lookupNode? next.occurrenceId == some node)
          "static view changed reached raw type/evidence/coercion or statement metadata"
        seen := next :: seen
        pending := node.references ++ pending
  SourceCompilerFeatureSupport.require (!seen.isEmpty) "static view empty test body"
  SourceCompilerFeatureSupport.require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders modified)
    "static view changed source binder metadata"

private def failureResume (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let complete ← entry.invoke []
  let token ← match complete.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "static typing fault fixture unexpectedly completed")
  SourceCompilerFeatureSupport.require (← complete.diagnostic token).isSome "static typing fault lost diagnostic"
  for fuel in [0, 10, 100] do
    let started ← SourceCompilerFeatureSupport.get "static typing suspension"
      (← complete.initial.run complete.key [] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel})
    let resumed ← match started with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match resumed, complete.outcome with
    | .failed actual heap, .failed expected final =>
      SourceCompilerFeatureSupport.require (actual == expected && heap.heapSize == final.heapSize)
        "static typing resume changed failure effects"
    | _, _ => throw (IO.userError "static typing resume changed outcome")

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "static typing checker" (checkProgram workspace)
  let mut inspected := 0
  for name in ["mixed", "failed"] do
    let entry ← SourceCompilerFeatureSupport.compileNamed checked name
    for template in entry.cached.indexed.ancestry.templates.lambdas do
      auditView template.context.inventory.source template.node
      inspected := inspected + 1
    if name == "mixed" then
      let expected := SourceCompilerFeatureSupport.scalar 10
      SourceCompilerFeatureSupport.require ((← entry.run []) == expected) "static typing nested call/loop/match result changed"
      for fuel in [0, 10, 100] do entry.checkResume [] expected fuel
    else failureResume entry
  SourceCompilerFeatureSupport.require (inspected == 3) "static typing did not audit every checked lambda"
  IO.println "lambda full source typing: all 13 judgments, nested/direct/indirect calls, loops/match/keys, exact metadata and resumed effects GREEN"

end Tests.SourceCoreCallableLambdaViewStaticTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableMethodBodyTraceBounds
/-! Actual method frames expose the original body child without declaring the
method an ordinary function. These are formal consumers; existing operator
runtime suites remain the execution regression tests. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableMethodBodyTraceBounds
open Frontend SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedCallBounds

abbrev fields_only := @body_trace_of_fields
abbrev ordinary_entry := @body_trace

section Actual
variable {program : Program} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {size : Nat} {types : List TypeSystem.Ty} {context : Context}
  {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

/-- Both allocation and the strict child come from this supplied derivation. -/
theorem actual_method
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < size :=
  body_trace_of_fields frame.source frame.context frame.parameters frame.result frame.roots extended arity executed

/-- The original input bound composes with the returned strict child; neither
source derivation is measured again. -/
theorem actual_method_below
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after)
    {budget : Nat} (within : size ≤ budget) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < budget := by
  obtain ⟨child, environment, bound, allocation, trace, smaller⟩ := actual_method frame extended arity executed
  exact ⟨child, environment, bound, allocation, trace, Nat.lt_of_lt_of_le smaller within⟩

/-- A nonempty dictionary and every heap cell retain their original indices. -/
theorem full_evidence_and_heap
    (frame : CallableCoercionMethodFrame.Frame body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧ child < size := by
  obtain ⟨child, environment, bound, allocation, trace, smaller⟩ := actual_method frame extended arity executed
  exact ⟨child, environment, bound, frame.parameters ▸ allocation, trace.sound, smaller⟩

/-- This consumer retains the old named signature and the same conclusion. -/
theorem actual_named {instantiation : SourceInference.DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (arity : function.parameters.length = arguments.length)
    (executed : BodyOutcome program size body function.evidence before arguments outcome after) :
    ∃ child environment bound,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      BodyTrace program child function context environment bound outcome after ∧ child < size :=
  body_trace frame extended arity executed
end Actual

section Boundaries
/-- Static body fields do not supply an ordinary declaration instantiation. -/
theorem method_frame_is_not_ordinary
    {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (_frame : CallableCoercionMethodFrame.Frame body function)
    (absent : ¬ Dynamic.FunctionInstantiates program instantiation body) :
    ¬ NamedCalls.SourceFrame program instantiation body function :=
  fun ordinary => absent ordinary.instantiated

/-- Arity is an independent prerequisite even for a real method frame. -/
theorem arity_fault_excluded
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {arguments : List Dynamic.Value}
    (frame : CallableCoercionMethodFrame.Frame body function)
    (arity : function.parameters.length = arguments.length) :
    ¬ body.source.inputs.length ≠ arguments.length := by
  simpa only [frame.parameters] using (not_not_intro arity)
end Boundaries
end Solcore.Test.SourceCoreCallableMethodBodyTraceBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableNamedCanonicalOrder
/-! The checker and specialization factory keep distinct ordered ledgers.
The actual two-parameter reference fixture requires the retained record, while
its compiler selection still matches the complete specialization metadata. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableNamedCanonicalOrder
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering TypeSystem
open CallableNamedCanonicalOrder

/-- Actual factory success and exact selector receipts suffice; no full metadata
equality or identical domain-order assumption is supplied by this consumer. -/
theorem retained_of_selected {signature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    (produced : SourceSpecialization.specializeFunction signature function supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) (next : Nat) (final : Substitution) (caller : ParameterSubstitution)
    (selected : SourceCompilationPlan.exactInstantiationKey plan (inferredInstantiation signature next final caller) = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized) :
    inferredInstantiation signature next final caller = retainedInstantiation specialized :=
  (CallableNamedMetadata.matches_of_exact selected record).retained_of_specialization produced unique next final caller

/-- The actual fresh allocator reverses two distinct declared parameters. -/
theorem two_parameter_order (scheme : ConstrainedDeclarationScheme) (first second : TypeParameterId)
    (parameters : scheme.parameters = [first, second]) (different : first ≠ second) (next : Nat) :
    (scheme.instantiate next).parameterSubstitution.map Prod.fst = [second, first] := by
  have unique : scheme.parameters.Nodup := by rw [parameters]; simp [different]
  simpa only [parameters, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_domain_reverse scheme next unique

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
    "function pairRef() returns (function(Word, Bool) returns (Word)) { return pair; }",
    "function callPair(a: Word, b: Bool) returns (Word) { return pair(a, b); }"]}]}

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "retained order checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "pair") with
    | some signature => pure signature | none => throw (IO.userError "missing generic pair signature")
  let referenceSignature ← match program.signatures.functions.find? (·.name == "pairRef") with
    | some signature => pure signature | none => throw (IO.userError "missing pair reference signature")
  let checked ← match program.functions.find? (fun function => function.declaration == referenceSignature.id) with
    | some function => pure function | none => throw (IO.userError "missing checked pair reference")
  let metadata ← match checked.typedBody.nodes.findSome? fun
    | .expression {form := .reference _ (.declaration metadata), ..} =>
        if metadata.declaration == signature.id then some metadata else none
    | _ => none with
    | some metadata => pure metadata | none => throw (IO.userError "missing retained generic reference")
  let entry ← SourceCompilerFeatureSupport.compileNamed program "pairRef"
  let selected ← SourceCompilerFeatureSupport.get "actual retained target" (SourceCompilationPlan.exactInstantiationKey entry.compiled.plan metadata)
  let record ← SourceCompilerFeatureSupport.get "actual specialization record" (SourceCompilationPlan.exactSpecialization entry.compiled.plan selected)
  SourceCompilerFeatureSupport.require (signature.scheme.parameters.length == 2) "fixture lost two declared parameters"
  SourceCompilerFeatureSupport.require (decide (metadata.parameterSubstitution.map Prod.fst = signature.scheme.parameters.reverse))
    "inference did not retain reverse declaration order"
  SourceCompilerFeatureSupport.require (decide (record.parameterSubstitution.map Prod.fst = signature.scheme.parameters))
    "specialization did not record declaration order"
  SourceCompilerFeatureSupport.require (decide (metadata = retainedInstantiation record))
    "retained record changed a metadata field beyond the authenticated ledger order"
  SourceCompilerFeatureSupport.require (decide (metadata ≠ CallableNamedMetadata.instantiation record))
    "source ledgers were silently identified by key selection"
  match ← entry.run [] with
  | .function _ => pure ()
  | _ => throw (IO.userError "retained reference did not return an owned function")
  let call ← SourceCompilerFeatureSupport.compileNamed program "callPair"
  let value : SourceCoreExecution.Value := .word (Word.ofNatModulo 37)
  SourceCompilerFeatureSupport.require ((← call.run [value, .bool true]) == value) "two-parameter direct call changed result"
  call.checkResume [value, .bool true] value
  IO.println "named canonical order: actual reverse source ledger, forward factory ledger and full metadata correspondence GREEN"
end Tests.SourceCoreCallableNamedCanonicalOrder
end
