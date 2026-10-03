import Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Terminal source fragments retain the actual non-Unit node annotations and
the compiler's emitted dead suffix. Formal consumers close concrete native
terminal heads. Runtime checks use checked source and the actual contextual
lowerer, including dead suffixes, fault prefixes and public checkpoint resume.
The existing Tree/Syntax integration remains a separate change. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false

namespace Tests.SourceCoreReachableStatementContinuations
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open ReachableStatementContinuations CoreProof

section Formal
variable {source : TypedSource} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {condition : ExpressionId} {leftSummary rightSummary : ControlSummary}
  {program : SourceSemantics.Program} {context finalContext : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ControlOutcome}

theorem actual_terminal_if (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary)
    (rightStops : StoppingStatements source right rightSummary)
    (trace : ScalarStatementViews.ListExecutes mode program context evidence source environment before
      (id :: rest) finalContext outcome after) :
    Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after ∧
      Dynamic.TerminalControl outcome :=
  source_stopped_head mode unique (.conditional found form leftStops rightStops) trace

theorem actual_terminal_block_fault {summary : ControlSummary} {reason : Dynamic.SemanticFault}
    (mode : Bool) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block left)
    (stops : StoppingStatements source left summary)
    (trace : ScalarStatementViews.ListFaults mode program context evidence source environment before
      (id :: rest) finalContext reason after) :
    finalContext = context ∧ Dynamic.StatementFaults program context evidence source environment before id reason after :=
  source_stopped_fault mode unique (.block found form stops) trace

theorem terminal_if_issued {policy : SourceCoreLoops.Policy} {fuel : Nat} {scope : SourceCoreLoops.Scope}
    {type readType : Core.Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {code : Expr}
    (read : policy.readStatement source id = .ok (node, readType))
    (form : node.form = .ifThen condition left (some right))
    (leftStops : StoppingStatements source left leftSummary)
    (rightStops : StoppingStatements source right rightSummary)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope (id :: rest)
      type reasonAt mode escaped = .ok code) :
    leftSummary.fallthrough = none ∧ rightSummary.fallthrough = none ∧
      ∃ lowered leftCode rightCode suffix,
        policy.lowerExpression fuel source scope condition reasonAt = .ok lowered ∧
        SourceCoreBasic.ensureType (.occurrence id.occurrence) .bool lowered.type = .ok () ∧
        Issued policy fuel source scope left type reasonAt false escaped leftCode ∧
        Issued policy fuel source scope right type reasonAt false escaped rightCode ∧
        Issued policy fuel source scope rest type reasonAt mode escaped suffix ∧
        code = LocalLoop.sequence type (LocalLoop.conditional type lowered.expression leftCode rightCode) suffix :=
  ⟨leftStops.no_fallthrough, rightStops.no_fallthrough, conditional_issued read form accepted⟩

/-- A reachable nil tail remains restricted in the old grammar. -/
theorem old_nil_nonunit {expected : TypeSystem.Ty} {expressionSyntax : ExpressionId → Prop}
    (nonunit : expected ≠ .unit) :
    ¬ GenericLexicalStatements.Syntax source expressionSyntax context true [] expected := by
  intro syntaxTree
  cases syntaxTree with
  | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_terminal_nil (summary : ControlSummary) : ¬ StoppingStatements source [] summary := by
  intro stops
  exact stops.nonempty rfl

theorem no_terminal_one_branch (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left none) (summary : ControlSummary) :
    ¬ StoppingStatement source id summary := by
  have shape : ∀ actual, source.lookupStatement? id = some actual →
      actual.form = .ifThen condition left none := by
    intro actual actualFound
    have same : actual = node := Option.some.inj (actualFound.symm.trans found)
    exact same ▸ form
  intro stops
  cases stops <;> have actualForm := shape _ (by assumption) <;> simp_all
end Formal

/-- The stopping obligation is discharged by this concrete native return,
not by an input law about a runtime body. The child is the original witness. -/
theorem concrete_return_stops {size : Nat} {native : Core.Environment} {initial final : Store}
    {suffix : Expr} {result : Value} (value : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence .word (LocalLoop.returned (.word value)) suffix) result final) :
    result = LocalLoop.returnedValue (.word value) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LocalLoop.returned (.word value)) result final := by
  have head : Evaluates native initial (LocalLoop.returned (.word value)) (LocalLoop.returnedValue (.word value)) initial :=
    LocalLoop.returned_evaluates .word
  obtain ⟨child, smaller, actual, _⟩ := native_sequence_stopped original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ NativeTerminal.returned (.word value))
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

theorem concrete_fault_stops {size : Nat} {native : Core.Environment} {initial final : Store}
    {type : Core.Ty} {suffix : Expr} {result : Value} (reason : Word)
    (original : EvaluationSize size native initial
      (LocalLoop.sequence type (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) suffix) result final) :
    result = .inLeft (LocalLoop.controlType type) (.word reason) ∧ final = initial ∧
      ∃ child, child < size ∧ EvaluationSize child native initial
        (LanguageResult.failure (LocalLoop.controlType type) (.word reason)) result final := by
  have head : Evaluates native initial (LanguageResult.failure (LocalLoop.controlType type) (.word reason))
      (.inLeft (LocalLoop.controlType type) (.word reason)) initial := .inLeft .word
  obtain ⟨child, smaller, actual, _⟩ := native_sequence_stopped original (by
    intro child middle result _ actual
    obtain ⟨same, _⟩ := evaluation_deterministic actual.sound head
    exact same ▸ NativeTerminal.failure reason)
  obtain ⟨same, storeEq⟩ := evaluation_deterministic actual.sound head
  exact ⟨same, storeEq, child, smaller, actual⟩

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function block() returns (Word) { { return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { return saved; } else { return 17; } } }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { return 29; } else { return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { let gap: Word; return gap; } else { return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable continuations missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable continuations parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable continuations missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable continuations actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable continuations actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable continuations actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable continuations changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable continuations root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable continuations actual statement read" (policy.readStatement source id)
            let condition ← get "reachable continuations actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable continuations actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable continuations actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable continuations emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable continuations whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable continuations did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 6 && reachableAnnotations == 1 && deadSuffixes == 1)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable continuations public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable statement continuations" content
    ["both", "block", "nested", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, []),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable continuations full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable continuations result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable continuations ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable continuations expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable continuations full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable continuations fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable continuations expected head fault: {reprStr other}")
  IO.println "reachable statement continuations: actual non-Unit annotations, source stops, original native child, emitted dead suffix and full source heaps/public resume GREEN"

end Tests.SourceCoreReachableStatementContinuations
