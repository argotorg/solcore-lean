import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Primitive operators retain ordered recursive staged children. Actual
numeric validators authenticate only their own literal rows; operator methods
and output coercions remain separate rules. Runtime inspection audits checked
and specialized source metadata and the existing native compiler. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceRecursiveStagePrimitiveOperators
open Solcore Frontend SourceInference SourceSemantics Dynamic Staging.Recursive
open SourceSemantics.CoreLowering

section Numeric
variable {program : Program} {registry : Registry} {scope : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution} {solved : List SolvedRequirement}
  (contains : ContainsExpression scope.source id node) (form : node.form = .integerLiteral literal resolution)
  (sameLedger : context.solvedRequirements = solved) (runtime : RuntimeRequirementLedgerValid context)

include contains form sameLedger runtime

theorem word_leaf {validated : SourceCoreElaboration.WordIntegerLiteral}
    (accepted : SourceCoreElaboration.validateWordIntegerLiteral solved node literal resolution = .ok validated) :
    Expression program registry scope context environment heap id (.value (.word validated.value)) heap := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound accepted
  apply Expression.atomicValue contains (form ▸ AtomicForm.integerLiteral literal resolution) metadata.coercions
  simpa only [metadata.coercions] using
    NumericLiteralEvidenceReceipts.word_raw accepted form sameLedger runtime program scope.evidence scope.source environment heap

theorem integer_leaf {validated : SourceCoreElaboration.NativeIntegerLiteral}
    (accepted : SourceCoreElaboration.validateNativeIntegerLiteral solved node literal resolution = .ok validated) :
    Expression program registry scope context environment heap id (.value (.integer validated.value)) heap := by
  have metadata := SourceCoreElaboration.validateNativeIntegerLiteral_sound accepted
  apply Expression.atomicValue contains (form ▸ AtomicForm.integerLiteral literal resolution) metadata.coercions
  simpa only [metadata.coercions] using
    NumericLiteralEvidenceReceipts.integer_raw accepted form sameLedger runtime program scope.evidence scope.source environment heap
end Numeric

section Ordered
variable {program : Program} {registry : Registry} {scope origin : Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap} {id left right call : ExpressionId}
  {operator : Syntax.BinaryOp} {reason : Staging.CallGuard.Fault}

theorem word_add {a b : Core.Word} (occurrence : Occurrence scope id (.binary left .add right))
    (first : Expression program registry scope context environment before left (.value (.word a)) middle)
    (second : Expression program registry scope context environment middle right (.value (.word b)) after) :
    Expression program registry scope context environment before id (.value (.word (a.add b))) after ∧
      ExpressionEvaluates program context scope.evidence scope.source environment before id (.word (a.add b)) after := by
  have trace := Expression.binary occurrence first (.strict .add) second (.wordAdd a b)
  exact ⟨trace, trace.value_plain⟩

theorem integer_not {operand : ExpressionId} {a : Int} (occurrence : Occurrence scope id (.unary .bitNot operand))
    (child : Expression program registry scope context environment before operand (.value (.integer a)) after) :
    Expression program registry scope context environment before id (.value (.integer (~~~a))) after :=
  .unary occurrence child (.integerBitNot a)

theorem left_stage_fault (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.binaryLeftFault occurrence first
  exact ⟨trace, trace.stage_origin rfl⟩

theorem right_stage_fault {a : Dynamic.Value} (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.value a) middle)
    (continues : EvaluatesRightOperand operator a)
    (second : Expression program registry scope context environment middle right (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after ∧
      Generated origin call reason := by
  have trace := Expression.binaryRightFault occurrence first continues second
  exact ⟨trace, trace.stage_origin rfl⟩

theorem short_circuit_skips_failing_right (occurrence : Occurrence scope id (.binary left .logicalAnd right))
    (first : Expression program registry scope context environment before left (.value (.bool false)) middle)
    (hypothetical : Expression program registry scope context environment middle right (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.value (.bool false)) middle ∧
      Generated origin call reason :=
  ⟨.binaryShortCircuit occurrence first .andFalse, hypothetical.stage_origin rfl⟩

theorem unary_stage_fault {operand : ExpressionId} {op : Syntax.UnaryOp}
    (occurrence : Occurrence scope id (.unary op operand))
    (child : Expression program registry scope context environment before operand (.fault (.stage origin call reason)) after) :
    Expression program registry scope context environment before id (.fault (.stage origin call reason)) after :=
  .unaryOperandFault occurrence child

theorem semantic_invalid {a b : Dynamic.Value} (occurrence : Occurrence scope id (.binary left operator right))
    (first : Expression program registry scope context environment before left (.value a) middle)
    (continues : EvaluatesRightOperand operator a)
    (second : Expression program registry scope context environment middle right (.value b) after)
    (invalid : BinaryPrimitiveOperandsInvalid operator a b) :
    ExpressionFaults program context scope.evidence scope.source environment before id (.invalidBinaryOperands operator) after :=
  (Expression.binaryInvalid occurrence first continues second invalid).semanticFault_plain
end Ordered

section Boundaries
variable {scope : Scope} {id : ExpressionId} {node : ExpressionNode} {form : ExpressionForm}
  (unique : NodeOccurrencesUnique scope.source) (found : ContainsExpression scope.source id node)

include unique found

theorem required_operator_not_ordinary (required : node.requirements ≠ []) : ¬ Occurrence scope id form := by
  rintro ⟨other, contains, _, empty, _⟩
  have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans (lookupExpression?_complete unique contains))
  exact required (by simpa only [same] using empty)

theorem coerced_operator_not_ordinary (coerced : node.coercions ≠ []) : ¬ Occurrence scope id form := by
  rintro ⟨other, contains, _, _, empty⟩
  have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans (lookupExpression?_complete unique contains))
  exact coerced (by simpa only [same] using empty)
end Boundaries

private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def word (n : Nat) : SourceTypedRuntime.Value := .word (Core.Word.ofNatModulo n)
private def content := String.intercalate "\n" [
  "function arithmetic() returns (Word) { return 2 + 3 * 4; }",
  "function inverted() returns (Word) { return ~4; }",
  "function logic() returns (Bool) { return !false && true; }",
  "function skipped() returns (Bool) { let absent: Bool; return false && absent; }",
  "function firstFault() returns (Word) { let first: Word; let second: Word; return first + second; }",
  "function secondFault() returns (Word) { let first: Word = 9; let second: Word; return first + second; }"
]

private def audit (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let mut operators := 0
  let mut numbers := 0
  for named in compiled.indexed.base.functions do
    let exact ← get "full actual specialization" (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key)
    require (exact == named.specialized) "operator source full record changed"
    let source := exact.function.typedBody
    let ledger := exact.function.solvedRequirements
    for entry in source.nodes do
      match entry with
      | .expression node => match node.form with
        | .unary .. | .binary .. =>
          require (node.requirements.isEmpty && node.coercions.isEmpty) "primitive parent carries requirements/coercions"
          operators := operators + 1
        | .integerLiteral literal resolution =>
          require (node.requirements == [resolution.requirement]) "numeric child lost its owned requirement"
          let _ ← get "actual numeric validator" (SourceCoreElaboration.validateWordIntegerLiteral ledger node literal resolution)
          let selected := ledger.filter (·.id == resolution.requirement)
          require (selected.length == 1) "numeric selection is not the retained singleton"
          numbers := numbers + 1
        | _ => pure ()
      | _ => pure ()
  require (operators == 8 && numbers == 5) s!"unexpected primitive inventory {operators}/{numbers}"

/-- These are real checked-source layouts, before any staged evaluator can
materialize the operators. The generic method remains a distinct nonempty row. -/
private def checked_boundaries : IO Unit := do
  let sources := [
    "function numeric() returns (comptime<integer>) { return 5 + 6; }",
    "trait Add<T> { function add(left: T, right: T) returns (T); } " ++
      "function generic<T>(left: T, right: T) returns (T) where T: Add { return left + right; }"
  ]
  let mut integers := 0
  let mut methods := 0
  let mut literals := 0
  for source in sources do
    let checked ← get "checked integer/method operator boundaries" (checkProgram {
      entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := source}] })
    for function in checked.functions do
      for entry in function.typedBody.nodes do
        match entry with
        | .expression node => match node.form with
          | .binary _ .add _ =>
            if node.requirements.isEmpty then
              require (node.rawType == .integer && node.coercions.isEmpty) "primitive integer parent layout changed"
              integers := integers + 1
            else
              require (!node.requirements.isEmpty && node.coercions.isEmpty) "generic method layout changed"
              methods := methods + 1
          | .integerLiteral literal resolution =>
            require (resolution.targetType == .integer && node.requirements == [resolution.requirement]) "integer child ownership changed"
            let _ ← get "actual Integer validator" (SourceCoreElaboration.validateNativeIntegerLiteral function.solvedRequirements node literal resolution)
            literals := literals + 1
          | _ => pure ()
        | _ => pure ()
  require (integers == 1 && methods == 1 && literals == 2) s!"checked integer/method inventory {integers}/{methods}/{literals}"

private def cells (state : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit :=
  require (reprStr (state.heap.map fun cell => (cell.type, cell.value)) == reprStr expected) "ordered full heap changed"

def run : IO Unit := do
  let names := ["arithmetic", "inverted", "logic", "skipped", "firstFault", "secondFault"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive stage primitives" content names
  audit compiled
  checked_boundaries
  for fuel in [0, 1, 37, 300000] do
    for name in names do
      let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel
      let resumed ← get "primitive checkpoint resume" (first.resume 300000)
      match name, resumed.observation with
      | "arithmetic", .done value state => require (reprStr value == reprStr (word 14)) "arithmetic"; cells state []
      | "inverted", .done (.word value) state => require (value == (Core.Word.ofNatModulo 4).bitNot) "unary"; cells state []
      | "logic", .done (.bool true) state => cells state []
      | "skipped", .done (.bool false) state => cells state [(.bool, none)]
      | "firstFault", .fault (.uninitializedLocal binder) state
      | "secondFault", .fault (.uninitializedLocal binder) state =>
        let key ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram name
        let named ← match compiled.indexed.base.functions.filter (·.signature.key == key) with
          | [row] => pure row | _ => throw (IO.userError "actual fault root missing")
        let expected ← match (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter
          (·.name == if name == "firstFault" then "first" else "second") with
          | [binder] => pure binder.id | _ => throw (IO.userError "actual fault binder missing")
        require (binder == expected) "operand first fault identity changed"
        cells state [(.word, if name == "firstFault" then none else some (word 9)), (.word, none)]
      | _, other => throw (IO.userError s!"unexpected primitive outcome {name}: {reprStr other}")
  IO.println "recursive staged primitive operators: actual checked metadata / owned numeric rows / ordered native fault heaps / short circuit / resume GREEN"
end Tests.SourceRecursiveStagePrimitiveOperators
