import Solcore.SourceSemantics

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsFault

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic

/-- A structurally absent occurrence produces the public fault outcome. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ExpressionEvaluatesOutcome program context evidence source environment heap id
      (.fault (.missingExpression id)) heap :=
  .fault (.missing missing)

/-- An empty lexical frame gives a positive unbound-local derivation. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (heap : Heap) (binder : Resolved.LocalId) (name : String) :
    ExpressionFormFaults program context evidence source [] heap
      (.reference name (.local binder)) [] [] (.unboundLocal binder) heap := by
  exact .localUnbound rfl (.nil binder)

/-- A location past the empty heap is dangling without negating heap reads. -/
example (location : Location) : Heap.Dangling ⟨[]⟩ location := by
  exact .nil location.index

/-- Primitive operand faults name the exact source operator. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (heap : Heap) :
    UnaryOperationFaults program context evidence heap .logicalNot [] .unit
      (.invalidUnaryOperand .logicalNot) heap := by
  apply UnaryOperationFaults.primitive
  exact .logicalNot (by simp [BooleanValue])

/-- Non-callable values fault before any body can be postulated. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap (.bool true) []
      .notCallable heap := by
  exact .notCallable (by simp [CallableValue])

/-- Builtins expose their retained parameter count in arity faults. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) []
      (.argumentArityMismatch 2 0) heap := by
  apply CallableFaults.builtinArity
  decide

/-- Correct-arity builtin calls diagnose the first wrong argument type. -/
example (program : Program) (context : SourceSemantics.Context)
    (caller invocation : EvidenceEnvironment) (heap : Heap) :
    CallableFaults program context caller invocation heap
      (.builtin ⟨.integerAdd⟩) [.bool true, .integer 0]
      (.typeMismatch .integer .bool) heap := by
  apply CallableFaults.builtinArgumentType
  · decide
  · apply ValuesFirstTypeMismatch.head (.bool true)
    decide

/-- Missing retained evidence names the exact unsatisfied requirement. -/
example (context : SourceSemantics.Context) (evidence : EvidenceEnvironment)
    (id : RequirementId) (missing : RequirementMissing context id) :
    RequirementUnavailable context evidence id :=
  .missing missing

/-- A malformed pattern is an explicit metadata fault, not a failed match. -/
example (context : SourceSemantics.Context) (value : Value)
    (arm : TypedMatchCase) (rest : List TypedMatchCase)
    (malformed : PatternMalformed context arm.pattern) :
    MatchCasesPatternFault context value (arm :: rest) :=
  .head malformed

/-- The closed Core-representable residualization boundary is the sole
staging-fault introduction rule. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (before after : Heap) (id : ExpressionId)
    (value : Int)
    (evaluates : ExpressionEvaluates program context evidence source environment
      before id (.integer value) after) :
    RuntimeExpressionEvaluatesOutcome program context evidence source environment
      before id (.fault .stagingViolation) after :=
  .stagingViolation evaluates (.integer value)

/-- Grouping preserves the exact child fault and its heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (inner : ExpressionId)
    (missing : ExpressionMissing source inner) :
    ExpressionFormFaults program context evidence source environment heap
      (.group inner) [] [] (.missingExpression inner) heap := by
  exact ExpressionFormFaults.group (coercions := []) rfl (.missing missing)

/-- Statement faults are reified as `ControlOutcome.fault`. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : StatementId)
    (missing : StatementMissing source id) :
    StatementExecutesOutcome program context evidence source environment heap id
      context (.fault (.missingStatement id)) heap :=
  .fault (.missing missing)

/-- A `for`-header vector stops at its first faulting item and preserves that
item's exact fault and heap. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    ForItemsFault program context evidence source environment heap
      [.expression id] context (.missingExpression id) heap := by
  exact .head (.expression (.missing missing))

/-- Loop-condition failure is observable before any body iteration. -/
example (program : Program) (context : SourceSemantics.Context)
    (evidence : EvidenceEnvironment) (source : TypedSource)
    (environment : Environment) (heap : Heap) (id : ExpressionId)
    (missing : ExpressionMissing source id) :
    WhileFaults program context evidence source environment heap id []
      (.missingExpression id) heap := by
  exact .condition (.missing missing)

end Solcore.Test.SourceSemanticsFault
