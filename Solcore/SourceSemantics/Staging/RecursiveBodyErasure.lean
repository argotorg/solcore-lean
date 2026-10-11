import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! Body projection retains the exact lexical stopping context and heap.
Expression children use the existing recursive erasure theorem, including their
nested bodies. Stage rejection supplies no ordinary Dynamic outcome. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

private def BodyPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (ids : List StatementId) (finalContext : Context)
    (outcome : BodyOutcome) (after : Heap) : Prop :=
  match outcome with
  | .fallthrough finalEnvironment => FunctionStatementsExecute program context scope.evidence scope.source
      environment before ids finalContext (.fallthrough finalEnvironment) after
  | .returned value => FunctionStatementsExecute program context scope.evidence scope.source
      environment before ids finalContext (.returned value) after
  | .fault (.semantic reason) => FunctionStatementsFault program context scope.evidence scope.source
      environment before ids finalContext reason after
  | .fault (.stage ..) => True

private theorem prepend_body {program : Program} {scope : Scope} {context middleContext finalContext : Context}
    {environment middleEnvironment : Environment} {before middle after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {outcome : BodyOutcome}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id
      middleContext (.fallthrough middleEnvironment) middle)
    (tail : BodyPlain program scope middleContext middleEnvironment middle rest finalContext outcome after) :
    BodyPlain program scope context environment before (id :: rest) finalContext outcome after := by
  cases outcome with
  | fault failure =>
    cases failure with
    | stage => trivial
    | semantic =>
      cases rest with
      | nil => cases tail
      | cons => exact .tail head tail
  | fallthrough =>
    cases rest with
    | nil => cases tail; exact .singleton contains notTail head
    | cons => exact .cons head tail
  | returned =>
    cases rest with
    | nil => cases tail
    | cons => exact .cons head tail

private theorem terminal_body {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {value : Value}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id
      context (.returned value) after) :
    BodyPlain program scope context environment before (id :: rest) context (.returned value) after := by
  cases rest with
  | nil => exact .singleton contains notTail head
  | cons => exact .terminal head (.returned _)

private theorem fault_body {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {rest : List StatementId}
    {reason : SemanticFault}
    (head : StatementFaults program context scope.evidence scope.source environment before id reason after) :
    BodyPlain program scope context environment before (id :: rest) context (.fault (.semantic reason)) after := by
  cases rest with
  | nil => exact .singleton head
  | cons => exact .head head

private theorem Statements.body_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {outcome : BodyOutcome}
    (trace : Statements program registry scope context environment before ids finalContext outcome after) :
    BodyPlain program scope context environment before ids finalContext outcome after := by
  induction trace using Statements.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
  all_goals try exact True.intro
  case nil => exact FunctionStatementsExecute.nil
  case returnUnit contains form =>
    exact terminal_body contains (by intro expression; simp [form]) (.returnUnit contains form)
  case returnValue contains form child _ih =>
    exact terminal_body contains (by intro expression; simp [form])
      (.returnValue contains form child.value_plain)
  case returnFault contains form child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_body (.returnValue contains form child.semanticFault_plain)
  case tail contains form child _ih =>
    exact .tailExpression contains form child.value_plain
  case discard contains form child _next _childIH tailIH =>
    exact prepend_body contains (by intro expression; simp [form])
      (.expression contains form child.value_plain) tailIH
  case expressionFault contains form child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_body (.expression contains form child.semanticFault_plain)
  case letUninitialized contains form mono extension allocate _next ih =>
    exact prepend_body contains (by intro expression; simp [form])
      (.letUninitialized contains form mono extension allocate) ih
  case letInitialized contains form child mono extension allocate _next _childIH tailIH =>
    exact prepend_body contains (by intro expression; simp [form])
      (.letInitialized contains form child.value_plain mono extension allocate) tailIH
  case letFault contains form mono child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_body (.letInitializer contains form mono child.semanticFault_plain)

/-- Returned staged bodies retain their complete ordinary function trace. -/
theorem Statements.returned_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {value : Value}
    (trace : Statements program registry scope context environment before ids finalContext (.returned value) after) :
    FunctionStatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.returned value) after := trace.body_plain

/-- Ordinary fallthrough keeps the same final lexical environment. -/
theorem Statements.fallthrough_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : Statements program registry scope context environment before ids finalContext
      (.fallthrough finalEnvironment) after) :
    FunctionStatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.fallthrough finalEnvironment) after := trace.body_plain

/-- A semantic fault keeps its actual reason, stopping context and prefix heap. -/
theorem Statements.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {reason : SemanticFault}
    (trace : Statements program registry scope context environment before ids finalContext
      (.fault (.semantic reason)) after) :
    FunctionStatementsFault program context scope.evidence scope.source environment before ids
      finalContext reason after := trace.body_plain

end Solcore.SourceSemantics.Staging.Recursive
