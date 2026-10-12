import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! Body projection retains the exact lexical stopping context and heap.
Expression children use the existing recursive erasure theorem, including their
nested bodies. Stage rejection supplies no ordinary Dynamic outcome. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

theorem StatementsIn.body_plain {program : Program} {registry : Registry} {mode : Bool} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {outcome : BodyOutcome}
    (trace : StatementsIn program registry mode scope context environment before ids finalContext outcome after) :
    StatementsPlain program mode scope context environment before ids finalContext outcome after := by
  induction trace using StatementsIn.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun scope context environment before condition statements outcome after _ => WhilePlain program scope context environment before condition statements outcome after)
  all_goals try exact True.intro
  case nil => rename_i mode _ _ _; intro heap; cases mode <;> exact .nil
  case returnUnit contains form =>
    exact StatementsPlain.terminal contains (by intro expression; simp [form]) (.returnUnit contains form)
  case returnValue contains form child _ih =>
    exact StatementsPlain.terminal contains (by intro expression; simp [form])
      (.returnValue contains form child.value_plain)
  case returnFault contains form child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.returnValue contains form child.semanticFault_plain)
  case tail contains form child _ih =>
    exact .tailExpression contains form child.value_plain
  case discard contains form child _next _childIH tailIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.expression contains form child.value_plain) tailIH
  case discardValue contains form child _next _childIH tailIH =>
    exact StatementsPlain.discard_value contains form child.value_plain tailIH
  case ifConditionFault contains form test _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.ifCondition contains form test.semanticFault_plain)
  case ifReturned contains form test _branch _testIH branchIH =>
    exact StatementsPlain.terminal contains (by intro e; simp [form])
      (StatementsPlain.if_execute contains form test.value_plain branchIH)
  case ifFault contains form test _branch _testIH branchIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (StatementsPlain.if_fault contains form test.value_plain branchIH)
  case ifFallthrough contains form test _branch _next _testIH branchIH nextIH =>
    exact StatementsPlain.prepend contains (by intro e; simp [form])
      (StatementsPlain.if_execute contains form test.value_plain branchIH) nextIH
  case expressionFault contains form child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.expression contains form child.semanticFault_plain)
  case assignBare contains form snapshot child write _next _childIH nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.assignValue contains form (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignBareFault contains form snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.assignValue contains form
        (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case assignBareUnbound contains form _bare missing =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target (.unbound missing)))
  case assignBareDangling contains form _bare lookup missing =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target (.dangling lookup missing)))
  case letUninitialized contains form mono extension allocate _next ih =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.letUninitialized contains form mono extension allocate) ih
  case letInitialized contains form child mono extension allocate _next _childIH tailIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.letInitialized contains form child.value_plain mono extension allocate) tailIH
  case letFault contains form mono child _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.letInitializer contains form mono child.semanticFault_plain)

  case blockReturned contains form inner ih =>
    exact StatementsPlain.terminal contains (by intro e; simp [form]) (.block contains form ih)
  case blockFault contains form inner ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.block contains form ih)
  case blockFallthrough contains form inner next innerIH nextIH =>
    exact StatementsPlain.prepend contains (by intro e; simp [form]) (.block contains form innerIH) nextIH
  case whileReturned contains form loop ih =>
    exact StatementsPlain.terminal contains (by intro e; simp [form]) (.whileLoop contains form ih)
  case whileFault contains form loop ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.whileIteration contains form ih)
  case whileFallthrough contains form loop next loopIH nextIH =>
    exact StatementsPlain.prepend contains (by intro e; simp [form]) (.whileLoop contains form loopIH) nextIH
  case done test _ih => exact .done test.value_plain
  case conditionFault test _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .condition test.semanticFault_plain
  case returned test body _testIH bodyIH => exact .returns test.value_plain bodyIH
  case bodyFault test body _testIH bodyIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain bodyIH
  case next test body next _testIH bodyIH nextIH => exact WhilePlain.next test.value_plain bodyIH nextIH

/-- Loops retain their actual finite ordinary iterations, including nested calls. -/
theorem While.plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : BodyOutcome}
    (trace : While program registry scope context environment before condition statements outcome after) :
    WhilePlain program scope context environment before condition statements outcome after := by
  induction trace using While.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True)
  all_goals try exact True.intro
  case done test _ih => exact .done test.value_plain
  case conditionFault test _ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .condition test.semanticFault_plain
  case returned test body _testIH _bodyIH => exact .returns test.value_plain body.body_plain
  case bodyFault test body _testIH _bodyIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain body.body_plain
  case next test body next _testIH _bodyIH nextIH => exact WhilePlain.next test.value_plain body.body_plain nextIH

/-- A scoped arm retains the independent ordinary sequence and its actual heap. -/
theorem StatementsIn.returned_scoped {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {value : Value}
    (trace : StatementsIn program registry false scope context environment before ids finalContext (.returned value) after) :
    StatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.returned value) after := trace.body_plain

theorem StatementsIn.fallthrough_scoped {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : StatementsIn program registry false scope context environment before ids finalContext
      (.fallthrough finalEnvironment) after) :
    StatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.fallthrough finalEnvironment) after := trace.body_plain

theorem StatementsIn.semanticFault_scoped {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {reason : SemanticFault}
    (trace : StatementsIn program registry false scope context environment before ids finalContext
      (.fault (.semantic reason)) after) :
    StatementsFault program context scope.evidence scope.source environment before ids
      finalContext reason after := trace.body_plain

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
