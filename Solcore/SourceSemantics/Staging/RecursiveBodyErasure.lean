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
    (motive_6 := fun scope context environment before resolution outcome after _ => MatchPlain program scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ForItemsPlain program scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ForLoopPlain program scope context environment before condition post body outcome after)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
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

  case matchReturned contains form matched ih =>
    exact StatementsPlain.terminal contains (by intro e; simp [form]) (ih _ _ contains form)
  case matchFault contains form matched ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (ih _ _ contains form)
  case matchFallthrough contains form matched next matchIH nextIH =>
    exact StatementsPlain.prepend contains (by intro e; simp [form]) (matchIH _ _ contains form) nextIH
  case scrutineeFault scrutinee ih =>
    rename_i failure
    intro id node contains form
    cases failure with
    | stage => trivial
    | semantic => exact .matchScrutinee contains form scrutinee.semanticFault_plain
  case patternFault contains scrutinee allocated invalid ih =>
    intro id node found form
    exact .matchPattern found form contains scrutinee.value_plain allocated invalid
  case arm contains scrutinee hidden selected extended allocated body scrutineeIH bodyIH =>
    exact MatchPlain.arm contains scrutinee.value_plain hidden selected extended allocated bodyIH
  case default contains scrutinee hidden selected body scrutineeIH bodyIH =>
    exact MatchPlain.default contains scrutinee.value_plain hidden selected bodyIH
  case noBranch contains scrutinee hidden selected ih =>
    intro id node found form
    exact .matchNoBranch found form contains scrutinee.value_plain hidden selected

  case forInitializerFault contains form initial initialIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.forInitializer contains form initialIH)
  case forReturned contains form initial loop initialIH loopIH =>
    exact StatementsPlain.terminal contains (by intro expression; simp [form]) (.forLoop contains form initialIH loopIH)
  case forFault contains form initial loop initialIH loopIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.forIteration contains form initialIH loopIH)
  case forFallthrough contains form initial loop next initialIH loopIH nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form]) (.forLoop contains form initialIH loopIH) nextIH
  case empty => exact .nil
  case absent mono extended allocated next nextIH =>
    exact ForItemsPlain.prepend (.letUninitialized mono extended allocated) nextIH
  case initialized mono extended child allocated next _childIH nextIH =>
    exact ForItemsPlain.prepend (.letInitialized child.value_plain mono extended allocated) nextIH
  case initializerFault mono child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.letInitializer mono child.semanticFault_plain)
  case expression child next _childIH nextIH => exact ForItemsPlain.prepend (.expression child.value_plain) nextIH
  case expressionFailure child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.expression child.semanticFault_plain)
  case assignment snapshot child write next _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignmentFailure snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case unbound _bare missing => exact .head (.assignValue (.target (.unbound missing)))
  case dangling _bare lookup missing => exact .head (.assignValue (.target (.dangling lookup missing)))
  case testFault test _testIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .condition test.semanticFault_plain
  case finished test _testIH => exact .done test.value_plain
  case bodyFailure test branch _testIH branchIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain branchIH
  case returnedFromBody test branch _testIH branchIH => exact .returns test.value_plain branchIH
  case postFailure test branch postTrace _testIH branchIH postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postFallthrough test.value_plain branchIH postIH
  case iterate test branch postTrace next _testIH branchIH postIH nextIH =>
    exact ForLoopPlain.next test.value_plain branchIH postIH nextIH

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
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
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

/-- Match erasure retains its actual selected arm and allocation prefix. -/
theorem Match.plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {resolution : MatchResolution} {outcome : BodyOutcome}
    (trace : Match program registry scope context environment before resolution outcome after) :
    MatchPlain program scope context environment before resolution outcome after := by
  cases trace with
  | scrutineeFault scrutinee =>
      rename_i failure
      intro id node contains form
      cases failure with
      | stage => trivial
      | semantic => exact .matchScrutinee contains form scrutinee.semanticFault_plain
  | patternFault contains scrutinee allocated invalid =>
      intro id node found form
      exact .matchPattern found form contains scrutinee.value_plain allocated invalid
  | arm contains scrutinee hidden selected extended allocated body =>
      exact MatchPlain.arm contains scrutinee.value_plain hidden selected extended allocated body.body_plain
  | default contains scrutinee hidden selected body =>
      exact MatchPlain.default contains scrutinee.value_plain hidden selected body.body_plain
  | noBranch contains scrutinee hidden selected =>
      intro id node found form
      exact .matchNoBranch found form contains scrutinee.value_plain hidden selected

/-- Header item erasure retains every allocation and its actual lexical context. -/
theorem ForItems.plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {items : List ForItemForm} {outcome : ForItemsOutcome}
    (trace : ForItems program registry scope context environment before items finalContext outcome after) :
    ForItemsPlain program scope context environment before items finalContext outcome after := by
  induction trace using ForItems.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
  all_goals try exact True.intro
  case empty => exact .nil
  case absent mono extended allocated next nextIH =>
    exact ForItemsPlain.prepend (.letUninitialized mono extended allocated) nextIH
  case initialized mono extended child allocated next _childIH nextIH =>
    exact ForItemsPlain.prepend (.letInitialized child.value_plain mono extended allocated) nextIH
  case initializerFault mono child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.letInitializer mono child.semanticFault_plain)
  case expression child next _childIH nextIH => exact ForItemsPlain.prepend (.expression child.value_plain) nextIH
  case expressionFailure child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.expression child.semanticFault_plain)
  case assignment snapshot child write next _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignmentFailure snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case unbound _bare missing => exact .head (.assignValue (.target (.unbound missing)))
  case dangling _bare lookup missing => exact .head (.assignValue (.target (.dangling lookup missing)))

/-- A finite for loop retains its actual body and post-item execution. -/
theorem ForLoop.plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {outcome : BodyOutcome}
    (trace : ForLoop program registry scope context environment before condition post body outcome after) :
    ForLoopPlain program scope context environment before condition post body outcome after := by
  induction trace using ForLoop.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
  all_goals try exact True.intro
  case testFault test _testIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .condition test.semanticFault_plain
  case finished test _testIH => exact .done test.value_plain
  case bodyFailure test branch _testIH _branchIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain branch.body_plain
  case returnedFromBody test branch _testIH _branchIH => exact .returns test.value_plain branch.body_plain
  case postFailure test branch postTrace _testIH _branchIH _postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postFallthrough test.value_plain branch.body_plain postTrace.plain
  case iterate test branch postTrace next _testIH _branchIH _postIH nextIH =>
    exact ForLoopPlain.next test.value_plain branch.body_plain postTrace.plain nextIH

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
