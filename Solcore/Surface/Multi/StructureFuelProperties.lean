import Solcore.Surface.Multi.Measure
import Solcore.Surface.Multi.StructureJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open StructureFuelDepth

private def HasStructuralFuelPath
    (module : ParsedModuleV1) : StructuralSite → Prop
  | .expression expression =>
      ∃ depth, StructuralFuelPath module (.expression expression) depth
  | .pattern pattern =>
      ∃ depth, StructuralFuelPath module (.pattern pattern) depth
  | .body loopDepth body =>
      ∃ depth, StructuralFuelPath module (.body loopDepth body) depth
  | .statement loopDepth statement =>
      ∃ depth, StructuralFuelPath module (.statement loopDepth statement) depth
  | .forInit item =>
      ∃ depth, StructuralFuelPath module (.forInit item) depth
  | .forPost item =>
      ∃ depth, StructuralFuelPath module (.forPost item) depth
  | _ => True

private theorem occurs_hasStructuralFuelPath
    {module : ParsedModuleV1} {site : StructuralSite}
    (occurrence : StructuralSite.Occurs module site) :
    HasStructuralFuelPath module site := by
  induction occurrence <;> simp only [HasStructuralFuelPath]
  all_goals try exact True.intro
  case topFunctionBody item declaration itemMember itemShape =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    exact ⟨0, .root (.topLevelFunction itemMember)⟩
  case instanceMethodBody item declaration method itemMember itemShape
      methodMember =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    exact ⟨0, .root (.instanceMethod itemMember methodMember)⟩
  case contractFieldInitializer item declaration member field initializer
      itemMember itemShape memberMember memberShape initializerShape =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    rcases member with ⟨memberSpan, memberPayload⟩
    simp only at memberShape
    subst memberPayload
    exact ⟨0, .root (.contractFieldInitializer
      itemMember memberMember initializerShape)⟩
  case contractFunctionBody item declaration member functionDeclaration
      itemMember itemShape memberMember memberShape =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    rcases member with ⟨memberSpan, memberPayload⟩
    simp only at memberShape
    subst memberPayload
    exact ⟨0, .root (.contractFunction itemMember memberMember)⟩
  case fallbackBody item declaration member fallbackDeclaration
      itemMember itemShape memberMember memberShape =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    rcases member with ⟨memberSpan, memberPayload⟩
    simp only at memberShape
    subst memberPayload
    exact ⟨0, .root (.fallback itemMember memberMember)⟩
  case constructorBody item declaration member constructorDeclaration
      itemMember itemShape memberMember memberShape =>
    rcases item with ⟨itemSpan, itemPayload⟩
    simp only at itemShape
    subst itemPayload
    rcases member with ⟨memberSpan, memberPayload⟩
    simp only at memberShape
    subst memberPayload
    exact ⟨0, .root (.constructor itemMember memberMember)⟩
  case expressionCallCallee expression callee arguments parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression callee) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionCallCallee
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionCallArgument expression callee argument arguments parent
      shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression argument) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionCallArgument member
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionSelectReceiver expression receiver field parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression receiver) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionSelectReceiver
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionDotConstructorArgument expression argument marker name
      arguments parent shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression argument) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionDotConstructorArgument member
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionLambdaBody expression parameters returnType body parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.body 0 body) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionLambdaBody
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionAnnotationInner expression inner typeExpression parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression inner) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionAnnotationInner
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionKeywordCondition expression condition thenBranch elseBranch
      parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression condition) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionKeywordCondition
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionKeywordThen expression condition thenBranch elseBranch parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression thenBranch) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionKeywordThen
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionKeywordElse expression condition thenBranch elseBranch parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression elseBranch) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionKeywordElse
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionTernaryCondition expression condition thenBranch elseBranch
      parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression condition) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionTernaryCondition
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionTernaryThen expression condition thenBranch elseBranch parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression thenBranch) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionTernaryThen
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionTernaryElse expression condition thenBranch elseBranch parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression elseBranch) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionTernaryElse
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionIndexReceiver expression receiver index parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression receiver) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionIndexReceiver
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionIndexValue expression receiver index parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression index) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionIndex
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionPrefixOperand expression operand operator parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression operand) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionPrefixOperand
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionInfixLeft expression left right operator parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression left) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionInfixLeft
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionInfixRight expression left right operator parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression right) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionInfixRight
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionTupleElement expression element elements parent shape member
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression element) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionTupleElement member
    exact ⟨depth + 1, .child parentPath edge⟩
  case expressionGroupInner expression inner parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.expression expression) (.expression inner) := by
      rcases expression with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .expressionGroupInner
    exact ⟨depth + 1, .child parentPath edge⟩
  case patternNamedArgument pattern argument name arguments parent shape member
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.pattern pattern) (.pattern argument) := by
      rcases pattern with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .patternNamedArgument (by
        simpa [NonemptyList.toList] using member)
    exact ⟨depth + 1, .child parentPath edge⟩
  case patternDotConstructorArgument pattern argument marker name arguments
      parent shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.pattern pattern) (.pattern argument) := by
      rcases pattern with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .patternDotConstructorArgument (by
        simpa [NonemptyList.toList] using member)
    exact ⟨depth + 1, .child parentPath edge⟩
  case patternComptimeExpression pattern marker expression parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.pattern pattern) (.expression expression) := by
      rcases pattern with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .patternComptimeExpression
    exact ⟨depth + 1, .child parentPath edge⟩
  case patternTupleElement pattern element elements parent shape member
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.pattern pattern) (.pattern element) := by
      rcases pattern with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .patternTupleElement member
    exact ⟨depth + 1, .child parentPath edge⟩
  case patternGroupInner pattern inner parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.pattern pattern) (.pattern inner) := by
      rcases pattern with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .patternGroupInner
    exact ⟨depth + 1, .child parentPath edge⟩
  case bodyStatement loopDepth body statement parent member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.body loopDepth body) (.statement loopDepth statement) := by
      rcases body with ⟨span, payload⟩
      rcases payload with ⟨origin, statements⟩
      simp only at member ⊢
      exact .bodyStatement member
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementAssignmentLeft loopDepth left right statement operator parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression left) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementAssignmentLeft
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementAssignmentRight loopDepth left right statement operator parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression right) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementAssignmentRight
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementLetInitializer loopDepth statement binding initializer parent
      shape initializerShape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression initializer) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementLetInitializer initializerShape
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementBlockBody loopDepth statement body parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.body loopDepth body) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementBlockBody
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementExpression loopDepth statement expression terminator parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression expression) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementExpression
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementReturnValue loopDepth statement expression terminator parent shape
      induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression expression) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementReturnExpression
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementMatchScrutinee loopDepth statement scrutinees arms terminator
      scrutinee parent shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression scrutinee) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementMatchScrutinee (by
        simpa [NonemptyList.toList] using member)
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementMatchPattern loopDepth statement scrutinees arms terminator arm
      pattern parent shape armMember patternMember induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.pattern pattern) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementMatchPattern
        (by simpa [NonemptyList.toList] using armMember)
        (by simpa [NonemptyList.toList] using patternMember)
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementMatchArmBody loopDepth statement scrutinees arms terminator arm
      parent shape armMember induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.body loopDepth arm.payload.body) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementMatchBody (by
        simpa [NonemptyList.toList] using armMember)
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementIfCondition loopDepth statement condition thenBody elseBody parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression condition) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementIfCondition
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementIfThenBody loopDepth statement condition thenBody elseBody parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.body loopDepth thenBody) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementIfThenBody
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementIfElseBody loopDepth statement condition thenBody elseBody parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.body loopDepth elseBody) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementIfElseBody
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementForInitializer loopDepth statement initializers condition post body
      item parent shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.forInit item) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementForInitializer member
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementForCondition loopDepth statement initializers condition post body
      parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.expression condition) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementForCondition
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementForPost loopDepth statement initializers condition post body item
      parent shape member induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.forPost item) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementForPost member
    exact ⟨depth + 1, .child parentPath edge⟩
  case statementForBody loopDepth statement initializers condition post body parent
      shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.statement loopDepth statement) (.body (loopDepth + 1) body) := by
      rcases statement with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .statementForBody
    exact ⟨depth + 1, .child parentPath edge⟩
  case forInitLetInitializer item binding initializer parent shape
      initializerShape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forInit item) (.expression initializer) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forInitLetInitializer initializerShape
    exact ⟨depth + 1, .child parentPath edge⟩
  case forInitAssignmentLeft item left right operator parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forInit item) (.expression left) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forInitAssignmentLeft
    exact ⟨depth + 1, .child parentPath edge⟩
  case forInitAssignmentRight item left right operator parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forInit item) (.expression right) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forInitAssignmentRight
    exact ⟨depth + 1, .child parentPath edge⟩
  case forInitExpression item expression parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forInit item) (.expression expression) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forInitExpression
    exact ⟨depth + 1, .child parentPath edge⟩
  case forPostAssignmentLeft item left right operator parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forPost item) (.expression left) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forPostAssignmentLeft
    exact ⟨depth + 1, .child parentPath edge⟩
  case forPostAssignmentRight item left right operator parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forPost item) (.expression right) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forPostAssignmentRight
    exact ⟨depth + 1, .child parentPath edge⟩
  case forPostExpression item expression parent shape induction =>
    rcases induction with ⟨depth, parentPath⟩
    have edge : RecursiveAstChild
        (.forPost item) (.expression expression) := by
      rcases item with ⟨span, payload⟩
      simp only at shape
      subst payload
      exact .forPostExpression
    exact ⟨depth + 1, .child parentPath edge⟩

namespace StructuralSite

/-- A reached expression has an exact structural-fuel path from its module. -/
theorem Occurs.expression_fuelPath
    {module : ParsedModuleV1} {expression : Expression}
    (occurrence : Occurs module (.expression expression)) :
    ∃ depth, StructuralFuelPath module (.expression expression) depth :=
  occurs_hasStructuralFuelPath occurrence

/-- A reached pattern has an exact structural-fuel path from its module. -/
theorem Occurs.pattern_fuelPath
    {module : ParsedModuleV1} {pattern : Pattern}
    (occurrence : Occurs module (.pattern pattern)) :
    ∃ depth, StructuralFuelPath module (.pattern pattern) depth :=
  occurs_hasStructuralFuelPath occurrence

/-- A reached body retains its loop depth in its structural-fuel path. -/
theorem Occurs.body_fuelPath
    {module : ParsedModuleV1} {loopDepth : Nat} {body : Body}
    (occurrence : Occurs module (.body loopDepth body)) :
    ∃ depth, StructuralFuelPath module (.body loopDepth body) depth :=
  occurs_hasStructuralFuelPath occurrence

/-- A reached statement retains its loop depth in its structural-fuel path. -/
theorem Occurs.statement_fuelPath
    {module : ParsedModuleV1} {loopDepth : Nat} {statement : Statement}
    (occurrence : Occurs module (.statement loopDepth statement)) :
    ∃ depth, StructuralFuelPath module (.statement loopDepth statement) depth :=
  occurs_hasStructuralFuelPath occurrence

/-- A reached `for` initializer has an exact path from its module. -/
theorem Occurs.forInit_fuelPath
    {module : ParsedModuleV1} {item : ForInitItem}
    (occurrence : Occurs module (.forInit item)) :
    ∃ depth, StructuralFuelPath module (.forInit item) depth :=
  occurs_hasStructuralFuelPath occurrence

/-- A reached `for` post item has an exact path from its module. -/
theorem Occurs.forPost_fuelPath
    {module : ParsedModuleV1} {item : ForPostItem}
    (occurrence : Occurs module (.forPost item)) :
    ∃ depth, StructuralFuelPath module (.forPost item) depth :=
  occurs_hasStructuralFuelPath occurrence

end StructuralSite

end Solcore.Surface.Multi
