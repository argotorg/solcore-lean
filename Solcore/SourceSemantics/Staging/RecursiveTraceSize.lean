import Solcore.SourceSemantics.Staging.RecursiveTrace

/-! Finite grades for the existing independent recursive staged profile.
Every recursive expression, argument list, invocation and statement body has
a strictly smaller grade than its parent. The original invocation scope,
stage failure and prefix heaps are unchanged. This grades the supported Source
judgments; it does not extend their coverage or assume a compiler theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.Staging.Recursive.Size
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- One step above the sum of the grades of the children that ran. -/
def stepSize (children : List Nat) : Nat := children.sum + 1

theorem stepSize_positive (children : List Nat) : 0 < stepSize children := by
  simp [stepSize]

theorem child_lt_stepSize {child : Nat} {children : List Nat}
    (member : child ∈ children) : child < stepSize children := by
  have bound : child ≤ children.sum := by
    induction children with
    | nil => cases member
    | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have bound := ih member
        simp only [List.sum_cons]
        omega
  unfold stepSize
  omega

mutual
  inductive Expression (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → ExpressionId → Outcome → Heap → Prop where
    | atomicValue {scope context environment before after id node value}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          node.form node.requirements [] value after) :
        Expression program registry (stepSize []) scope context environment before id (.value value) after
    | atomicFault {scope context environment before after id node reason}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          node.form node.requirements [] reason after) :
        Expression program registry (stepSize []) scope context environment before id (.fault (.semantic reason)) after
    | group {childSize : Nat} {scope context environment before after id inner outcome}
        (occurrence : Occurrence scope id (.group inner))
        (child : Expression program registry childSize scope context environment before inner outcome after) :
        Expression program registry (stepSize [childSize]) scope context environment before id outcome after
    | pair {firstSize secondSize : Nat} {scope context environment before middle after id left right a b}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry firstSize scope context environment before left (.value a) middle)
        (second : Expression program registry secondSize scope context environment middle right (.value b) after) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id (.value (.product a b)) after
    | pairLeftFault {childSize : Nat} {scope context environment before after id left right failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (child : Expression program registry childSize scope context environment before left (.fault failure) after) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault failure) after
    | pairRightFault {firstSize secondSize : Nat} {scope context environment before middle after id left right value failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry firstSize scope context environment before left (.value value) middle)
        (second : Expression program registry secondSize scope context environment middle right (.fault failure) after) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id (.fault failure) after
    | tupleValue {childrenSize : Nat} {scope context environment before after id elements values packed}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry childrenSize scope context environment before elements (.values values) after)
        (pack : ValuesPack values packed) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.value packed) after
    | tupleFault {childrenSize : Nat} {scope context environment before after id elements failure}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry childrenSize scope context environment before elements (.fault failure) after) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.fault failure) after
    | constructorValue {childrenSize : Nat} {scope context environment before after id instantiation arguments values}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (children : Expressions program registry childrenSize scope context environment before arguments (.values values) after) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.value (.constructed instantiation values)) after
    | constructorFault {childrenSize : Nat} {scope context environment before after id instantiation arguments failure}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (children : Expressions program registry childrenSize scope context environment before arguments (.fault failure) after) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.fault failure) after
    | indexBaseFault {firstSize : Nat} {scope context environment before after id base key failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry firstSize scope context environment before base (.fault failure) after) :
        Expression program registry (stepSize [firstSize]) scope context environment before id (.fault failure) after
    | indexKeyFault {firstSize secondSize : Nat} {scope context environment before middle after id base key value failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry firstSize scope context environment before base (.value value) middle)
        (second : Expression program registry secondSize scope context environment middle key (.fault failure) after) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id (.fault failure) after
    | indexResult {firstSize secondSize : Nat} {scope context environment before middle after id base key baseValue keyValue outcome}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry firstSize scope context environment before base (.value baseValue) middle)
        (second : Expression program registry secondSize scope context environment middle key (.value keyValue) after)
        (result : IndexOutcome baseValue keyValue outcome) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id outcome after
    | unary {childSize : Nat} {scope context environment before after id operator operand input output}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry childSize scope context environment before operand (.value input) after)
        (applies : UnaryPrimitiveApplies operator input output) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.value output) after
    | unaryOperandFault {childSize : Nat} {scope context environment before after id operator operand failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (child : Expression program registry childSize scope context environment before operand (.fault failure) after) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault failure) after
    | unaryInvalid {childSize : Nat} {scope context environment before after id operator operand input}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry childSize scope context environment before operand (.value input) after)
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        Expression program registry (stepSize [childSize]) scope context environment before id
          (.fault (.semantic (.invalidUnaryOperand operator))) after
    | binaryLeftFault {firstSize : Nat} {scope context environment before after id left operator right failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (first : Expression program registry firstSize scope context environment before left (.fault failure) after) :
        Expression program registry (stepSize [firstSize]) scope context environment before id (.fault failure) after
    | binaryLeftInvalid {firstSize : Nat} {scope context environment before after id left operator right input}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry firstSize scope context environment before left (.value input) after)
        (invalid : BinaryLeftOperandInvalid operator input) :
        Expression program registry (stepSize [firstSize]) scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | binaryShortCircuit {firstSize : Nat} {scope context environment before after id left operator right input output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry firstSize scope context environment before left (.value input) after)
        (circuit : ShortCircuits operator input output) :
        Expression program registry (stepSize [firstSize]) scope context environment before id (.value output) after
    | binaryRightFault {firstSize secondSize : Nat} {scope context environment before middle after id left operator right input failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (first : Expression program registry firstSize scope context environment before left (.value input) middle)
        (continues : EvaluatesRightOperand operator input)
        (second : Expression program registry secondSize scope context environment middle right (.fault failure) after) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id (.fault failure) after
    | binary {firstSize secondSize : Nat} {scope context environment before middle after id left operator right a b output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry firstSize scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry secondSize scope context environment middle right (.value b) after)
        (applies : BinaryPrimitiveApplies operator a b output) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id (.value output) after
    | binaryInvalid {firstSize secondSize : Nat} {scope context environment before middle after id left operator right a b}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry firstSize scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry secondSize scope context environment middle right (.value b) after)
        (invalid : BinaryPrimitiveOperandsInvalid operator a b) :
        Expression program registry (stepSize [firstSize, secondSize]) scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | unaryMethod {operandSize bodySize : Nat} {scope context environment before argumentsHeap bound after id operator operand input
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (operandTrace : Expression program registry operandSize scope context environment before operand (.value input) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry (stepSize [operandSize, bodySize]) scope context environment before id result after
    | binaryMethod {leftSize rightSize bodySize : Nat} {scope context environment before middle argumentsHeap bound after id left operator right a b
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (first : Expression program registry leftSize scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry rightSize scope context environment middle right (.value b) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [a, b] bodyEnvironment bound)
        (body : StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry (stepSize [leftSize, rightSize, bodySize]) scope context environment before id result after
    | conditional {testSize branchSize : Nat} {scope context environment before middle after id condition yes no truth outcome}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : Expression program registry branchSize scope context environment middle (if truth then yes else no) outcome after) :
        Expression program registry (stepSize [testSize, branchSize]) scope context environment before id outcome after
    | conditionalFault {testSize : Nat} {scope context environment before after id condition yes no failure}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry testSize scope context environment before condition (.fault failure) after) :
        Expression program registry (stepSize [testSize]) scope context environment before id (.fault failure) after
    | builtinArgumentsFault {childrenSize : Nat} {scope context environment before after id callee arguments function failure}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry childrenSize scope context environment before arguments (.fault failure) after) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.fault failure) after
    | builtinApplied {childrenSize invocationSize : Nat} {scope context environment before argumentsHeap after id callee arguments function values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry childrenSize scope context environment before arguments (.values values) argumentsHeap)
        (invocation : Applies program registry invocationSize scope context argumentsHeap (.builtin ⟨function⟩) values outcome after) :
        Expression program registry (stepSize [childrenSize, invocationSize]) scope context environment before id outcome after
    | directArgumentsFault {childrenSize : Nat} {scope context environment before after id callee arguments instantiation name failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry childrenSize scope context environment before arguments (.fault failure) after) :
        Expression program registry (stepSize [childrenSize]) scope context environment before id (.fault failure) after
    | directApplied {childrenSize invocationSize : Nat} {scope context environment before argumentsHeap after id callee arguments instantiation name values evidence outcome}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry childrenSize scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements [] instantiation.predicates evidence)
        (invocation : Applies program registry invocationSize scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        Expression program registry (stepSize [childrenSize, invocationSize]) scope context environment before id outcome after
    | calleeFault {childSize : Nat} {scope context environment before after id callee arguments metadata failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry childSize scope context environment before callee (.fault failure) after) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault failure) after
    | notCallable {childSize : Nat} {scope context environment before after id callee arguments metadata value}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry childSize scope context environment before callee (.value value) after)
        (invalid : ¬ CallableValue value) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault (.semantic .notCallable)) after
    | rejected {childSize : Nat} {scope context environment before after id callee arguments metadata value reason}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry childSize scope context environment before callee (.value value) after)
        (guard : CallBoundary.GuardRejects scope.guards id arguments value reason) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault (.stage scope id reason)) after
    | argumentsFault {childSize childrenSize : Nat} {scope context environment before middle after id callee arguments metadata value failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry childSize scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry childrenSize scope context environment middle arguments (.fault failure) after) :
        Expression program registry (stepSize [childSize, childrenSize]) scope context environment before id (.fault failure) after
    | sourceArity {childSize childrenSize : Nat} {scope context environment before middle after id callee arguments metadata value values}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry childSize scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry childrenSize scope context environment middle arguments (.values values) after)
        (mismatch : arguments.length ≠ metadata.argumentCount) :
        Expression program registry (stepSize [childSize, childrenSize]) scope context environment before id
          (.fault (.semantic (.argumentArityMismatch metadata.argumentCount arguments.length))) after
    | applied {childSize childrenSize invocationSize : Nat} {scope context environment before calleeHeap argumentsHeap after id callee arguments metadata value values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (uncoerced : metadata.argumentCoercions = [])
        (child : Expression program registry childSize scope context environment before callee (.value value) calleeHeap)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry childrenSize scope context environment calleeHeap arguments (.values values) argumentsHeap)
        (arity : arguments.length = metadata.argumentCount)
        (invocation : Applies program registry invocationSize scope context argumentsHeap value values outcome after) :
        Expression program registry (stepSize [childSize, childrenSize, invocationSize]) scope context environment before id outcome after

    | coercedValue {rawSize pathSize : Nat} {scope context environment before middle after id node value outcome}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry rawSize scope context environment before node.form
          node.requirements node.coercions (.value value) middle)
        (path : CoercionPath program registry pathSize scope context middle node.coercions value outcome after) :
        Expression program registry (stepSize [rawSize, pathSize]) scope context environment before id outcome after
    | coercedFault {rawSize : Nat} {scope context environment before after id node failure}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry rawSize scope context environment before node.form
          node.requirements node.coercions (.fault failure) after) :
        Expression program registry (stepSize [rawSize]) scope context environment before id (.fault failure) after

  inductive Expressions (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → List ExpressionId → ValuesOutcome → Heap → Prop where
    | nil {scope context environment heap} :
        Expressions program registry (stepSize []) scope context environment heap [] (.values []) heap
    | cons {headSize tailSize : Nat} {scope context environment before middle after id ids value values}
        (head : Expression program registry headSize scope context environment before id (.value value) middle)
        (tail : Expressions program registry tailSize scope context environment middle ids (.values values) after) :
        Expressions program registry (stepSize [headSize, tailSize]) scope context environment before (id :: ids) (.values (value :: values)) after
    | headFault {headSize : Nat} {scope context environment before after id ids failure}
        (head : Expression program registry headSize scope context environment before id (.fault failure) after) :
        Expressions program registry (stepSize [headSize]) scope context environment before (id :: ids) (.fault failure) after
    | tailFault {headSize tailSize : Nat} {scope context environment before middle after id ids value failure}
        (head : Expression program registry headSize scope context environment before id (.value value) middle)
        (tail : Expressions program registry tailSize scope context environment middle ids (.fault failure) after) :
        Expressions program registry (stepSize [headSize, tailSize]) scope context environment before (id :: ids) (.fault failure) after

  inductive Applies (program : Program) (registry : Registry) :
      Nat → Scope → Context → Heap → Value → List Value → Outcome → Heap → Prop where
    | builtin {scope context heap function arguments value}
        (primitive : BuiltinApplies function.id arguments value) :
        Applies program registry (stepSize []) scope context heap (.builtin function) arguments (.value value) heap
    | builtinArity {scope context heap function arguments}
        (mismatch : function.id.parameterTypes.length ≠ arguments.length) :
        Applies program registry (stepSize []) scope context heap (.builtin function) arguments
          (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length arguments.length))) heap
    | builtinType {scope context heap function arguments expected actual}
        (arity : function.id.parameterTypes.length = arguments.length)
        (mismatch : ValuesFirstTypeMismatch arguments function.id.parameterTypes expected actual) :
        Applies program registry (stepSize []) scope context heap (.builtin function) arguments
          (.fault (.semantic (.typeMismatch expected actual))) heap
    | closureArity {scope context heap function arguments}
        (mismatch : function.parameters.length ≠ arguments.length) :
        Applies program registry (stepSize []) scope context heap (.closure function) arguments
          (.fault (.semantic (.argumentArityMismatch function.parameters.length arguments.length))) heap
    | globalArity {scope context heap function arguments bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        Applies program registry (stepSize []) scope context heap (.global function) arguments
          (.fault (.semantic (.argumentArityMismatch bodyInstance.source.inputs.length arguments.length))) heap
    | global {bodySize : Nat} {scope context before bound after function arguments environment
          parameterTypes bodyContext finalContext bodyInstance roots child outcome result}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (covers : function.evidence.Covers bodyInstance.context)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
        (body : StatementsIn program registry true bodySize child bodyContext environment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Applies program registry (stepSize [bodySize]) scope context before (.global function) arguments result after
    | closure {bodySize : Nat} {scope context before bound after function arguments environment parameterTypes bodyContext finalContext child outcome result}
        (selected : registry.Closure function child)
        (valid : ClosureFrame program function)
        (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
        (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
        (body : StatementsIn program registry true bodySize child bodyContext environment bound function.body finalContext outcome after)
        (resultRule : BodyResult function.resultType outcome result) :
        Applies program registry (stepSize [bodySize]) scope context before (.closure function) arguments result after

  inductive StatementsIn (program : Program) (registry : Registry) :
      Bool → Nat → Scope → Context → Environment → Heap → List StatementId → Context → BodyOutcome → Heap → Prop where
    | nil {mode scope context environment heap} :
        StatementsIn program registry mode (stepSize []) scope context environment heap [] context (.fallthrough environment) heap
    | returnUnit {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt none) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context (.returned .unit) heap
    | continuing {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .continueStmt) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context (.continuing environment) heap
    | breaking {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .breakStmt) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context (.breaking environment) heap
    | returnValue {childSize : Nat} {mode scope context environment before after id rest node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry childSize scope context environment before expression (.value value) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.returned value) after
    | returnFault {childSize : Nat} {mode scope context environment before after id rest node expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | tail {childSize : Nat} {scope context environment before after id node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry childSize scope context environment before expression (.value value) after) :
        StatementsIn program registry true (stepSize [childSize]) scope context environment before [id] context (.returned value) after
    | discard {childSize nextSize : Nat} {mode scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression true)
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry mode nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | expressionFault {childSize : Nat} {mode scope context environment before after id rest node expression semicolon failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression semicolon)
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    /-- A non-tail branch expression discards its value even at the end of its arm. -/
    | discardValue {childSize nextSize : Nat} {scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry false nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry false (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | ifConditionFault {testSize : Nat} {mode scope context environment before after id rest node condition thenBody elseBody failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.fault failure) after) :
        StatementsIn program registry mode (stepSize [testSize]) scope context environment before (id :: rest) context (.fault failure) after
    | ifReturned {testSize branchSize : Nat} {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.returned value) after) :
        StatementsIn program registry mode (stepSize [testSize, branchSize]) scope context environment before (id :: rest) context (.returned value) after
    | ifContinuing {testSize branchSize : Nat} {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode (stepSize [testSize, branchSize]) scope context environment before (id :: rest) context (.continuing environment) after
    | ifBreaking {testSize branchSize : Nat} {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode (stepSize [testSize, branchSize]) scope context environment before (id :: rest) context (.breaking environment) after
    | ifFault {testSize branchSize : Nat} {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fault failure) after) :
        StatementsIn program registry mode (stepSize [testSize, branchSize]) scope context environment before (id :: rest) context (.fault failure) after
    /-- Branch-local bindings leave scope; all writes and allocations remain in its reached heap. -/
    | ifFallthrough {testSize branchSize nextSize : Nat} {mode scope context innerContext finalContext environment innerEnvironment before middle branchHeap after
          id rest node condition thenBody elseBody truth outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fallthrough innerEnvironment) branchHeap)
        (next : StatementsIn program registry mode nextSize scope context environment branchHeap rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [testSize, branchSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | blockReturned {innerSize : Nat} {mode scope context innerContext environment before after id rest node statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false innerSize scope context environment before statements innerContext (.returned value) after) :
        StatementsIn program registry mode (stepSize [innerSize]) scope context environment before (id :: rest) context (.returned value) after
    | blockContinuing {innerSize : Nat} {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false innerSize scope context environment before statements innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode (stepSize [innerSize]) scope context environment before (id :: rest) context (.continuing environment) after
    | blockBreaking {innerSize : Nat} {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false innerSize scope context environment before statements innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode (stepSize [innerSize]) scope context environment before (id :: rest) context (.breaking environment) after
    | blockFault {innerSize : Nat} {mode scope context innerContext environment before after id rest node statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false innerSize scope context environment before statements innerContext (.fault failure) after) :
        StatementsIn program registry mode (stepSize [innerSize]) scope context environment before (id :: rest) context (.fault failure) after
    /-- A block restores its entry bindings while retaining every write and allocation. -/
    | blockFallthrough {innerSize nextSize : Nat} {mode scope context innerContext finalContext environment innerEnvironment before middle after id rest node statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false innerSize scope context environment before statements innerContext (.fallthrough innerEnvironment) middle)
        (next : StatementsIn program registry mode nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [innerSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | matchReturned {matchSize : Nat} {mode scope context environment before after id rest node resolution value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.returned value) after) :
        StatementsIn program registry mode (stepSize [matchSize]) scope context environment before (id :: rest) context (.returned value) after
    | matchContinuing {matchSize : Nat} {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.continuing environment) after) :
        StatementsIn program registry mode (stepSize [matchSize]) scope context environment before (id :: rest) context (.continuing environment) after
    | matchBreaking {matchSize : Nat} {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.breaking environment) after) :
        StatementsIn program registry mode (stepSize [matchSize]) scope context environment before (id :: rest) context (.breaking environment) after
    | matchFault {matchSize : Nat} {mode scope context environment before after id rest node resolution failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.fault failure) after) :
        StatementsIn program registry mode (stepSize [matchSize]) scope context environment before (id :: rest) context (.fault failure) after
    | matchFallthrough {matchSize nextSize : Nat} {mode scope context finalContext environment before middle after id rest node resolution outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.fallthrough environment) middle)
        (next : StatementsIn program registry mode nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [matchSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | forInitializerFault {initialSize : Nat} {mode scope context failedContext environment before after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry initialSize scope context environment before initializer failedContext (.fault failure) after) :
        StatementsIn program registry mode (stepSize [initialSize]) scope context environment before (id :: rest) context (.fault failure) after
    | forReturned {initialSize loopSize : Nat} {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry initialSize scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry loopSize scope loopContext loopEnvironment middle condition post body (.returned value) after) :
        StatementsIn program registry mode (stepSize [initialSize, loopSize]) scope context environment before (id :: rest) context (.returned value) after
    | forFault {initialSize loopSize : Nat} {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry initialSize scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry loopSize scope loopContext loopEnvironment middle condition post body (.fault failure) after) :
        StatementsIn program registry mode (stepSize [initialSize, loopSize]) scope context environment before (id :: rest) context (.fault failure) after
    | forFallthrough {initialSize loopSize nextSize : Nat} {mode scope context loopContext finalContext environment loopEnvironment before middle loopHeap after
          id rest node initializer condition post body outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry initialSize scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry loopSize scope loopContext loopEnvironment middle condition post body (.fallthrough loopEnvironment) loopHeap)
        (next : StatementsIn program registry mode nextSize scope context environment loopHeap rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [initialSize, loopSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | whileReturned {loopSize : Nat} {mode scope context environment before after id rest node condition statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry loopSize scope context environment before condition statements (.returned value) after) :
        StatementsIn program registry mode (stepSize [loopSize]) scope context environment before (id :: rest) context (.returned value) after
    | whileFault {loopSize : Nat} {mode scope context environment before after id rest node condition statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry loopSize scope context environment before condition statements (.fault failure) after) :
        StatementsIn program registry mode (stepSize [loopSize]) scope context environment before (id :: rest) context (.fault failure) after
    | whileFallthrough {loopSize nextSize : Nat} {mode scope context finalContext environment before middle after id rest node condition statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry loopSize scope context environment before condition statements (.fallthrough environment) middle)
        (next : StatementsIn program registry mode nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [loopSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    /-- The target snapshot precedes the RHS; the write uses its actual final heap. -/
    | bitNotProjected {keysSize nextSize : Nat} {mode scope context finalContext environment before targetHeap written after assignment values target updated id rest node outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (write : ResolvedPlaceWrites
          (fun _ replacement => BitNotSnapshot target.selected replacement)
          targetHeap target updated written)
        (next : StatementsIn program registry mode nextSize scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [keysSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | bitNotProjectedRootFault {mode scope context environment before assignment id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        StatementsIn program registry mode (stepSize []) scope context environment before (id :: rest) context (.fault (.semantic reason)) before
    | bitNotProjectedKeysFault {keysSize : Nat} {mode scope context environment before after assignment id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        StatementsIn program registry mode (stepSize [keysSize]) scope context environment before (id :: rest) context (.fault failure) after
    | bitNotProjectedGetterFault {keysSize : Nat} {mode scope context environment before after assignment values id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        StatementsIn program registry mode (stepSize [keysSize]) scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignProjected {keysSize childSize nextSize : Nat} {mode scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated id rest node outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode nextSize scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [keysSize, childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | assignProjectedRootFault {mode scope context environment before assignment operator rhs id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        StatementsIn program registry mode (stepSize []) scope context environment before (id :: rest) context (.fault (.semantic reason)) before
    | assignProjectedKeysFault {keysSize : Nat} {mode scope context environment before after assignment operator rhs id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        StatementsIn program registry mode (stepSize [keysSize]) scope context environment before (id :: rest) context (.fault failure) after
    | assignProjectedGetterFault {keysSize : Nat} {mode scope context environment before after assignment operator rhs values id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        StatementsIn program registry mode (stepSize [keysSize]) scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignProjectedRhsFault {keysSize childSize : Nat} {mode scope context environment before targetHeap after assignment operator rhs values target id rest node failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.fault failure) after) :
        StatementsIn program registry mode (stepSize [keysSize, childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | assignProjectedWriteFault {keysSize childSize : Nat} {mode scope context environment before targetHeap after assignment operator rhs values target right id rest node reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.value right) after)
        (failed : ProjectedTarget.WriteFault operator target right after reason) :
        StatementsIn program registry mode (stepSize [keysSize, childSize]) scope context environment before (id :: rest) context (.fault (.semantic reason)) after
    | assignBare {childSize nextSize : Nat} {mode scope context finalContext environment before middle written after
          id rest node assignment operator rhs value target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode nextSize scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | assignBareFault {childSize : Nat} {mode scope context environment before after id rest node assignment operator rhs target failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.fault failure) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | assignBareOperands {childSize : Nat} {mode scope context environment before after id rest node assignment operator rhs
          target right currentCell initial currentSelected}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | assignBareUnbound {mode scope context environment heap id rest node assignment operator rhs}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | assignBareDangling {mode scope context environment heap id rest node assignment operator rhs location}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap
    /-- Bare unary assignment reads its snapshot and performs a real write,
    without an expression child for the compiler's administrative Unit. -/
    | bitNotBare {nextSize : Nat} {mode scope context finalContext environment before written after
          id rest node assignment target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (snapshot : BareTarget environment before assignment.target target)
        (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
          before target updated written)
        (next : StatementsIn program registry mode nextSize scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | bitNotBareFault {mode scope context environment before id rest node assignment reason}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignBitNot assignment)
        (bare : assignment.target.projections = [])
        (failed : SourcePlaceBitNotFaults program context scope.evidence scope.source environment
          before assignment.target reason before) :
        StatementsIn program registry mode (stepSize []) scope context environment before (id :: rest) context
          (.fault (.semantic reason)) before
    | letUninitialized {nextSize : Nat} {mode scope context middleContext finalContext environment before bound after id rest node binder location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : StatementsIn program registry mode nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | letInitialized {childSize nextSize : Nat} {mode scope context middleContext finalContext environment before middle bound after id rest node binder expression value location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : StatementsIn program registry mode nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | letFault {childSize : Nat} {mode scope context environment before after id rest node binder expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after

  /-- Finite loop iterations restore their original lexical scope while retaining
  all condition and body heap effects. Break leaves the loop; continue tests again. -/
  inductive While (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → ExpressionId → List StatementId → BodyOutcome → Heap → Prop where
    | done {testSize : Nat} {scope context environment before after condition statements}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool false)) after) :
        While program registry (stepSize [testSize]) scope context environment before condition statements (.fallthrough environment) after
    | conditionFault {testSize : Nat} {scope context environment before after condition statements failure}
        (test : Expression program registry testSize scope context environment before condition (.fault failure) after) :
        While program registry (stepSize [testSize]) scope context environment before condition statements (.fault failure) after
    | returned {testSize bodySize : Nat} {scope context innerContext environment before middle after condition statements value}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.returned value) after) :
        While program registry (stepSize [testSize, bodySize]) scope context environment before condition statements (.returned value) after
    | breakFromBody {testSize bodySize : Nat} {scope context innerContext environment before middle after condition statements innerEnvironment}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.breaking innerEnvironment) after) :
        While program registry (stepSize [testSize, bodySize]) scope context environment before condition statements (.fallthrough environment) after
    | bodyFault {testSize bodySize : Nat} {scope context innerContext environment before middle after condition statements failure}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.fault failure) after) :
        While program registry (stepSize [testSize, bodySize]) scope context environment before condition statements (.fault failure) after
    | next {testSize bodySize nextSize : Nat} {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.fallthrough innerEnvironment) bodyHeap)
        (next : While program registry nextSize scope context environment bodyHeap condition statements outcome after) :
        While program registry (stepSize [testSize, bodySize, nextSize]) scope context environment before condition statements outcome after

    | continueNext {testSize bodySize nextSize : Nat} {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.continuing innerEnvironment) bodyHeap)
        (next : While program registry nextSize scope context environment bodyHeap condition statements outcome after) :
        While program registry (stepSize [testSize, bodySize, nextSize]) scope context environment before condition statements outcome after

  /-- The original source's ordered pattern decision and real allocations are
  independent of the compiler. Selected bodies keep the same staged registry. -/
  inductive Match (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → MatchResolution → BodyOutcome → Heap → Prop where
    | scrutineeFault {scrutineeSize : Nat} {scope context environment before after resolution failure}
        (scrutinee : Expression program registry scrutineeSize scope context environment before resolution.scrutinee (.fault failure) after) :
        Match program registry (stepSize [scrutineeSize]) scope context environment before resolution (.fault failure) after
    | patternFault {scrutineeSize : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scrutineeSize scope context environment before resolution.scrutinee (.value value) middle)
        (allocated : Heap.Allocates middle node.type (some value) location hidden)
        (invalid : MatchCasesPatternFault context value resolution.cases) :
        Match program registry (stepSize [scrutineeSize]) scope context environment before resolution (.fault (.semantic .invalidPattern)) hidden
    | arm {scrutineeSize bodySize : Nat} {scope context armContext finalContext environment armEnvironment before middle hidden bound after
          resolution node value location statements bindings outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scrutineeSize scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
        (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
        (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
        (body : StatementsIn program registry false bodySize scope armContext armEnvironment bound statements finalContext outcome after) :
        Match program registry (stepSize [scrutineeSize, bodySize]) scope context environment before resolution (outcome.restore environment) after
    | default {scrutineeSize bodySize : Nat} {scope context finalContext environment before middle hidden after resolution node value location statements outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scrutineeSize scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
        (body : StatementsIn program registry false bodySize scope context environment hidden statements finalContext outcome after) :
        Match program registry (stepSize [scrutineeSize, bodySize]) scope context environment before resolution (outcome.restore environment) after
    | noBranch {scrutineeSize : Nat} {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scrutineeSize scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
        Match program registry (stepSize [scrutineeSize]) scope context environment before resolution (.fallthrough environment) hidden

  /-- Ordered ordinary for-header effects retain their actual lexical context.
  A fault carries the context reached before the failing item. -/
  inductive ForItems (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → List ForItemForm → Context → ForItemsOutcome → Heap → Prop where
    | empty {scope context environment heap} :
        ForItems program registry (stepSize []) scope context environment heap [] context (.done environment) heap
    | absent {nextSize : Nat} {scope context middleContext finalContext environment before bound after binder rest location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : ForItems program registry nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry (stepSize [nextSize]) scope context environment before (.letDecl binder none :: rest) finalContext outcome after
    | initialized {childSize nextSize : Nat} {scope context middleContext finalContext environment before middle bound after binder initializer rest value location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (child : Expression program registry childSize scope context environment before initializer (.value value) middle)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : ForItems program registry nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry (stepSize [childSize, nextSize]) scope context environment before (.letDecl binder (some initializer) :: rest) finalContext outcome after
    | initializerFault {childSize : Nat} {scope context environment before after binder initializer rest failure}
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry childSize scope context environment before initializer (.fault failure) after) :
        ForItems program registry (stepSize [childSize]) scope context environment before (.letDecl binder (some initializer) :: rest) context (.fault failure) after
    | expression {childSize nextSize : Nat} {scope context finalContext environment before middle after expression rest value outcome}
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (next : ForItems program registry nextSize scope context environment middle rest finalContext outcome after) :
        ForItems program registry (stepSize [childSize, nextSize]) scope context environment before (.expression expression :: rest) finalContext outcome after
    | expressionFailure {childSize : Nat} {scope context environment before after expression rest failure}
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        ForItems program registry (stepSize [childSize]) scope context environment before (.expression expression :: rest) context (.fault failure) after
    | projectedBitNot {keysSize nextSize : Nat} {scope context finalContext environment before targetHeap written after assignment values target updated rest outcome}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (write : ResolvedPlaceWrites
          (fun _ replacement => BitNotSnapshot target.selected replacement)
          targetHeap target updated written)
        (next : ForItems program registry nextSize scope context environment written rest finalContext outcome after) :
        ForItems program registry (stepSize [keysSize, nextSize]) scope context environment before (.assignBitNot assignment :: rest) finalContext outcome after
    | projectedBitNotRootFault {scope context environment before assignment rest reason}
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        ForItems program registry (stepSize []) scope context environment before (.assignBitNot assignment :: rest) context (.fault (.semantic reason)) before
    | projectedBitNotKeysFault {keysSize : Nat} {scope context environment before after assignment rest failure}
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        ForItems program registry (stepSize [keysSize]) scope context environment before (.assignBitNot assignment :: rest) context (.fault failure) after
    | projectedBitNotGetterFault {keysSize : Nat} {scope context environment before after assignment values rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        ForItems program registry (stepSize [keysSize]) scope context environment before (.assignBitNot assignment :: rest) context (.fault (.semantic reason)) after
    | projectedAssignment {keysSize childSize nextSize : Nat} {scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated rest outcome}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : ForItems program registry nextSize scope context environment written rest finalContext outcome after) :
        ForItems program registry (stepSize [keysSize, childSize, nextSize]) scope context environment before (.assignValue assignment operator rhs :: rest) finalContext outcome after
    | projectedAssignmentRootFault {scope context environment before assignment operator rhs rest reason}
        (projected : assignment.target.projections ≠ [])
        (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
        ForItems program registry (stepSize []) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) before
    | projectedAssignmentKeysFault {keysSize : Nat} {scope context environment before after assignment operator rhs rest failure}
        (projected : assignment.target.projections ≠ [])
        (ready : ProjectedTarget.RootReady environment before assignment.target)
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
        ForItems program registry (stepSize [keysSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | projectedAssignmentGetterFault {keysSize : Nat} {scope context environment before after assignment operator rhs values rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) after)
        (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
        ForItems program registry (stepSize [keysSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after
    | projectedAssignmentRhsFault {keysSize childSize : Nat} {scope context environment before targetHeap after assignment operator rhs values target rest failure}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.fault failure) after) :
        ForItems program registry (stepSize [keysSize, childSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | projectedAssignmentWriteFault {keysSize childSize : Nat} {scope context environment before targetHeap after assignment operator rhs values target right rest reason}
        (projected : assignment.target.projections ≠ [])
        (keys : Expressions program registry keysSize scope context environment before
          (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
        (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
        (child : Expression program registry childSize scope context environment targetHeap rhs (.value right) after)
        (failed : ProjectedTarget.WriteFault operator target right after reason) :
        ForItems program registry (stepSize [keysSize, childSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault (.semantic reason)) after
    | assignment {childSize nextSize : Nat} {scope context finalContext environment before middle written after assignment operator rhs value target updated rest outcome}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : ForItems program registry nextSize scope context environment written rest finalContext outcome after) :
        ForItems program registry (stepSize [childSize, nextSize]) scope context environment before (.assignValue assignment operator rhs :: rest) finalContext outcome after
    | assignmentFailure {childSize : Nat} {scope context environment before after assignment operator rhs target rest failure}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.fault failure) after) :
        ForItems program registry (stepSize [childSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | assignmentOperands {childSize : Nat} {scope context environment before after assignment operator rhs target right
          currentCell initial currentSelected rest}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        ForItems program registry (stepSize [childSize]) scope context environment before (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | unbound {scope context environment heap assignment operator rhs rest}
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        ForItems program registry (stepSize []) scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | dangling {scope context environment heap assignment operator rhs rest location}
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        ForItems program registry (stepSize []) scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap

  /-- Finite for iteration runs each post header in the original loop scope.
  Body/post local bindings are restored, while their heap effects persist. -/    | bitNot {nextSize : Nat} {scope context finalContext environment before written after assignment target updated rest outcome}
        (snapshot : BareTarget environment before assignment.target target)
        (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
          before target updated written)
        (next : ForItems program registry nextSize scope context environment written rest finalContext outcome after) :
        ForItems program registry (stepSize [nextSize]) scope context environment before (.assignBitNot assignment :: rest) finalContext outcome after
    | bitNotFault {scope context environment before assignment rest reason}
        (bare : assignment.target.projections = [])
        (failed : SourcePlaceBitNotFaults program context scope.evidence scope.source environment
          before assignment.target reason before) :
        ForItems program registry (stepSize []) scope context environment before (.assignBitNot assignment :: rest) context
          (.fault (.semantic reason)) before


  inductive ForLoop (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → ExpressionId → List ForItemForm → List StatementId → BodyOutcome → Heap → Prop where
    | testFault {testSize : Nat} {scope context environment before after condition post body failure}
        (test : Expression program registry testSize scope context environment before condition (.fault failure) after) :
        ForLoop program registry (stepSize [testSize]) scope context environment before condition post body (.fault failure) after
    | finished {testSize : Nat} {scope context environment before after condition post body}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool false)) after) :
        ForLoop program registry (stepSize [testSize]) scope context environment before condition post body (.fallthrough environment) after
    | bodyFailure {testSize branchSize : Nat} {scope context innerContext environment before middle after condition post body failure}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.fault failure) after) :
        ForLoop program registry (stepSize [testSize, branchSize]) scope context environment before condition post body (.fault failure) after
    | returnedFromBody {testSize branchSize : Nat} {scope context innerContext environment before middle after condition post body value}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.returned value) after) :
        ForLoop program registry (stepSize [testSize, branchSize]) scope context environment before condition post body (.returned value) after
    | forBreakFromBody {testSize branchSize : Nat} {scope context innerContext environment before middle after condition post body innerEnvironment}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.breaking innerEnvironment) after) :
        ForLoop program registry (stepSize [testSize, branchSize]) scope context environment before condition post body (.fallthrough environment) after
    | postFailure {testSize branchSize postTraceSize : Nat} {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry postTraceSize scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry (stepSize [testSize, branchSize, postTraceSize]) scope context environment before condition post body (.fault failure) after
    | continuePostFailure {testSize branchSize postTraceSize : Nat} {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry postTraceSize scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry (stepSize [testSize, branchSize, postTraceSize]) scope context environment before condition post body (.fault failure) after
    | iterate {testSize branchSize postTraceSize nextSize : Nat} {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry postTraceSize scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry nextSize scope context environment postHeap condition post body outcome after) :
        ForLoop program registry (stepSize [testSize, branchSize, postTraceSize, nextSize]) scope context environment before condition post body outcome after

    | continueIterate {testSize branchSize postTraceSize nextSize : Nat} {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false branchSize scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry postTraceSize scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry nextSize scope context environment postHeap condition post body outcome after) :
        ForLoop program registry (stepSize [testSize, branchSize, postTraceSize, nextSize]) scope context environment before condition post body outcome after

  /-- The original form before its retained output path. Child expressions keep
  the same source scope, full requirements and actual coercion partition. -/
  inductive RawForm (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → ExpressionForm → List RequirementId →
      List SourceInference.CoercionStep → Outcome → Heap → Prop where
    | rawAtomicValue {scope context environment before after form requirements coercions value}
        (atomic : AtomicForm form)
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          form requirements coercions value after) :
        RawForm program registry (stepSize []) scope context environment before form requirements coercions (.value value) after
    | rawAtomicFault {scope context environment before after form requirements coercions reason}
        (atomic : AtomicForm form)
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          form requirements coercions reason after) :
        RawForm program registry (stepSize []) scope context environment before form requirements coercions (.fault (.semantic reason)) after
    | rawDirectArgumentsFault {childrenSize : Nat} {scope context environment before after callee arguments instantiation name failure requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry childrenSize scope context environment before arguments (.fault failure) after) :
        RawForm program registry (stepSize [childrenSize]) scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions (.fault failure) after
    | rawDirectApplied {childrenSize invocationSize : Nat} {scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry childrenSize scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements coercions instantiation.predicates evidence)
        (invocation : Applies program registry invocationSize scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        RawForm program registry (stepSize [childrenSize, invocationSize]) scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions outcome after

  /-- An actual conversion edge uses either the independent primitive rule or
  a selected method body in its authentic staged scope. -/
  inductive CoercionStep (program : Program) (registry : Registry) :
      Nat → Scope → Context → Heap → SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionPrimitive {scope context heap step input output}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (applies : CoercionApplies context step input output) :
        CoercionStep program registry (stepSize []) scope context heap step input (.value output) heap
    | coercionRequirement {scope context heap step input failed}
        (fault : RequirementListFaults context scope.evidence step.requirements failed) :
        CoercionStep program registry (stepSize []) scope context heap step input (.fault (.semantic (.unsatisfiedRequirement failed))) heap
    | coercionPrimitiveInput {scope context heap step input actual}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (invalid : PrimitiveCoercionInputInvalid step input)
        (actualType : ValueRuntimeType input actual) :
        CoercionStep program registry (stepSize []) scope context heap step input (.fault (.semantic (.typeMismatch step.source actual))) heap
    | coercionMethod {bodySize : Nat} {scope context before bound after step input bodyInstance dictionary roots child
          parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (method : OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
          step.requirements bodyInstance dictionary)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        CoercionStep program registry (stepSize [bodySize]) scope context before step input result after

  /-- Ordered retained edges stop at the first semantic or staged failure. -/
  inductive CoercionPath (program : Program) (registry : Registry) :
      Nat → Scope → Context → Heap → List SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionsNil {scope context heap value} :
        CoercionPath program registry (stepSize []) scope context heap [] value (.value value) heap
    | coercionsCons {headSize tailSize : Nat} {scope context before middle after step steps input converted outcome}
        (head : CoercionStep program registry headSize scope context before step input (.value converted) middle)
        (tail : CoercionPath program registry tailSize scope context middle steps converted outcome after) :
        CoercionPath program registry (stepSize [headSize, tailSize]) scope context before (step :: steps) input outcome after
    | coercionsFault {headSize : Nat} {scope context before after step steps input failure}
        (head : CoercionStep program registry headSize scope context before step input (.fault failure) after) :
        CoercionPath program registry (stepSize [headSize]) scope context before (step :: steps) input (.fault failure) after

end

abbrev Statements (program : Program) (registry : Registry) := StatementsIn program registry true
namespace Statements
export StatementsIn (breaking continuing ifBreaking ifContinuing blockBreaking blockContinuing matchBreaking matchContinuing nil returnUnit returnValue returnFault tail discard expressionFault
  assignProjected assignProjectedRootFault assignProjectedKeysFault assignProjectedGetterFault assignProjectedRhsFault assignProjectedWriteFault
  bitNotProjected bitNotProjectedRootFault bitNotProjectedKeysFault bitNotProjectedGetterFault
  bitNotBare bitNotBareFault assignBare assignBareFault assignBareOperands assignBareUnbound assignBareDangling letUninitialized letInitialized letFault
  ifConditionFault ifReturned ifFault ifFallthrough blockReturned blockFault blockFallthrough whileReturned whileFault whileFallthrough matchReturned matchFault matchFallthrough
  forInitializerFault forReturned forFault forFallthrough)
end Statements


/-! The four mutually recursive projections use the same rule handlers. -/
local macro "erase_stage_grade" : tactic =>
  `(tactic| (
    case breaking => apply Recursive.StatementsIn.breaking <;> assumption
    case ifBreaking => apply Recursive.StatementsIn.ifBreaking <;> assumption
    case blockBreaking => apply Recursive.StatementsIn.blockBreaking <;> assumption
    case matchBreaking => apply Recursive.StatementsIn.matchBreaking <;> assumption
    case continuing => apply Recursive.StatementsIn.continuing <;> assumption
    case ifContinuing => apply Recursive.StatementsIn.ifContinuing <;> assumption
    case blockContinuing => apply Recursive.StatementsIn.blockContinuing <;> assumption
    case matchContinuing => apply Recursive.StatementsIn.matchContinuing <;> assumption
    case breakFromBody => apply Recursive.While.breakFromBody <;> assumption
    case continueNext => apply Recursive.While.continueNext <;> assumption
    case forBreakFromBody => apply Recursive.ForLoop.forBreakFromBody <;> assumption
    case continuePostFailure => apply Recursive.ForLoop.continuePostFailure <;> assumption
    case continueIterate => apply Recursive.ForLoop.continueIterate <;> assumption
    case coercedValue => apply Recursive.Expression.coercedValue <;> assumption
    case coercedFault => apply Recursive.Expression.coercedFault <;> assumption
    case rawAtomicValue => apply Recursive.RawForm.rawAtomicValue <;> assumption
    case rawAtomicFault => apply Recursive.RawForm.rawAtomicFault <;> assumption
    case rawDirectArgumentsFault => apply Recursive.RawForm.rawDirectArgumentsFault <;> assumption
    case rawDirectApplied => apply Recursive.RawForm.rawDirectApplied <;> assumption
    case coercionPrimitive => apply Recursive.CoercionStep.coercionPrimitive <;> assumption
    case coercionRequirement => apply Recursive.CoercionStep.coercionRequirement <;> assumption
    case coercionPrimitiveInput => apply Recursive.CoercionStep.coercionPrimitiveInput <;> assumption
    case coercionMethod => apply Recursive.CoercionStep.coercionMethod <;> assumption
    case coercionsNil => apply Recursive.CoercionPath.coercionsNil <;> assumption
    case coercionsCons => apply Recursive.CoercionPath.coercionsCons <;> assumption
    case coercionsFault => apply Recursive.CoercionPath.coercionsFault <;> assumption
    case atomicValue => apply Recursive.Expression.atomicValue <;> assumption
    case atomicFault => apply Recursive.Expression.atomicFault <;> assumption
    case group => apply Recursive.Expression.group <;> assumption
    case pair => apply Recursive.Expression.pair <;> assumption
    case pairLeftFault => apply Recursive.Expression.pairLeftFault <;> assumption
    case pairRightFault => apply Recursive.Expression.pairRightFault <;> assumption
    case tupleValue => apply Recursive.Expression.tupleValue <;> assumption
    case tupleFault => apply Recursive.Expression.tupleFault <;> assumption
    case constructorValue => apply Recursive.Expression.constructorValue <;> assumption
    case constructorFault => apply Recursive.Expression.constructorFault <;> assumption
    case indexBaseFault => apply Recursive.Expression.indexBaseFault <;> assumption
    case indexKeyFault => apply Recursive.Expression.indexKeyFault <;> assumption
    case indexResult => apply Recursive.Expression.indexResult <;> assumption
    case unary => apply Recursive.Expression.unary <;> assumption
    case unaryOperandFault => apply Recursive.Expression.unaryOperandFault <;> assumption
    case unaryInvalid => apply Recursive.Expression.unaryInvalid <;> assumption
    case binaryLeftFault => apply Recursive.Expression.binaryLeftFault <;> assumption
    case binaryLeftInvalid => apply Recursive.Expression.binaryLeftInvalid <;> assumption
    case binaryShortCircuit => apply Recursive.Expression.binaryShortCircuit <;> assumption
    case binaryRightFault => apply Recursive.Expression.binaryRightFault <;> assumption
    case binary => apply Recursive.Expression.binary <;> assumption
    case binaryInvalid => apply Recursive.Expression.binaryInvalid <;> assumption
    case unaryMethod => apply Recursive.Expression.unaryMethod <;> assumption
    case binaryMethod => apply Recursive.Expression.binaryMethod <;> assumption
    case conditional => apply Recursive.Expression.conditional <;> assumption
    case conditionalFault => apply Recursive.Expression.conditionalFault <;> assumption
    case builtinArgumentsFault => apply Recursive.Expression.builtinArgumentsFault <;> assumption
    case builtinApplied => apply Recursive.Expression.builtinApplied <;> assumption
    case directArgumentsFault => apply Recursive.Expression.directArgumentsFault <;> assumption
    case directApplied => apply Recursive.Expression.directApplied <;> assumption
    case calleeFault => apply Recursive.Expression.calleeFault <;> assumption
    case notCallable => apply Recursive.Expression.notCallable <;> assumption
    case rejected => apply Recursive.Expression.rejected <;> assumption
    case argumentsFault => apply Recursive.Expression.argumentsFault <;> assumption
    case sourceArity => apply Recursive.Expression.sourceArity <;> assumption
    case applied => apply Recursive.Expression.applied <;> assumption
    case nil => apply Recursive.Expressions.nil <;> assumption
    case cons => apply Recursive.Expressions.cons <;> assumption
    case headFault => apply Recursive.Expressions.headFault <;> assumption
    case tailFault => apply Recursive.Expressions.tailFault <;> assumption
    case builtin => apply Recursive.Applies.builtin <;> assumption
    case builtinArity => apply Recursive.Applies.builtinArity <;> assumption
    case builtinType => apply Recursive.Applies.builtinType <;> assumption
    case closureArity => apply Recursive.Applies.closureArity <;> assumption
    case globalArity => apply Recursive.Applies.globalArity <;> assumption
    case global => apply Recursive.Applies.global <;> assumption
    case closure => apply Recursive.Applies.closure <;> assumption
    case nil => apply Recursive.StatementsIn.nil <;> assumption
    case returnUnit => apply Recursive.StatementsIn.returnUnit <;> assumption
    case returnValue => apply Recursive.StatementsIn.returnValue <;> assumption
    case returnFault => apply Recursive.StatementsIn.returnFault <;> assumption
    case tail => apply Recursive.StatementsIn.tail <;> assumption
    case discard => apply Recursive.StatementsIn.discard <;> assumption
    case discardValue => apply Recursive.StatementsIn.discardValue <;> assumption
    case ifConditionFault => apply Recursive.StatementsIn.ifConditionFault <;> assumption
    case ifReturned => apply Recursive.StatementsIn.ifReturned <;> assumption
    case ifFault => apply Recursive.StatementsIn.ifFault <;> assumption
    case ifFallthrough => apply Recursive.StatementsIn.ifFallthrough <;> assumption
    case expressionFault => apply Recursive.StatementsIn.expressionFault <;> assumption
    case bitNotBare => apply Recursive.StatementsIn.bitNotBare <;> assumption
    case bitNotBareFault => apply Recursive.StatementsIn.bitNotBareFault <;> assumption
    case bitNot => apply Recursive.ForItems.bitNot <;> assumption
    case bitNotFault => apply Recursive.ForItems.bitNotFault <;> assumption
    case bitNotProjected => apply Recursive.StatementsIn.bitNotProjected <;> assumption
    case bitNotProjectedRootFault => apply Recursive.StatementsIn.bitNotProjectedRootFault <;> assumption
    case bitNotProjectedKeysFault => apply Recursive.StatementsIn.bitNotProjectedKeysFault <;> assumption
    case bitNotProjectedGetterFault => apply Recursive.StatementsIn.bitNotProjectedGetterFault <;> assumption
    case assignProjected => apply Recursive.StatementsIn.assignProjected <;> assumption
    case assignProjectedRootFault => apply Recursive.StatementsIn.assignProjectedRootFault <;> assumption
    case assignProjectedKeysFault => apply Recursive.StatementsIn.assignProjectedKeysFault <;> assumption
    case assignProjectedGetterFault => apply Recursive.StatementsIn.assignProjectedGetterFault <;> assumption
    case assignProjectedRhsFault => apply Recursive.StatementsIn.assignProjectedRhsFault <;> assumption
    case assignProjectedWriteFault => apply Recursive.StatementsIn.assignProjectedWriteFault <;> assumption
    case projectedBitNot => apply Recursive.ForItems.projectedBitNot <;> assumption
    case projectedBitNotRootFault => apply Recursive.ForItems.projectedBitNotRootFault <;> assumption
    case projectedBitNotKeysFault => apply Recursive.ForItems.projectedBitNotKeysFault <;> assumption
    case projectedBitNotGetterFault => apply Recursive.ForItems.projectedBitNotGetterFault <;> assumption
    case projectedAssignment => apply Recursive.ForItems.projectedAssignment <;> assumption
    case projectedAssignmentRootFault => apply Recursive.ForItems.projectedAssignmentRootFault <;> assumption
    case projectedAssignmentKeysFault => apply Recursive.ForItems.projectedAssignmentKeysFault <;> assumption
    case projectedAssignmentGetterFault => apply Recursive.ForItems.projectedAssignmentGetterFault <;> assumption
    case projectedAssignmentRhsFault => apply Recursive.ForItems.projectedAssignmentRhsFault <;> assumption
    case projectedAssignmentWriteFault => apply Recursive.ForItems.projectedAssignmentWriteFault <;> assumption
    case assignBare => apply Recursive.StatementsIn.assignBare <;> assumption
    case assignBareFault => apply Recursive.StatementsIn.assignBareFault <;> assumption
    case assignBareOperands => apply Recursive.StatementsIn.assignBareOperands <;> assumption
    case assignBareUnbound => apply Recursive.StatementsIn.assignBareUnbound <;> assumption
    case assignBareDangling => apply Recursive.StatementsIn.assignBareDangling <;> assumption
    case letUninitialized => apply Recursive.StatementsIn.letUninitialized <;> assumption
    case letInitialized => apply Recursive.StatementsIn.letInitialized <;> assumption
    case letFault => apply Recursive.StatementsIn.letFault <;> assumption
    case blockReturned => apply Recursive.StatementsIn.blockReturned <;> assumption
    case blockFault => apply Recursive.StatementsIn.blockFault <;> assumption
    case blockFallthrough => apply Recursive.StatementsIn.blockFallthrough <;> assumption
    case whileReturned => apply Recursive.StatementsIn.whileReturned <;> assumption
    case whileFault => apply Recursive.StatementsIn.whileFault <;> assumption
    case whileFallthrough => apply Recursive.StatementsIn.whileFallthrough <;> assumption
    case done => apply Recursive.While.done <;> assumption
    case conditionFault => apply Recursive.While.conditionFault <;> assumption
    case returned => apply Recursive.While.returned <;> assumption
    case bodyFault => apply Recursive.While.bodyFault <;> assumption
    case next => apply Recursive.While.next <;> assumption
    case matchReturned => apply Recursive.StatementsIn.matchReturned <;> assumption
    case matchFault => apply Recursive.StatementsIn.matchFault <;> assumption
    case matchFallthrough => apply Recursive.StatementsIn.matchFallthrough <;> assumption
    case forInitializerFault => apply Recursive.StatementsIn.forInitializerFault <;> assumption
    case forReturned => apply Recursive.StatementsIn.forReturned <;> assumption
    case forFault => apply Recursive.StatementsIn.forFault <;> assumption
    case forFallthrough => apply Recursive.StatementsIn.forFallthrough <;> assumption
    case scrutineeFault => apply Recursive.Match.scrutineeFault <;> assumption
    case patternFault => apply Recursive.Match.patternFault <;> assumption
    case arm => apply Recursive.Match.arm <;> assumption
    case default => apply Recursive.Match.default <;> assumption
    case noBranch => apply Recursive.Match.noBranch <;> assumption
    case empty => apply Recursive.ForItems.empty <;> assumption
    case absent => apply Recursive.ForItems.absent <;> assumption
    case initialized => apply Recursive.ForItems.initialized <;> assumption
    case initializerFault => apply Recursive.ForItems.initializerFault <;> assumption
    case expression => apply Recursive.ForItems.expression <;> assumption
    case expressionFailure => apply Recursive.ForItems.expressionFailure <;> assumption
    case assignment => apply Recursive.ForItems.assignment <;> assumption
    case assignmentFailure => apply Recursive.ForItems.assignmentFailure <;> assumption
    case assignmentOperands => apply Recursive.ForItems.assignmentOperands <;> assumption
    case unbound => apply Recursive.ForItems.unbound <;> assumption
    case dangling => apply Recursive.ForItems.dangling <;> assumption
    case testFault => apply Recursive.ForLoop.testFault <;> assumption
    case finished => apply Recursive.ForLoop.finished <;> assumption
    case bodyFailure => apply Recursive.ForLoop.bodyFailure <;> assumption
    case returnedFromBody => apply Recursive.ForLoop.returnedFromBody <;> assumption
    case postFailure => apply Recursive.ForLoop.postFailure <;> assumption
    case iterate => apply Recursive.ForLoop.iterate <;> assumption
  ))

local macro "construct_stage_grade" : tactic =>
  `(tactic| (
    case breaking contains form =>
      exact ⟨_, .breaking contains form⟩
    case ifBreaking contains form test branch testIH branchIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_branch⟩ := branchIH
      exact ⟨_, .ifBreaking contains form graded_test graded_branch⟩
    case blockBreaking contains form inner innerIH =>
      obtain ⟨_, graded_inner⟩ := innerIH
      exact ⟨_, .blockBreaking contains form graded_inner⟩
    case matchBreaking contains form matched matchedIH =>
      obtain ⟨_, graded_matched⟩ := matchedIH
      exact ⟨_, .matchBreaking contains form graded_matched⟩
    case continuing contains form =>
      exact ⟨_, .continuing contains form⟩
    case ifContinuing contains form test branch testIH branchIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_branch⟩ := branchIH
      exact ⟨_, .ifContinuing contains form graded_test graded_branch⟩
    case blockContinuing contains form inner innerIH =>
      obtain ⟨_, graded_inner⟩ := innerIH
      exact ⟨_, .blockContinuing contains form graded_inner⟩
    case matchContinuing contains form matched matchedIH =>
      obtain ⟨_, graded_matched⟩ := matchedIH
      exact ⟨_, .matchContinuing contains form graded_matched⟩
    case breakFromBody test body testIH bodyIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_body⟩ := bodyIH
      exact ⟨_, .breakFromBody graded_test graded_body⟩
    case continueNext test body next testIH bodyIH nextIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_body⟩ := bodyIH
      obtain ⟨_, graded_next⟩ := nextIH
      exact ⟨_, .continueNext graded_test graded_body graded_next⟩
    case forBreakFromBody test branch testIH branchIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_branch⟩ := branchIH
      exact ⟨_, .forBreakFromBody graded_test graded_branch⟩
    case continuePostFailure test branch postTrace testIH branchIH postTraceIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_branch⟩ := branchIH
      obtain ⟨_, graded_postTrace⟩ := postTraceIH
      exact ⟨_, .continuePostFailure graded_test graded_branch graded_postTrace⟩
    case continueIterate test branch postTrace next testIH branchIH postTraceIH nextIH =>
      obtain ⟨_, graded_test⟩ := testIH
      obtain ⟨_, graded_branch⟩ := branchIH
      obtain ⟨_, graded_postTrace⟩ := postTraceIH
      obtain ⟨_, graded_next⟩ := nextIH
      exact ⟨_, .continueIterate graded_test graded_branch graded_postTrace graded_next⟩
    case coercedValue contains nonempty raw path rawIH pathIH =>
      obtain ⟨_, graded_raw⟩ := rawIH
      obtain ⟨_, graded_path⟩ := pathIH
      exact ⟨_, .coercedValue contains nonempty graded_raw graded_path⟩
    case coercedFault contains nonempty raw rawIH =>
      obtain ⟨_, graded_raw⟩ := rawIH
      exact ⟨_, .coercedFault contains nonempty graded_raw⟩
    case rawAtomicValue atomic valueRule =>
      exact ⟨_, .rawAtomicValue atomic valueRule⟩
    case rawAtomicFault atomic faultRule =>
      exact ⟨_, .rawAtomicFault atomic faultRule⟩
    case rawDirectArgumentsFault calleeOccurrence children childrenIH =>
      obtain ⟨_, graded_children⟩ := childrenIH
      exact ⟨_, .rawDirectArgumentsFault calleeOccurrence graded_children⟩
    case rawDirectApplied calleeOccurrence valid children callEvidence invocation childrenIH invocationIH =>
      obtain ⟨_, graded_children⟩ := childrenIH
      obtain ⟨_, graded_invocation⟩ := invocationIH
      exact ⟨_, .rawDirectApplied calleeOccurrence valid graded_children callEvidence graded_invocation⟩
    case coercionPrimitive noSourceMethod applies =>
      exact ⟨_, .coercionPrimitive noSourceMethod applies⟩
    case coercionRequirement fault =>
      exact ⟨_, .coercionRequirement fault⟩
    case coercionPrimitiveInput noSourceMethod invalid actualType =>
      exact ⟨_, .coercionPrimitiveInput noSourceMethod invalid actualType⟩
    case coercionMethod method rootsEq selected parameters allocate body resultRule bodyIH =>
      obtain ⟨_, graded_body⟩ := bodyIH
      exact ⟨_, .coercionMethod method rootsEq selected parameters allocate graded_body resultRule⟩
    case coercionsNil  =>
      exact ⟨_, .coercionsNil⟩
    case coercionsCons head tail headIH tailIH =>
      obtain ⟨_, graded_head⟩ := headIH
      obtain ⟨_, graded_tail⟩ := tailIH
      exact ⟨_, .coercionsCons graded_head graded_tail⟩
    case coercionsFault head headIH =>
      obtain ⟨_, graded_head⟩ := headIH
      exact ⟨_, .coercionsFault graded_head⟩
    case atomicValue contains atomic uncoerced valueRule =>
      exact ⟨_, .atomicValue contains atomic uncoerced valueRule⟩
    case atomicFault contains atomic uncoerced faultRule =>
      exact ⟨_, .atomicFault contains atomic uncoerced faultRule⟩
    case group occurrence child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .group occurrence graded_child⟩
    case pair occurrence first second ih_first ih_second =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      obtain ⟨secondSize, graded_second⟩ := ih_second
      exact ⟨_, .pair occurrence graded_first graded_second⟩
    case pairLeftFault occurrence child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .pairLeftFault occurrence graded_child⟩
    case pairRightFault occurrence first second ih_first ih_second =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      obtain ⟨secondSize, graded_second⟩ := ih_second
      exact ⟨_, .pairRightFault occurrence graded_first graded_second⟩
    case tupleValue occurrence children pack ih_children =>
      obtain ⟨childrenSize, graded_children⟩ := ih_children
      exact ⟨_, .tupleValue occurrence graded_children pack⟩
    case tupleFault occurrence children ih_children =>
      obtain ⟨childrenSize, graded_children⟩ := ih_children
      exact ⟨_, .tupleFault occurrence graded_children⟩
    case constructorValue occurrence valid children ih_children =>
      obtain ⟨_, graded_children⟩ := ih_children
      exact ⟨_, .constructorValue occurrence valid graded_children⟩
    case constructorFault occurrence children ih_children =>
      obtain ⟨_, graded_children⟩ := ih_children
      exact ⟨_, .constructorFault occurrence graded_children⟩
    case indexBaseFault occurrence first ih_first =>
      obtain ⟨_, first⟩ := ih_first
      exact ⟨_, .indexBaseFault occurrence first⟩
    case indexKeyFault occurrence first second ih_first ih_second =>
      obtain ⟨_, first⟩ := ih_first
      obtain ⟨_, second⟩ := ih_second
      exact ⟨_, .indexKeyFault occurrence first second⟩
    case indexResult occurrence first second result ih_first ih_second =>
      obtain ⟨_, first⟩ := ih_first
      obtain ⟨_, second⟩ := ih_second
      exact ⟨_, .indexResult occurrence first second result⟩
    case unary occurrence child applies ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .unary occurrence graded_child applies⟩
    case unaryOperandFault occurrence child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .unaryOperandFault occurrence graded_child⟩
    case unaryInvalid occurrence child invalid ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .unaryInvalid occurrence graded_child invalid⟩
    case binaryLeftFault occurrence first ih_first =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      exact ⟨_, .binaryLeftFault occurrence graded_first⟩
    case binaryLeftInvalid occurrence first invalid ih_first =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      exact ⟨_, .binaryLeftInvalid occurrence graded_first invalid⟩
    case binaryShortCircuit occurrence first circuit ih_first =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      exact ⟨_, .binaryShortCircuit occurrence graded_first circuit⟩
    case binaryRightFault occurrence first continues second ih_first ih_second =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      obtain ⟨secondSize, graded_second⟩ := ih_second
      exact ⟨_, .binaryRightFault occurrence graded_first continues graded_second⟩
    case binary occurrence first continues second applies ih_first ih_second =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      obtain ⟨secondSize, graded_second⟩ := ih_second
      exact ⟨_, .binary occurrence graded_first continues graded_second applies⟩
    case binaryInvalid occurrence first continues second invalid ih_first ih_second =>
      obtain ⟨firstSize, graded_first⟩ := ih_first
      obtain ⟨secondSize, graded_second⟩ := ih_second
      exact ⟨_, .binaryInvalid occurrence graded_first continues graded_second invalid⟩
    case unaryMethod occurrence dispatch method operand rootsEq selected parameters allocate body resultRule operandIH bodyIH =>
      obtain ⟨operandSize, gradedOperand⟩ := operandIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .unaryMethod occurrence dispatch method gradedOperand rootsEq selected parameters allocate gradedBody resultRule⟩
    case binaryMethod occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule firstIH secondIH bodyIH =>
      obtain ⟨leftSize, gradedFirst⟩ := firstIH
      obtain ⟨rightSize, gradedSecond⟩ := secondIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .binaryMethod occurrence dispatch method gradedFirst continues gradedSecond rootsEq selected parameters allocate gradedBody resultRule⟩
    case conditional occurrence test branch ih_test ih_branch =>
      obtain ⟨testSize, graded_test⟩ := ih_test
      obtain ⟨branchSize, graded_branch⟩ := ih_branch
      exact ⟨_, .conditional occurrence graded_test graded_branch⟩
    case conditionalFault occurrence test ih_test =>
      obtain ⟨testSize, graded_test⟩ := ih_test
      exact ⟨_, .conditionalFault occurrence graded_test⟩
    case builtinArgumentsFault occurrence children ih_children =>
      obtain ⟨_, graded_children⟩ := ih_children
      exact ⟨_, .builtinArgumentsFault occurrence graded_children⟩
    case builtinApplied occurrence children invocation ih_children ih_invocation =>
      obtain ⟨_, graded_children⟩ := ih_children
      obtain ⟨_, graded_invocation⟩ := ih_invocation
      exact ⟨_, .builtinApplied occurrence graded_children graded_invocation⟩
    case directArgumentsFault occurrence calleeOccurrence children ih_children =>
      obtain ⟨_, graded_children⟩ := ih_children
      exact ⟨_, .directArgumentsFault occurrence calleeOccurrence graded_children⟩
    case directApplied occurrence calleeOccurrence valid children callEvidence invocation ih_children ih_invocation =>
      obtain ⟨_, graded_children⟩ := ih_children
      obtain ⟨_, graded_invocation⟩ := ih_invocation
      exact ⟨_, .directApplied occurrence calleeOccurrence valid graded_children callEvidence graded_invocation⟩
    case calleeFault occurrence child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .calleeFault occurrence graded_child⟩
    case notCallable occurrence child invalid ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .notCallable occurrence graded_child invalid⟩
    case rejected occurrence child guard ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .rejected occurrence graded_child guard⟩
    case argumentsFault occurrence child guard children ih_child ih_children =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨childrenSize, graded_children⟩ := ih_children
      exact ⟨_, .argumentsFault occurrence graded_child guard graded_children⟩
    case sourceArity occurrence child guard children mismatch ih_child ih_children =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨childrenSize, graded_children⟩ := ih_children
      exact ⟨_, .sourceArity occurrence graded_child guard graded_children mismatch⟩
    case applied occurrence uncoerced child guard children arity invocation ih_child ih_children ih_invocation =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨childrenSize, graded_children⟩ := ih_children
      obtain ⟨invocationSize, graded_invocation⟩ := ih_invocation
      exact ⟨_, .applied occurrence uncoerced graded_child guard graded_children arity graded_invocation⟩
    case nil =>
      exact ⟨_, .nil⟩
    case cons head tail ih_head ih_tail =>
      obtain ⟨headSize, graded_head⟩ := ih_head
      obtain ⟨tailSize, graded_tail⟩ := ih_tail
      exact ⟨_, .cons graded_head graded_tail⟩
    case headFault head ih_head =>
      obtain ⟨headSize, graded_head⟩ := ih_head
      exact ⟨_, .headFault graded_head⟩
    case tailFault head tail ih_head ih_tail =>
      obtain ⟨headSize, graded_head⟩ := ih_head
      obtain ⟨tailSize, graded_tail⟩ := ih_tail
      exact ⟨_, .tailFault graded_head graded_tail⟩
    case builtin primitive =>
      exact ⟨_, .builtin primitive⟩
    case builtinArity mismatch =>
      exact ⟨_, .builtinArity mismatch⟩
    case builtinType arity mismatch =>
      exact ⟨_, .builtinType arity mismatch⟩
    case closureArity mismatch =>
      exact ⟨_, .closureArity mismatch⟩
    case globalArity instantiates mismatch =>
      exact ⟨_, .globalArity instantiates mismatch⟩
    case global instantiates covers rootsEq selected parameters allocate body resultRule ih_body =>
      obtain ⟨bodySize, graded_body⟩ := ih_body
      exact ⟨_, .global instantiates covers rootsEq selected parameters allocate graded_body resultRule⟩
    case closure selected valid parameters allocate body resultRule ih_body =>
      obtain ⟨bodySize, graded_body⟩ := ih_body
      exact ⟨_, .closure selected valid parameters allocate graded_body resultRule⟩
    case nil =>
      exact ⟨_, .nil⟩
    case returnUnit contains form =>
      exact ⟨_, .returnUnit contains form⟩
    case returnValue contains form child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .returnValue contains form graded_child⟩
    case returnFault contains form child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .returnFault contains form graded_child⟩
    case tail contains form child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .tail contains form graded_child⟩
    case discard contains form child next ih_child ih_next =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨nextSize, graded_next⟩ := ih_next
      exact ⟨_, .discard contains form graded_child graded_next⟩
    case discardValue contains form child next ih_child ih_next =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨nextSize, graded_next⟩ := ih_next
      exact ⟨_, .discardValue contains form graded_child graded_next⟩
    case ifConditionFault contains form test ih =>
      obtain ⟨testSize, graded⟩ := ih
      exact ⟨_, .ifConditionFault contains form graded⟩
    case ifReturned contains form test branch testIH branchIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨branchSize, gradedBranch⟩ := branchIH
      exact ⟨_, .ifReturned contains form gradedTest gradedBranch⟩
    case ifFault contains form test branch testIH branchIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨branchSize, gradedBranch⟩ := branchIH
      exact ⟨_, .ifFault contains form gradedTest gradedBranch⟩
    case ifFallthrough contains form test branch next testIH branchIH nextIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨branchSize, gradedBranch⟩ := branchIH
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .ifFallthrough contains form gradedTest gradedBranch gradedNext⟩
    case expressionFault contains form child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .expressionFault contains form graded_child⟩
    case bitNotBare contains form snapshot write next nextIH =>
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .bitNotBare contains form snapshot write gradedNext⟩
    case bitNotBareFault contains form bare failed =>
      exact ⟨_, .bitNotBareFault contains form bare failed⟩
    case bitNot snapshot write next nextIH =>
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .bitNot snapshot write gradedNext⟩
    case bitNotFault bare failed => exact ⟨_, .bitNotFault bare failed⟩
    case bitNotProjected contains form projected keys snapshot write next keysIH nextIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .bitNotProjected contains form projected keysGraded snapshot write nextGraded⟩
    case bitNotProjectedRootFault contains form projected failed =>
      exact ⟨_, .bitNotProjectedRootFault contains form projected failed⟩
    case bitNotProjectedKeysFault contains form projected ready keys keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .bitNotProjectedKeysFault contains form projected ready keysGraded⟩
    case bitNotProjectedGetterFault contains form projected keys failed keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .bitNotProjectedGetterFault contains form projected keysGraded failed⟩
    case assignProjected contains form projected keys snapshot child write next keysIH childIH nextIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .assignProjected contains form projected keysGraded snapshot childGraded write nextGraded⟩
    case assignProjectedRootFault contains form projected failed =>
      exact ⟨_, .assignProjectedRootFault contains form projected failed⟩
    case assignProjectedKeysFault contains form projected ready keys keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .assignProjectedKeysFault contains form projected ready keysGraded⟩
    case assignProjectedGetterFault contains form projected keys failed keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .assignProjectedGetterFault contains form projected keysGraded failed⟩
    case assignProjectedRhsFault contains form projected keys snapshot child keysIH childIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignProjectedRhsFault contains form projected keysGraded snapshot childGraded⟩
    case assignProjectedWriteFault contains form projected keys snapshot child failed keysIH childIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignProjectedWriteFault contains form projected keysGraded snapshot childGraded failed⟩
    case assignBare contains form snapshot child write next childIH nextIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .assignBare contains form snapshot childGraded write nextGraded⟩
    case assignBareFault contains form snapshot child childIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignBareFault contains form snapshot childGraded⟩
    case assignBareOperands contains form snapshot child currentRead rootType initialValue pathRead invalid childIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignBareOperands contains form snapshot childGraded currentRead rootType initialValue pathRead invalid⟩
    case assignBareUnbound contains form bare missing =>
      exact ⟨_, .assignBareUnbound contains form bare missing⟩
    case assignBareDangling contains form bare lookup missing =>
      exact ⟨_, .assignBareDangling contains form bare lookup missing⟩
    case letUninitialized contains form monomorphic extension allocate next ih_next =>
      obtain ⟨nextSize, graded_next⟩ := ih_next
      exact ⟨_, .letUninitialized contains form monomorphic extension allocate graded_next⟩
    case letInitialized contains form child monomorphic extension allocate next ih_child ih_next =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      obtain ⟨nextSize, graded_next⟩ := ih_next
      exact ⟨_, .letInitialized contains form graded_child monomorphic extension allocate graded_next⟩
    case letFault contains form monomorphic child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .letFault contains form monomorphic graded_child⟩
    case blockReturned contains form inner ih | blockFault contains form inner ih =>
      obtain ⟨innerSize, graded⟩ := ih
      first | exact ⟨_, .blockReturned contains form graded⟩ | exact ⟨_, .blockFault contains form graded⟩
    case blockFallthrough contains form inner next innerIH nextIH =>
      obtain ⟨innerSize, gradedInner⟩ := innerIH
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .blockFallthrough contains form gradedInner gradedNext⟩
    case whileReturned contains form loop ih | whileFault contains form loop ih =>
      obtain ⟨loopSize, graded⟩ := ih
      first | exact ⟨_, .whileReturned contains form graded⟩ | exact ⟨_, .whileFault contains form graded⟩
    case whileFallthrough contains form loop next loopIH nextIH =>
      obtain ⟨loopSize, gradedLoop⟩ := loopIH
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .whileFallthrough contains form gradedLoop gradedNext⟩
    case done test ih =>
      obtain ⟨testSize, graded⟩ := ih
      exact ⟨_, .done graded⟩
    case conditionFault test ih =>
      obtain ⟨testSize, graded⟩ := ih
      exact ⟨_, .conditionFault graded⟩
    case returned test body testIH bodyIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .returned gradedTest gradedBody⟩
    case bodyFault test body testIH bodyIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .bodyFault gradedTest gradedBody⟩
    case next test body next testIH bodyIH nextIH =>
      obtain ⟨testSize, gradedTest⟩ := testIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .next gradedTest gradedBody gradedNext⟩
    case matchReturned contains form matched ih | matchFault contains form matched ih =>
      obtain ⟨matchSize, graded⟩ := ih
      first | exact ⟨_, .matchReturned contains form graded⟩ | exact ⟨_, .matchFault contains form graded⟩
    case matchFallthrough contains form matched next matchIH nextIH =>
      obtain ⟨matchSize, gradedMatch⟩ := matchIH
      obtain ⟨nextSize, gradedNext⟩ := nextIH
      exact ⟨_, .matchFallthrough contains form gradedMatch gradedNext⟩
    case scrutineeFault scrutinee ih =>
      obtain ⟨scrutineeSize, graded⟩ := ih
      exact ⟨_, .scrutineeFault graded⟩
    case patternFault contains scrutinee allocated invalid ih =>
      obtain ⟨scrutineeSize, graded⟩ := ih
      exact ⟨_, .patternFault contains graded allocated invalid⟩
    case arm contains scrutinee hidden selected extended allocated body scrutineeIH bodyIH =>
      obtain ⟨scrutineeSize, gradedScrutinee⟩ := scrutineeIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .arm contains gradedScrutinee hidden selected extended allocated gradedBody⟩
    case default contains scrutinee hidden selected body scrutineeIH bodyIH =>
      obtain ⟨scrutineeSize, gradedScrutinee⟩ := scrutineeIH
      obtain ⟨bodySize, gradedBody⟩ := bodyIH
      exact ⟨_, .default contains gradedScrutinee hidden selected gradedBody⟩
    case noBranch contains scrutinee hidden selected ih =>
      obtain ⟨scrutineeSize, graded⟩ := ih
      exact ⟨_, .noBranch contains graded hidden selected⟩
    case forInitializerFault contains form initial initialIH =>
      obtain ⟨initialSize, gradedinitial⟩ := initialIH
      exact ⟨_, .forInitializerFault contains form gradedinitial⟩
    case forReturned contains form initial loop initialIH loopIH =>
      obtain ⟨initialSize, gradedinitial⟩ := initialIH
      obtain ⟨loopSize, gradedloop⟩ := loopIH
      exact ⟨_, .forReturned contains form gradedinitial gradedloop⟩
    case forFault contains form initial loop initialIH loopIH =>
      obtain ⟨initialSize, gradedinitial⟩ := initialIH
      obtain ⟨loopSize, gradedloop⟩ := loopIH
      exact ⟨_, .forFault contains form gradedinitial gradedloop⟩
    case forFallthrough contains form initial loop next initialIH loopIH nextIH =>
      obtain ⟨initialSize, gradedinitial⟩ := initialIH
      obtain ⟨loopSize, gradedloop⟩ := loopIH
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .forFallthrough contains form gradedinitial gradedloop gradednext⟩
    case empty =>
      exact ⟨_, .empty⟩
    case absent monomorphic extension allocate next nextIH =>
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .absent monomorphic extension allocate gradednext⟩
    case initialized monomorphic extension child allocate next childIH nextIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .initialized monomorphic extension gradedchild allocate gradednext⟩
    case initializerFault monomorphic child childIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      exact ⟨_, .initializerFault monomorphic gradedchild⟩
    case expression child next childIH nextIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .expression gradedchild gradednext⟩
    case expressionFailure child childIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      exact ⟨_, .expressionFailure gradedchild⟩
    case projectedBitNot projected keys snapshot write next keysIH nextIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .projectedBitNot projected keysGraded snapshot write nextGraded⟩
    case projectedBitNotRootFault projected failed =>
      exact ⟨_, .projectedBitNotRootFault projected failed⟩
    case projectedBitNotKeysFault projected ready keys keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .projectedBitNotKeysFault projected ready keysGraded⟩
    case projectedBitNotGetterFault projected keys failed keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .projectedBitNotGetterFault projected keysGraded failed⟩
    case projectedAssignment projected keys snapshot child write next keysIH childIH nextIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .projectedAssignment projected keysGraded snapshot childGraded write nextGraded⟩
    case projectedAssignmentRootFault projected failed =>
      exact ⟨_, .projectedAssignmentRootFault projected failed⟩
    case projectedAssignmentKeysFault projected ready keys keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .projectedAssignmentKeysFault projected ready keysGraded⟩
    case projectedAssignmentGetterFault projected keys failed keysIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      exact ⟨_, .projectedAssignmentGetterFault projected keysGraded failed⟩
    case projectedAssignmentRhsFault projected keys snapshot child keysIH childIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .projectedAssignmentRhsFault projected keysGraded snapshot childGraded⟩
    case projectedAssignmentWriteFault projected keys snapshot child failed keysIH childIH =>
      obtain ⟨keysSize, keysGraded⟩ := keysIH
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .projectedAssignmentWriteFault projected keysGraded snapshot childGraded failed⟩
    case assignment snapshot child write next childIH nextIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .assignment snapshot gradedchild write gradednext⟩
    case assignmentFailure snapshot child childIH =>
      obtain ⟨childSize, gradedchild⟩ := childIH
      exact ⟨_, .assignmentFailure snapshot gradedchild⟩
    case assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid childIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignmentOperands snapshot childGraded currentRead rootType initialValue pathRead invalid⟩
    case unbound bare missing =>
      exact ⟨_, .unbound bare missing⟩
    case dangling bare lookup missing =>
      exact ⟨_, .dangling bare lookup missing⟩
    case testFault test testIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      exact ⟨_, .testFault gradedtest⟩
    case finished test testIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      exact ⟨_, .finished gradedtest⟩
    case bodyFailure test branch testIH branchIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      obtain ⟨branchSize, gradedbranch⟩ := branchIH
      exact ⟨_, .bodyFailure gradedtest gradedbranch⟩
    case returnedFromBody test branch testIH branchIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      obtain ⟨branchSize, gradedbranch⟩ := branchIH
      exact ⟨_, .returnedFromBody gradedtest gradedbranch⟩
    case postFailure test branch postTrace testIH branchIH postTraceIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      obtain ⟨branchSize, gradedbranch⟩ := branchIH
      obtain ⟨postTraceSize, gradedpostTrace⟩ := postTraceIH
      exact ⟨_, .postFailure gradedtest gradedbranch gradedpostTrace⟩
    case iterate test branch postTrace next testIH branchIH postTraceIH nextIH =>
      obtain ⟨testSize, gradedtest⟩ := testIH
      obtain ⟨branchSize, gradedbranch⟩ := branchIH
      obtain ⟨postTraceSize, gradedpostTrace⟩ := postTraceIH
      obtain ⟨nextSize, gradednext⟩ := nextIH
      exact ⟨_, .iterate gradedtest gradedbranch gradedpostTrace gradednext⟩
  ))

theorem Expression.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry size scope context environment before id outcome after) :
    Recursive.Expression program registry scope context environment before id outcome after := by
  induction trace using Expression.rec
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem Expressions.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Expressions program registry size scope context environment before ids outcome after) :
    Recursive.Expressions program registry scope context environment before ids outcome after := by
  induction trace using Expressions.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem Applies.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {before after : Heap}
    {function : Value} {arguments : List Value} {outcome : Outcome}
    (trace : Applies program registry size scope context before function arguments outcome after) :
    Recursive.Applies program registry scope context before function arguments outcome after := by
  induction trace using Applies.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem StatementsIn.sound {mode : Bool} {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : StatementsIn program registry mode size scope context environment before roots finalContext outcome after) :
    Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after := by
  induction trace using StatementsIn.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem Expression.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {outcome : Outcome}
    (trace : Recursive.Expression program registry scope context environment before id outcome after) :
    ∃ size, Expression program registry size scope context environment before id outcome after := by
  induction trace using Recursive.Expression.rec
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem Expressions.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Recursive.Expressions program registry scope context environment before ids outcome after) :
    ∃ size, Expressions program registry size scope context environment before ids outcome after := by
  induction trace using Recursive.Expressions.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem Applies.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap}
    {function : Value} {arguments : List Value} {outcome : Outcome}
    (trace : Recursive.Applies program registry scope context before function arguments outcome after) :
    ∃ size, Applies program registry size scope context before function arguments outcome after := by
  induction trace using Recursive.Applies.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem StatementsIn.of_trace {mode : Bool} {program : Program} {registry : Registry}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after) :
    ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after := by
  induction trace using Recursive.StatementsIn.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem While.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : BodyOutcome}
    (trace : While program registry size scope context environment before condition statements outcome after) :
    Recursive.While program registry scope context environment before condition statements outcome after := by
  induction trace using While.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem While.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : BodyOutcome}
    (trace : Recursive.While program registry scope context environment before condition statements outcome after) :
    ∃ size, While program registry size scope context environment before condition statements outcome after := by
  induction trace using Recursive.While.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

/-- Preserve the original true-mode field-notation API. -/
theorem Statements.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : Statements program registry size scope context environment before roots finalContext outcome after) :
    Recursive.Statements program registry scope context environment before roots finalContext outcome after :=
  StatementsIn.sound trace

theorem Statements.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : Recursive.Statements program registry scope context environment before roots finalContext outcome after) :
    ∃ size, Statements program registry size scope context environment before roots finalContext outcome after :=
  StatementsIn.of_trace trace

theorem Match.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {resolution : MatchResolution} {outcome : BodyOutcome}
    (trace : Match program registry size scope context environment before resolution outcome after) :
    Recursive.Match program registry scope context environment before resolution outcome after := by
  induction trace using Match.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem Match.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {resolution : MatchResolution} {outcome : BodyOutcome}
    (trace : Recursive.Match program registry scope context environment before resolution outcome after) :
    ∃ size, Match program registry size scope context environment before resolution outcome after := by
  induction trace using Recursive.Match.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem ForItems.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {items : List ForItemForm} {outcome : ForItemsOutcome}
    (trace : ForItems program registry size scope context environment before items finalContext outcome after) :
    Recursive.ForItems program registry scope context environment before items finalContext outcome after := by
  induction trace using ForItems.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem ForItems.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {items : List ForItemForm} {outcome : ForItemsOutcome}
    (trace : Recursive.ForItems program registry scope context environment before items finalContext outcome after) :
    ∃ size, ForItems program registry size scope context environment before items finalContext outcome after := by
  induction trace using Recursive.ForItems.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem ForLoop.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {outcome : BodyOutcome}
    (trace : ForLoop program registry size scope context environment before condition post body outcome after) :
    Recursive.ForLoop program registry scope context environment before condition post body outcome after := by
  induction trace using ForLoop.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem ForLoop.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {outcome : BodyOutcome}
    (trace : Recursive.ForLoop program registry scope context environment before condition post body outcome after) :
    ∃ size, ForLoop program registry size scope context environment before condition post body outcome after := by
  induction trace using Recursive.ForLoop.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem RawForm.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    (trace : RawForm program registry size scope context environment before form requirements coercions outcome after) :
    Recursive.RawForm program registry scope context environment before form requirements coercions outcome after := by
  induction trace using RawForm.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem RawForm.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    (trace : Recursive.RawForm program registry scope context environment before form requirements coercions outcome after) :
    ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after := by
  induction trace using Recursive.RawForm.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem CoercionStep.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionStep program registry size scope context before step input outcome after) :
    Recursive.CoercionStep program registry scope context before step input outcome after := by
  induction trace using CoercionStep.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_11 := fun _ scope context before steps input outcome after _ => Recursive.CoercionPath program registry scope context before steps input outcome after)
  erase_stage_grade

theorem CoercionStep.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : Recursive.CoercionStep program registry scope context before step input outcome after) :
    ∃ size, CoercionStep program registry size scope context before step input outcome after := by
  induction trace using Recursive.CoercionStep.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => ∃ size, CoercionPath program registry size scope context before steps input outcome after)
  construct_stage_grade

theorem CoercionPath.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionPath program registry size scope context before steps input outcome after) :
    Recursive.CoercionPath program registry scope context before steps input outcome after := by
  induction trace using CoercionPath.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun mode _ scope context environment before roots finalContext outcome after _ => Recursive.StatementsIn program registry mode scope context environment before roots finalContext outcome after)
    (motive_5 := fun _ scope context environment before condition statements outcome after _ => Recursive.While program registry scope context environment before condition statements outcome after)
    (motive_6 := fun _ scope context environment before resolution outcome after _ => Recursive.Match program registry scope context environment before resolution outcome after)
    (motive_7 := fun _ scope context environment before items finalContext outcome after _ => Recursive.ForItems program registry scope context environment before items finalContext outcome after)
    (motive_8 := fun _ scope context environment before condition post body outcome after _ => Recursive.ForLoop program registry scope context environment before condition post body outcome after)
    (motive_9 := fun _ scope context environment before form requirements coercions outcome after _ => Recursive.RawForm program registry scope context environment before form requirements coercions outcome after)
    (motive_10 := fun _ scope context before step input outcome after _ => Recursive.CoercionStep program registry scope context before step input outcome after)
  erase_stage_grade

theorem CoercionPath.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : Recursive.CoercionPath program registry scope context before steps input outcome after) :
    ∃ size, CoercionPath program registry size scope context before steps input outcome after := by
  induction trace using Recursive.CoercionPath.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun mode scope context environment before roots finalContext outcome after _ => ∃ size, StatementsIn program registry mode size scope context environment before roots finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => ∃ size, While program registry size scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => ∃ size, Match program registry size scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ∃ size, ForItems program registry size scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ∃ size, ForLoop program registry size scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => ∃ size, RawForm program registry size scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => ∃ size, CoercionStep program registry size scope context before step input outcome after)
  construct_stage_grade

end Solcore.SourceSemantics.Staging.Recursive.Size
