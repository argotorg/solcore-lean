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
    | unary {childSize : Nat} {scope context environment before after id operator operand input output}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry childSize scope context environment before operand (.value input) after)
        (applies : UnaryPrimitiveApplies operator input output) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.value output) after
    | unaryOperandFault {childSize : Nat} {scope context environment before after id operator operand failure}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry childSize scope context environment before operand (.fault failure) after) :
        Expression program registry (stepSize [childSize]) scope context environment before id (.fault failure) after
    | unaryInvalid {childSize : Nat} {scope context environment before after id operator operand input}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry childSize scope context environment before operand (.value input) after)
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        Expression program registry (stepSize [childSize]) scope context environment before id
          (.fault (.semantic (.invalidUnaryOperand operator))) after
    | binaryLeftFault {firstSize : Nat} {scope context environment before after id left operator right failure}
        (occurrence : Occurrence scope id (.binary left operator right))
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
        (occurrence : Occurrence scope id (.binary left operator right))
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
    | conditional {testSize branchSize : Nat} {scope context environment before middle after id condition yes no truth outcome}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry testSize scope context environment before condition (.value (.bool truth)) middle)
        (branch : Expression program registry branchSize scope context environment middle (if truth then yes else no) outcome after) :
        Expression program registry (stepSize [testSize, branchSize]) scope context environment before id outcome after
    | conditionalFault {testSize : Nat} {scope context environment before after id condition yes no failure}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry testSize scope context environment before condition (.fault failure) after) :
        Expression program registry (stepSize [testSize]) scope context environment before id (.fault failure) after
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
        (body : Statements program registry bodySize child bodyContext environment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Applies program registry (stepSize [bodySize]) scope context before (.global function) arguments result after
    | closure {bodySize : Nat} {scope context before bound after function arguments environment parameterTypes bodyContext finalContext child outcome result}
        (selected : registry.Closure function child)
        (valid : ClosureFrame program function)
        (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
        (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
        (body : Statements program registry bodySize child bodyContext environment bound function.body finalContext outcome after)
        (resultRule : BodyResult function.resultType outcome result) :
        Applies program registry (stepSize [bodySize]) scope context before (.closure function) arguments result after

  inductive Statements (program : Program) (registry : Registry) :
      Nat → Scope → Context → Environment → Heap → List StatementId → Context → BodyOutcome → Heap → Prop where
    | nil {scope context environment heap} :
        Statements program registry (stepSize []) scope context environment heap [] context (.fallthrough environment) heap
    | returnUnit {scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt none) :
        Statements program registry (stepSize []) scope context environment heap (id :: rest) context (.returned .unit) heap
    | returnValue {childSize : Nat} {scope context environment before after id rest node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry childSize scope context environment before expression (.value value) after) :
        Statements program registry (stepSize [childSize]) scope context environment before (id :: rest) context (.returned value) after
    | returnFault {childSize : Nat} {scope context environment before after id rest node expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        Statements program registry (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | tail {childSize : Nat} {scope context environment before after id node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry childSize scope context environment before expression (.value value) after) :
        Statements program registry (stepSize [childSize]) scope context environment before [id] context (.returned value) after
    | discard {childSize nextSize : Nat} {scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression true)
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (next : Statements program registry nextSize scope context environment middle rest finalContext outcome after) :
        Statements program registry (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | expressionFault {childSize : Nat} {scope context environment before after id rest node expression semicolon failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression semicolon)
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        Statements program registry (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | letUninitialized {nextSize : Nat} {scope context middleContext finalContext environment before bound after id rest node binder location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : Statements program registry nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        Statements program registry (stepSize [nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | letInitialized {childSize nextSize : Nat} {scope context middleContext finalContext environment before middle bound after id rest node binder expression value location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (child : Expression program registry childSize scope context environment before expression (.value value) middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : Statements program registry nextSize scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        Statements program registry (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | letFault {childSize : Nat} {scope context environment before after id rest node binder expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry childSize scope context environment before expression (.fault failure) after) :
        Statements program registry (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after

end


/-! The four mutually recursive projections use the same rule handlers. -/
local macro "erase_stage_grade" : tactic =>
  `(tactic| (
    case atomicValue => apply Recursive.Expression.atomicValue <;> assumption
    case atomicFault => apply Recursive.Expression.atomicFault <;> assumption
    case group => apply Recursive.Expression.group <;> assumption
    case pair => apply Recursive.Expression.pair <;> assumption
    case pairLeftFault => apply Recursive.Expression.pairLeftFault <;> assumption
    case pairRightFault => apply Recursive.Expression.pairRightFault <;> assumption
    case tupleValue => apply Recursive.Expression.tupleValue <;> assumption
    case tupleFault => apply Recursive.Expression.tupleFault <;> assumption
    case unary => apply Recursive.Expression.unary <;> assumption
    case unaryOperandFault => apply Recursive.Expression.unaryOperandFault <;> assumption
    case unaryInvalid => apply Recursive.Expression.unaryInvalid <;> assumption
    case binaryLeftFault => apply Recursive.Expression.binaryLeftFault <;> assumption
    case binaryLeftInvalid => apply Recursive.Expression.binaryLeftInvalid <;> assumption
    case binaryShortCircuit => apply Recursive.Expression.binaryShortCircuit <;> assumption
    case binaryRightFault => apply Recursive.Expression.binaryRightFault <;> assumption
    case binary => apply Recursive.Expression.binary <;> assumption
    case binaryInvalid => apply Recursive.Expression.binaryInvalid <;> assumption
    case conditional => apply Recursive.Expression.conditional <;> assumption
    case conditionalFault => apply Recursive.Expression.conditionalFault <;> assumption
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
    case nil => apply Recursive.Statements.nil <;> assumption
    case returnUnit => apply Recursive.Statements.returnUnit <;> assumption
    case returnValue => apply Recursive.Statements.returnValue <;> assumption
    case returnFault => apply Recursive.Statements.returnFault <;> assumption
    case tail => apply Recursive.Statements.tail <;> assumption
    case discard => apply Recursive.Statements.discard <;> assumption
    case expressionFault => apply Recursive.Statements.expressionFault <;> assumption
    case letUninitialized => apply Recursive.Statements.letUninitialized <;> assumption
    case letInitialized => apply Recursive.Statements.letInitialized <;> assumption
    case letFault => apply Recursive.Statements.letFault <;> assumption
  ))

local macro "construct_stage_grade" : tactic =>
  `(tactic| (
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
    case conditional occurrence test branch ih_test ih_branch =>
      obtain ⟨testSize, graded_test⟩ := ih_test
      obtain ⟨branchSize, graded_branch⟩ := ih_branch
      exact ⟨_, .conditional occurrence graded_test graded_branch⟩
    case conditionalFault occurrence test ih_test =>
      obtain ⟨testSize, graded_test⟩ := ih_test
      exact ⟨_, .conditionalFault occurrence graded_test⟩
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
    case expressionFault contains form child ih_child =>
      obtain ⟨childSize, graded_child⟩ := ih_child
      exact ⟨_, .expressionFault contains form graded_child⟩
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
  ))

theorem Expression.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry size scope context environment before id outcome after) :
    Recursive.Expression program registry scope context environment before id outcome after := by
  induction trace using Expression.rec
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun _ scope context environment before roots finalContext outcome after _ => Recursive.Statements program registry scope context environment before roots finalContext outcome after)
  erase_stage_grade

theorem Expressions.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Expressions program registry size scope context environment before ids outcome after) :
    Recursive.Expressions program registry scope context environment before ids outcome after := by
  induction trace using Expressions.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
    (motive_4 := fun _ scope context environment before roots finalContext outcome after _ => Recursive.Statements program registry scope context environment before roots finalContext outcome after)
  erase_stage_grade

theorem Applies.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context : Context} {before after : Heap}
    {function : Value} {arguments : List Value} {outcome : Outcome}
    (trace : Applies program registry size scope context before function arguments outcome after) :
    Recursive.Applies program registry scope context before function arguments outcome after := by
  induction trace using Applies.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_4 := fun _ scope context environment before roots finalContext outcome after _ => Recursive.Statements program registry scope context environment before roots finalContext outcome after)
  erase_stage_grade

theorem Statements.sound {program : Program} {registry : Registry} {size : Nat}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : Statements program registry size scope context environment before roots finalContext outcome after) :
    Recursive.Statements program registry scope context environment before roots finalContext outcome after := by
  induction trace using Statements.rec
    (motive_1 := fun _ scope context environment before id outcome after _ => Recursive.Expression program registry scope context environment before id outcome after)
    (motive_2 := fun _ scope context environment before ids outcome after _ => Recursive.Expressions program registry scope context environment before ids outcome after)
    (motive_3 := fun _ scope context before function arguments outcome after _ => Recursive.Applies program registry scope context before function arguments outcome after)
  erase_stage_grade

theorem Expression.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {id : ExpressionId} {outcome : Outcome}
    (trace : Recursive.Expression program registry scope context environment before id outcome after) :
    ∃ size, Expression program registry size scope context environment before id outcome after := by
  induction trace using Recursive.Expression.rec
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun scope context environment before roots finalContext outcome after _ => ∃ size, Statements program registry size scope context environment before roots finalContext outcome after)
  construct_stage_grade

theorem Expressions.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Recursive.Expressions program registry scope context environment before ids outcome after) :
    ∃ size, Expressions program registry size scope context environment before ids outcome after := by
  induction trace using Recursive.Expressions.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
    (motive_4 := fun scope context environment before roots finalContext outcome after _ => ∃ size, Statements program registry size scope context environment before roots finalContext outcome after)
  construct_stage_grade

theorem Applies.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap}
    {function : Value} {arguments : List Value} {outcome : Outcome}
    (trace : Recursive.Applies program registry scope context before function arguments outcome after) :
    ∃ size, Applies program registry size scope context before function arguments outcome after := by
  induction trace using Recursive.Applies.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_4 := fun scope context environment before roots finalContext outcome after _ => ∃ size, Statements program registry size scope context environment before roots finalContext outcome after)
  construct_stage_grade

theorem Statements.of_trace {program : Program} {registry : Registry}
    {scope : Scope} {context finalContext : Context} {environment : Environment} {before after : Heap}
    {roots : List StatementId} {outcome : BodyOutcome}
    (trace : Recursive.Statements program registry scope context environment before roots finalContext outcome after) :
    ∃ size, Statements program registry size scope context environment before roots finalContext outcome after := by
  induction trace using Recursive.Statements.rec
    (motive_1 := fun scope context environment before id outcome after _ => ∃ size, Expression program registry size scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ∃ size, Expressions program registry size scope context environment before ids outcome after)
    (motive_3 := fun scope context before function arguments outcome after _ => ∃ size, Applies program registry size scope context before function arguments outcome after)
  construct_stage_grade

end Solcore.SourceSemantics.Staging.Recursive.Size
