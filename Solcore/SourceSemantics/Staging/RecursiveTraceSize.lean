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
    | matchFault {matchSize : Nat} {mode scope context environment before after id rest node resolution failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.fault failure) after) :
        StatementsIn program registry mode (stepSize [matchSize]) scope context environment before (id :: rest) context (.fault failure) after
    | matchFallthrough {matchSize nextSize : Nat} {mode scope context finalContext environment before middle after id rest node resolution outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry matchSize scope context environment before resolution (.fallthrough environment) middle)
        (next : StatementsIn program registry mode nextSize scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [matchSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
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
    | assignBare {childSize nextSize : Nat} {mode scope context finalContext environment before middle written after
          id rest node assignment rhs value target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment .equal rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode nextSize scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode (stepSize [childSize, nextSize]) scope context environment before (id :: rest) finalContext outcome after
    | assignBareFault {childSize : Nat} {mode scope context environment before after id rest node assignment rhs target failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment .equal rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry childSize scope context environment before rhs (.fault failure) after) :
        StatementsIn program registry mode (stepSize [childSize]) scope context environment before (id :: rest) context (.fault failure) after
    | assignBareUnbound {mode scope context environment heap id rest node assignment rhs}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment .equal rhs)
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | assignBareDangling {mode scope context environment heap id rest node assignment rhs location}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment .equal rhs)
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        StatementsIn program registry mode (stepSize []) scope context environment heap (id :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap
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
  all condition and body heap effects. Loop-control transfers are a later extension. -/
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
    | bodyFault {testSize bodySize : Nat} {scope context innerContext environment before middle after condition statements failure}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.fault failure) after) :
        While program registry (stepSize [testSize, bodySize]) scope context environment before condition statements (.fault failure) after
    | next {testSize bodySize nextSize : Nat} {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry testSize scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false bodySize scope context environment middle statements innerContext (.fallthrough innerEnvironment) bodyHeap)
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

end

abbrev Statements (program : Program) (registry : Registry) := StatementsIn program registry true
namespace Statements
export StatementsIn (nil returnUnit returnValue returnFault tail discard expressionFault
  assignBare assignBareFault assignBareUnbound assignBareDangling letUninitialized letInitialized letFault
  ifConditionFault ifReturned ifFault ifFallthrough blockReturned blockFault blockFallthrough whileReturned whileFault whileFallthrough matchReturned matchFault matchFallthrough)
end Statements


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
    case assignBare => apply Recursive.StatementsIn.assignBare <;> assumption
    case assignBareFault => apply Recursive.StatementsIn.assignBareFault <;> assumption
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
    case scrutineeFault => apply Recursive.Match.scrutineeFault <;> assumption
    case patternFault => apply Recursive.Match.patternFault <;> assumption
    case arm => apply Recursive.Match.arm <;> assumption
    case default => apply Recursive.Match.default <;> assumption
    case noBranch => apply Recursive.Match.noBranch <;> assumption
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
    case assignBare contains form snapshot child write next childIH nextIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      obtain ⟨nextSize, nextGraded⟩ := nextIH
      exact ⟨_, .assignBare contains form snapshot childGraded write nextGraded⟩
    case assignBareFault contains form snapshot child childIH =>
      obtain ⟨childSize, childGraded⟩ := childIH
      exact ⟨_, .assignBareFault contains form snapshot childGraded⟩
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
  construct_stage_grade

end Solcore.SourceSemantics.Staging.Recursive.Size
