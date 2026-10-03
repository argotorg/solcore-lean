import Solcore.SourceSemantics.Staging.RecursiveScope

/-! A finite recursive staged profile. Every callee, argument and closure body
uses these same mutually recursive judgments. Staging rejection is propagated
unchanged through lexical scopes and call returns, with exact prefix heaps.

The initial profile covers atomic forms, groups, binary tuples, uncoerced primitive unary/binary operators, conditionals,
indirect calls without argument/output coercions, builtins, and closure/global bodies
containing monomorphic lets, discard, and returns. It deliberately has no plain
Dynamic fallback for unsupported expressions or bodies. Direct declaration/method calls,
evidence-selected operator methods, coercion paths, assignments, and loops require later recursive rules. These
judgments do not assert coverage of the full current compiler. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

inductive BodyResult : TypeSystem.Ty → BodyOutcome → Outcome → Prop where
  | returned {type value} : BodyResult type (.returned value) (.value value)
  | unit {environment} : BodyResult .unit (.fallthrough environment) (.value .unit)
  | fault {type failure} : BodyResult type (.fault failure) (.fault failure)

/-- A named body has an empty lexical capture and its independent full
invocation dictionary. This view is not itself a global callable identity;
global application also requires genuine program instantiation and Covers. -/
def globalView (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) : Closure where
  parameters := body.source.inputs
  resultType := body.resultType
  body := roots
  source := body.source
  captured := []
  context := body.context
  evidence := evidence

mutual
  inductive Expression (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → Outcome → Heap → Prop where
    | atomicValue {scope context environment before after id node value}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          node.form node.requirements [] value after) :
        Expression program registry scope context environment before id (.value value) after
    | atomicFault {scope context environment before after id node reason}
        (contains : ContainsExpression scope.source id node)
        (atomic : AtomicForm node.form) (uncoerced : node.coercions = [])
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          node.form node.requirements [] reason after) :
        Expression program registry scope context environment before id (.fault (.semantic reason)) after
    | group {scope context environment before after id inner outcome}
        (occurrence : Occurrence scope id (.group inner))
        (child : Expression program registry scope context environment before inner outcome after) :
        Expression program registry scope context environment before id outcome after
    | pair {scope context environment before middle after id left right a b}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (second : Expression program registry scope context environment middle right (.value b) after) :
        Expression program registry scope context environment before id (.value (.product a b)) after
    | pairLeftFault {scope context environment before after id left right failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (child : Expression program registry scope context environment before left (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | pairRightFault {scope context environment before middle after id left right value failure}
        (occurrence : Occurrence scope id (.tuple [left, right]))
        (first : Expression program registry scope context environment before left (.value value) middle)
        (second : Expression program registry scope context environment middle right (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | unary {scope context environment before after id operator operand input output}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (applies : UnaryPrimitiveApplies operator input output) :
        Expression program registry scope context environment before id (.value output) after
    | unaryOperandFault {scope context environment before after id operator operand failure}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | unaryInvalid {scope context environment before after id operator operand input}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidUnaryOperand operator))) after
    | binaryLeftFault {scope context environment before after id left operator right failure}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | binaryLeftInvalid {scope context environment before after id left operator right input}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value input) after)
        (invalid : BinaryLeftOperandInvalid operator input) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | binaryShortCircuit {scope context environment before after id left operator right input output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value input) after)
        (circuit : ShortCircuits operator input output) :
        Expression program registry scope context environment before id (.value output) after
    | binaryRightFault {scope context environment before middle after id left operator right input failure}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value input) middle)
        (continues : EvaluatesRightOperand operator input)
        (second : Expression program registry scope context environment middle right (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | binary {scope context environment before middle after id left operator right a b output}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) after)
        (applies : BinaryPrimitiveApplies operator a b output) :
        Expression program registry scope context environment before id (.value output) after
    | binaryInvalid {scope context environment before middle after id left operator right a b}
        (occurrence : Occurrence scope id (.binary left operator right))
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) after)
        (invalid : BinaryPrimitiveOperandsInvalid operator a b) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidBinaryOperands operator))) after
    | conditional {scope context environment before middle after id condition yes no truth outcome}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : Expression program registry scope context environment middle (if truth then yes else no) outcome after) :
        Expression program registry scope context environment before id outcome after
    | conditionalFault {scope context environment before after id condition yes no failure}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | calleeFault {scope context environment before after id callee arguments metadata failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | notCallable {scope context environment before after id callee arguments metadata value}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) after)
        (invalid : ¬ CallableValue value) :
        Expression program registry scope context environment before id (.fault (.semantic .notCallable)) after
    | rejected {scope context environment before after id callee arguments metadata value reason}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) after)
        (guard : CallBoundary.GuardRejects scope.guards id arguments value reason) :
        Expression program registry scope context environment before id (.fault (.stage scope id reason)) after
    | argumentsFault {scope context environment before middle after id callee arguments metadata value failure}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment middle arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | sourceArity {scope context environment before middle after id callee arguments metadata value values}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (child : Expression program registry scope context environment before callee (.value value) middle)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment middle arguments (.values values) after)
        (mismatch : arguments.length ≠ metadata.argumentCount) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.argumentArityMismatch metadata.argumentCount arguments.length))) after
    | applied {scope context environment before calleeHeap argumentsHeap after id callee arguments metadata value values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.indirect metadata)))
        (uncoerced : metadata.argumentCoercions = [])
        (child : Expression program registry scope context environment before callee (.value value) calleeHeap)
        (guard : CallBoundary.GuardAccepts scope.guards id arguments value)
        (children : Expressions program registry scope context environment calleeHeap arguments (.values values) argumentsHeap)
        (arity : arguments.length = metadata.argumentCount)
        (invocation : Applies program registry scope context argumentsHeap value values outcome after) :
        Expression program registry scope context environment before id outcome after

  inductive Expressions (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → List ExpressionId → ValuesOutcome → Heap → Prop where
    | nil {scope context environment heap} :
        Expressions program registry scope context environment heap [] (.values []) heap
    | cons {scope context environment before middle after id ids value values}
        (head : Expression program registry scope context environment before id (.value value) middle)
        (tail : Expressions program registry scope context environment middle ids (.values values) after) :
        Expressions program registry scope context environment before (id :: ids) (.values (value :: values)) after
    | headFault {scope context environment before after id ids failure}
        (head : Expression program registry scope context environment before id (.fault failure) after) :
        Expressions program registry scope context environment before (id :: ids) (.fault failure) after
    | tailFault {scope context environment before middle after id ids value failure}
        (head : Expression program registry scope context environment before id (.value value) middle)
        (tail : Expressions program registry scope context environment middle ids (.fault failure) after) :
        Expressions program registry scope context environment before (id :: ids) (.fault failure) after

  inductive Applies (program : Program) (registry : Registry) :
      Scope → Context → Heap → Value → List Value → Outcome → Heap → Prop where
    | builtin {scope context heap function arguments value}
        (primitive : BuiltinApplies function.id arguments value) :
        Applies program registry scope context heap (.builtin function) arguments (.value value) heap
    | builtinArity {scope context heap function arguments}
        (mismatch : function.id.parameterTypes.length ≠ arguments.length) :
        Applies program registry scope context heap (.builtin function) arguments
          (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length arguments.length))) heap
    | builtinType {scope context heap function arguments expected actual}
        (arity : function.id.parameterTypes.length = arguments.length)
        (mismatch : ValuesFirstTypeMismatch arguments function.id.parameterTypes expected actual) :
        Applies program registry scope context heap (.builtin function) arguments
          (.fault (.semantic (.typeMismatch expected actual))) heap
    | closureArity {scope context heap function arguments}
        (mismatch : function.parameters.length ≠ arguments.length) :
        Applies program registry scope context heap (.closure function) arguments
          (.fault (.semantic (.argumentArityMismatch function.parameters.length arguments.length))) heap
    | globalArity {scope context heap function arguments bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        Applies program registry scope context heap (.global function) arguments
          (.fault (.semantic (.argumentArityMismatch bodyInstance.source.inputs.length arguments.length))) heap
    | global {scope context before bound after function arguments environment
          parameterTypes bodyContext finalContext bodyInstance roots child outcome result}
        (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
        (covers : function.evidence.Covers bodyInstance.context)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
        (body : Statements program registry child bodyContext environment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Applies program registry scope context before (.global function) arguments result after
    | closure {scope context before bound after function arguments environment parameterTypes bodyContext finalContext child outcome result}
        (selected : registry.Closure function child)
        (valid : ClosureFrame program function)
        (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
        (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
        (body : Statements program registry child bodyContext environment bound function.body finalContext outcome after)
        (resultRule : BodyResult function.resultType outcome result) :
        Applies program registry scope context before (.closure function) arguments result after

  inductive Statements (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → List StatementId → Context → BodyOutcome → Heap → Prop where
    | nil {scope context environment heap} :
        Statements program registry scope context environment heap [] context (.fallthrough environment) heap
    | returnUnit {scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt none) :
        Statements program registry scope context environment heap (id :: rest) context (.returned .unit) heap
    | returnValue {scope context environment before after id rest node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.value value) after) :
        Statements program registry scope context environment before (id :: rest) context (.returned value) after
    | returnFault {scope context environment before after id rest node expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        Statements program registry scope context environment before (id :: rest) context (.fault failure) after
    | tail {scope context environment before after id node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry scope context environment before expression (.value value) after) :
        Statements program registry scope context environment before [id] context (.returned value) after
    | discard {scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression true)
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : Statements program registry scope context environment middle rest finalContext outcome after) :
        Statements program registry scope context environment before (id :: rest) finalContext outcome after
    | expressionFault {scope context environment before after id rest node expression semicolon failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression semicolon)
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        Statements program registry scope context environment before (id :: rest) context (.fault failure) after
    | letUninitialized {scope context middleContext finalContext environment before bound after id rest node binder location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : Statements program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        Statements program registry scope context environment before (id :: rest) finalContext outcome after
    | letInitialized {scope context middleContext finalContext environment before middle bound after id rest node binder expression value location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : Statements program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        Statements program registry scope context environment before (id :: rest) finalContext outcome after
    | letFault {scope context environment before after id rest node binder expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        Statements program registry scope context environment before (id :: rest) context (.fault failure) after


end

end Solcore.SourceSemantics.Staging.Recursive
