import Solcore.SourceSemantics.Staging.RecursiveBareTarget

/-! A finite recursive staged profile. Every callee, argument and selected body
uses these same mutually recursive judgments. Staging rejection propagates
unchanged through lexical scopes and call returns, retaining exact prefix heaps.

The profile covers atomic forms, groups, ordered tuples, nominal constructor
payloads, mapping indices, primitive and evidence-selected operators,
conditionals, direct declarations, indirect calls and builtins. Output coercion
paths on atomic forms and direct calls retain their original source metadata.
Bodies cover monomorphic lets, bare plain assignments, discards, scoped blocks,
conditional statements, finite while and for loops, ordered match arms, returns,
and scoped break and continue transfers.
Blocks and conditional arms restore lexical bindings while keeping heap effects.
Projected assignments require further rules. These judgments do not assert coverage of the full current compiler. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

/-- Leaving a match arm restores lexical bindings, while its heap is retained. -/
def BodyOutcome.restore (environment : Environment) : BodyOutcome → BodyOutcome
  | .fallthrough _ => .fallthrough environment
  | .breaking _ => .breaking environment
  | .continuing _ => .continuing environment
  | .returned value => .returned value
  | .fault failure => .fault failure

/-- For-header completion retains its actual live bindings; headers do not transfer control. -/
inductive ForItemsOutcome where
  | done (environment : Dynamic.Environment)
  | fault (failure : Failure)

inductive BodyResult : TypeSystem.Ty → BodyOutcome → Outcome → Prop where
  | returned {type value} : BodyResult type (.returned value) (.value value)
  | breaking {type environment} :
      BodyResult type (.breaking environment) (.fault (.semantic .controlEscapedFunction))
  | continuing {type environment} :
      BodyResult type (.continuing environment) (.fault (.semantic .controlEscapedFunction))
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

/-- A method body uses a neutral scope view with its selected dictionary.
This record is neither an ordinary global identity nor a source lambda value. -/
def methodView (body : BodyInstance) (evidence : EvidenceEnvironment) (roots : List StatementId) : Closure :=
  globalView body evidence roots

/-- Mapping lookup decides only after both children have finished. This
independent Source relation keeps the original key and value types. -/
inductive IndexOutcome (base key : Dynamic.Value) : Outcome → Prop where
  | found {keyType valueType entries value}
      (shape : base = .mapping keyType valueType entries)
      (located : MappingLookup key entries value) : IndexOutcome base key (.value value)
  | default {keyType valueType entries value}
      (shape : base = .mapping keyType valueType entries)
      (absent : MappingAbsent key entries) (defaulted : DefaultValue valueType value) :
      IndexOutcome base key (.value value)
  | shape (invalid : ¬ MappingValue base) :
      IndexOutcome base key (.fault (.semantic .invalidProjection))
  | keyType {keyType valueType entries actual}
      (shape : base = .mapping keyType valueType entries)
      (typed : ValueRuntimeType key actual) (mismatch : runtimeType actual ≠ runtimeType keyType) :
      IndexOutcome base key (.fault (.semantic (.typeMismatch keyType (runtimeType actual))))
  | unavailable {keyType valueType entries}
      (shape : base = .mapping keyType valueType entries)
      (typed : ValueRuntimeTypeMatches key keyType) (absent : MappingAbsent key entries)
      (missing : ¬ Defaultable valueType) :
      IndexOutcome base key (.fault (.semantic (.missingMappingDefault valueType)))

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
    | tupleValue {scope context environment before after id elements values packed}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry scope context environment before elements (.values values) after)
        (pack : ValuesPack values packed) :
        Expression program registry scope context environment before id (.value packed) after
    | tupleFault {scope context environment before after id elements failure}
        (occurrence : Occurrence scope id (.tuple elements))
        (children : Expressions program registry scope context environment before elements (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | constructorValue {scope context environment before after id instantiation arguments values}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) after) :
        Expression program registry scope context environment before id (.value (.constructed instantiation values)) after
    | constructorFault {scope context environment before after id instantiation arguments failure}
        (occurrence : Occurrence scope id (.constructor instantiation arguments))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexBaseFault {scope context environment before after id base key failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexKeyFault {scope context environment before middle after id base key value failure}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.value value) middle)
        (second : Expression program registry scope context environment middle key (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | indexResult {scope context environment before middle after id base key baseValue keyValue outcome}
        (occurrence : Occurrence scope id (.index base key))
        (first : Expression program registry scope context environment before base (.value baseValue) middle)
        (second : Expression program registry scope context environment middle key (.value keyValue) after)
        (result : IndexOutcome baseValue keyValue outcome) :
        Expression program registry scope context environment before id outcome after
    | unary {scope context environment before after id operator operand input output}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (applies : UnaryPrimitiveApplies operator input output) :
        Expression program registry scope context environment before id (.value output) after
    | unaryOperandFault {scope context environment before after id operator operand failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (child : Expression program registry scope context environment before operand (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | unaryInvalid {scope context environment before after id operator operand input}
        (occurrence : Occurrence scope id (.unary operator operand))
        (child : Expression program registry scope context environment before operand (.value input) after)
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        Expression program registry scope context environment before id
          (.fault (.semantic (.invalidUnaryOperand operator))) after
    | binaryLeftFault {scope context environment before after id left operator right failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
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
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
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
    | unaryMethod {scope context environment before argumentsHeap bound after id operator operand input
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.unary operator operand) requirements)
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (operandTrace : Expression program registry scope context environment before operand (.value input) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry scope context environment before id result after
    | binaryMethod {scope context environment before middle argumentsHeap bound after id left operator right a b
          requirements traitName methodName bodyInstance dictionary roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (occurrence : Occurrence scope id (.binary left operator right) requirements)
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (method : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
        (first : Expression program registry scope context environment before left (.value a) middle)
        (continues : EvaluatesRightOperand operator a)
        (second : Expression program registry scope context environment middle right (.value b) argumentsHeap)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [a, b] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Expression program registry scope context environment before id result after
    | conditional {scope context environment before middle after id condition yes no truth outcome}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : Expression program registry scope context environment middle (if truth then yes else no) outcome after) :
        Expression program registry scope context environment before id outcome after
    | conditionalFault {scope context environment before after id condition yes no failure}
        (occurrence : Occurrence scope id (.conditional condition yes no))
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | builtinArgumentsFault {scope context environment before after id callee arguments function failure}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | builtinApplied {scope context environment before argumentsHeap after id callee arguments function values outcome}
        (occurrence : Occurrence scope id (.call callee arguments (.builtinFunction function)))
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (invocation : Applies program registry scope context argumentsHeap (.builtin ⟨function⟩) values outcome after) :
        Expression program registry scope context environment before id outcome after
    | directArgumentsFault {scope context environment before after id callee arguments instantiation name failure}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after
    | directApplied {scope context environment before argumentsHeap after id callee arguments instantiation name values evidence outcome}
        {requirements : List RequirementId}
        (occurrence : Occurrence scope id (.call callee arguments (.declaration instantiation)) requirements)
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements [] instantiation.predicates evidence)
        (invocation : Applies program registry scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        Expression program registry scope context environment before id outcome after
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

    | coercedValue {scope context environment before middle after id node value outcome}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry scope context environment before node.form
          node.requirements node.coercions (.value value) middle)
        (path : CoercionPath program registry scope context middle node.coercions value outcome after) :
        Expression program registry scope context environment before id outcome after
    | coercedFault {scope context environment before after id node failure}
        (contains : ContainsExpression scope.source id node)
        (nonempty : node.coercions ≠ [])
        (raw : RawForm program registry scope context environment before node.form
          node.requirements node.coercions (.fault failure) after) :
        Expression program registry scope context environment before id (.fault failure) after

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
        (body : StatementsIn program registry true child bodyContext environment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        Applies program registry scope context before (.global function) arguments result after
    | closure {scope context before bound after function arguments environment parameterTypes bodyContext finalContext child outcome result}
        (selected : registry.Closure function child)
        (valid : ClosureFrame program function)
        (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
        (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
        (body : StatementsIn program registry true child bodyContext environment bound function.body finalContext outcome after)
        (resultRule : BodyResult function.resultType outcome result) :
        Applies program registry scope context before (.closure function) arguments result after

  inductive StatementsIn (program : Program) (registry : Registry) :
      Bool → Scope → Context → Environment → Heap → List StatementId → Context → BodyOutcome → Heap → Prop where
    | nil {mode scope context environment heap} :
        StatementsIn program registry mode scope context environment heap [] context (.fallthrough environment) heap
    | returnUnit {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt none) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.returned .unit) heap
    | continuing {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .continueStmt) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.continuing environment) heap
    | breaking {mode scope context environment heap id rest node}
        (contains : ContainsStatement scope.source id node) (form : node.form = .breakStmt) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context (.breaking environment) heap
    | returnValue {mode scope context environment before after id rest node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.value value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | returnFault {mode scope context environment before after id rest node expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .returnStmt (some expression))
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | tail {scope context environment before after id node expression value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry scope context environment before expression (.value value) after) :
        StatementsIn program registry true scope context environment before [id] context (.returned value) after
    | discard {mode scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression true)
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | expressionFault {mode scope context environment before after id rest node expression semicolon failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression semicolon)
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- A non-tail branch expression discards its value even at the end of its arm. -/
    | discardValue {scope context finalContext environment before middle after id rest node expression value outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : StatementsIn program registry false scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry false scope context environment before (id :: rest) finalContext outcome after
    | ifConditionFault {mode scope context environment before after id rest node condition thenBody elseBody failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | ifReturned {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | ifContinuing {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | ifBreaking {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | ifFault {mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- Branch-local bindings leave scope; all writes and allocations remain in its reached heap. -/
    | ifFallthrough {mode scope context innerContext finalContext environment innerEnvironment before middle branchHeap after
          id rest node condition thenBody elseBody truth outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
        (test : Expression program registry scope context environment before condition (.value (.bool truth)) middle)
        (branch : StatementsIn program registry false scope context environment middle
          (if truth then thenBody else elseBody.getD []) innerContext (.fallthrough innerEnvironment) branchHeap)
        (next : StatementsIn program registry mode scope context environment branchHeap rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | blockReturned {mode scope context innerContext environment before after id rest node statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | blockContinuing {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.continuing innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | blockBreaking {mode scope context innerContext environment before after id rest node statements innerEnvironment}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.breaking innerEnvironment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | blockFault {mode scope context innerContext environment before after id rest node statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    /-- A block restores its entry bindings while retaining every write and allocation. -/
    | blockFallthrough {mode scope context innerContext finalContext environment innerEnvironment before middle after id rest node statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .block statements)
        (inner : StatementsIn program registry false scope context environment before statements innerContext (.fallthrough innerEnvironment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | matchReturned {mode scope context environment before after id rest node resolution value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | matchContinuing {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.continuing environment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.continuing environment) after
    | matchBreaking {mode scope context environment before after id rest node resolution}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.breaking environment) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.breaking environment) after
    | matchFault {mode scope context environment before after id rest node resolution failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | matchFallthrough {mode scope context finalContext environment before middle after id rest node resolution outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .matchWith resolution)
        (matched : Match program registry scope context environment before resolution (.fallthrough environment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | forInitializerFault {mode scope context failedContext environment before after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer failedContext (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | forReturned {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | forFault {mode scope context loopContext environment loopEnvironment before middle after id rest node initializer condition post body failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | forFallthrough {mode scope context loopContext finalContext environment loopEnvironment before middle loopHeap after
          id rest node initializer condition post body outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .forLoop initializer condition post body)
        (initial : ForItems program registry scope context environment before initializer loopContext (.done loopEnvironment) middle)
        (loop : ForLoop program registry scope loopContext loopEnvironment middle condition post body (.fallthrough loopEnvironment) loopHeap)
        (next : StatementsIn program registry mode scope context environment loopHeap rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | whileReturned {mode scope context environment before after id rest node condition statements value}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.returned value) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.returned value) after
    | whileFault {mode scope context environment before after id rest node condition statements failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | whileFallthrough {mode scope context finalContext environment before middle after id rest node condition statements outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .whileLoop condition statements)
        (loop : While program registry scope context environment before condition statements (.fallthrough environment) middle)
        (next : StatementsIn program registry mode scope context environment middle rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    /-- The target snapshot precedes the RHS; the write uses its actual final heap. -/
    | assignBare {mode scope context finalContext environment before middle written after
          id rest node assignment operator rhs value target updated outcome}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : StatementsIn program registry mode scope context environment written rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | assignBareFault {mode scope context environment before after id rest node assignment operator rhs target failure}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after
    | assignBareOperands {mode scope context environment before after id rest node assignment operator rhs
          target right currentCell initial currentSelected}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        StatementsIn program registry mode scope context environment before (id :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | assignBareUnbound {mode scope context environment heap id rest node assignment operator rhs}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | assignBareDangling {mode scope context environment heap id rest node assignment operator rhs location}
        (contains : ContainsStatement scope.source id node)
        (form : node.form = .assignValue assignment operator rhs)
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        StatementsIn program registry mode scope context environment heap (id :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap
    | letUninitialized {mode scope context middleContext finalContext environment before bound after id rest node binder location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : StatementsIn program registry mode scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | letInitialized {mode scope context middleContext finalContext environment before middle bound after id rest node binder expression value location outcome}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : StatementsIn program registry mode scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        StatementsIn program registry mode scope context environment before (id :: rest) finalContext outcome after
    | letFault {mode scope context environment before after id rest node binder expression failure}
        (contains : ContainsStatement scope.source id node) (form : node.form = .letDecl binder (some expression))
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        StatementsIn program registry mode scope context environment before (id :: rest) context (.fault failure) after


  /-- Finite loop iterations restore their original lexical scope while retaining
  all condition and body heap effects. Break leaves the loop; continue tests again. -/
  inductive While (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → List StatementId → BodyOutcome → Heap → Prop where
    | done {scope context environment before after condition statements}
        (test : Expression program registry scope context environment before condition (.value (.bool false)) after) :
        While program registry scope context environment before condition statements (.fallthrough environment) after
    | conditionFault {scope context environment before after condition statements failure}
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        While program registry scope context environment before condition statements (.fault failure) after
    | returned {scope context innerContext environment before middle after condition statements value}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.returned value) after) :
        While program registry scope context environment before condition statements (.returned value) after
    | breakFromBody {scope context innerContext environment before middle after condition statements innerEnvironment}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.breaking innerEnvironment) after) :
        While program registry scope context environment before condition statements (.fallthrough environment) after
    | bodyFault {scope context innerContext environment before middle after condition statements failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.fault failure) after) :
        While program registry scope context environment before condition statements (.fault failure) after
    | next {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.fallthrough innerEnvironment) bodyHeap)
        (next : While program registry scope context environment bodyHeap condition statements outcome after) :
        While program registry scope context environment before condition statements outcome after
    | continueNext {scope context innerContext environment innerEnvironment before middle bodyHeap after condition statements outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (body : StatementsIn program registry false scope context environment middle statements innerContext (.continuing innerEnvironment) bodyHeap)
        (next : While program registry scope context environment bodyHeap condition statements outcome after) :
        While program registry scope context environment before condition statements outcome after


  /-- The original source's ordered pattern decision and real allocations are
  independent of the compiler. Selected bodies keep the same staged registry. -/
  inductive Match (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → MatchResolution → BodyOutcome → Heap → Prop where
    | scrutineeFault {scope context environment before after resolution failure}
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.fault failure) after) :
        Match program registry scope context environment before resolution (.fault failure) after
    | patternFault {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (allocated : Heap.Allocates middle node.type (some value) location hidden)
        (invalid : MatchCasesPatternFault context value resolution.cases) :
        Match program registry scope context environment before resolution (.fault (.semantic .invalidPattern)) hidden
    | arm {scope context armContext finalContext environment armEnvironment before middle hidden bound after
          resolution node value location statements bindings outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
        (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
        (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
        (body : StatementsIn program registry false scope armContext armEnvironment bound statements finalContext outcome after) :
        Match program registry scope context environment before resolution (outcome.restore environment) after
    | default {scope context finalContext environment before middle hidden after resolution node value location statements outcome}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
        (body : StatementsIn program registry false scope context environment hidden statements finalContext outcome after) :
        Match program registry scope context environment before resolution (outcome.restore environment) after
    | noBranch {scope context environment before middle hidden resolution node value location}
        (contains : ContainsExpression scope.source resolution.scrutinee node)
        (scrutinee : Expression program registry scope context environment before resolution.scrutinee (.value value) middle)
        (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
        (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
        Match program registry scope context environment before resolution (.fallthrough environment) hidden


  /-- Ordered ordinary for-header effects retain their actual lexical context.
  A fault carries the context reached before the failing item. -/
  inductive ForItems (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → List ForItemForm → Context → ForItemsOutcome → Heap → Prop where
    | empty {scope context environment heap} :
        ForItems program registry scope context environment heap [] context (.done environment) heap
    | absent {scope context middleContext finalContext environment before bound after binder rest location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (allocate : Heap.Allocates before binder.scheme.body none location bound)
        (next : ForItems program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry scope context environment before (.letDecl binder none :: rest) finalContext outcome after
    | initialized {scope context middleContext finalContext environment before middle bound after binder initializer rest value location outcome}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends scope.source.owner context binder middleContext)
        (child : Expression program registry scope context environment before initializer (.value value) middle)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location bound)
        (next : ForItems program registry scope middleContext ((binder.id, location) :: environment) bound rest finalContext outcome after) :
        ForItems program registry scope context environment before (.letDecl binder (some initializer) :: rest) finalContext outcome after
    | initializerFault {scope context environment before after binder initializer rest failure}
        (monomorphic : binder.scheme.quantified = [])
        (child : Expression program registry scope context environment before initializer (.fault failure) after) :
        ForItems program registry scope context environment before (.letDecl binder (some initializer) :: rest) context (.fault failure) after
    | expression {scope context finalContext environment before middle after expression rest value outcome}
        (child : Expression program registry scope context environment before expression (.value value) middle)
        (next : ForItems program registry scope context environment middle rest finalContext outcome after) :
        ForItems program registry scope context environment before (.expression expression :: rest) finalContext outcome after
    | expressionFailure {scope context environment before after expression rest failure}
        (child : Expression program registry scope context environment before expression (.fault failure) after) :
        ForItems program registry scope context environment before (.expression expression :: rest) context (.fault failure) after
    | assignment {scope context finalContext environment before middle written after assignment operator rhs value target updated rest outcome}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value value) middle)
        (write : ResolvedPlaceWrites
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
          middle target updated written)
        (next : ForItems program registry scope context environment written rest finalContext outcome after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) finalContext outcome after
    | assignmentFailure {scope context environment before after assignment operator rhs target rest failure}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.fault failure) after) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context (.fault failure) after
    | assignmentOperands {scope context environment before after assignment operator rhs target right
          currentCell initial currentSelected rest}
        (snapshot : BareTarget environment before assignment.target target)
        (child : Expression program registry scope context environment before rhs (.value right) after)
        (currentRead : Heap.Reads after target.location currentCell)
        (rootType : currentCell.type = target.rootType)
        (initialValue : RootInitialValue currentCell initial)
        (pathRead : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        ForItems program registry scope context environment before (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.invalidAssignmentOperands operator))) after
    | unbound {scope context environment heap assignment operator rhs rest}
        (bare : assignment.target.projections = [])
        (missing : environment.Unbound assignment.target.root) :
        ForItems program registry scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.unboundLocal assignment.target.root))) heap
    | dangling {scope context environment heap assignment operator rhs rest location}
        (bare : assignment.target.projections = [])
        (lookup : Environment.LooksUp environment assignment.target.root location)
        (missing : heap.Dangling location) :
        ForItems program registry scope context environment heap (.assignValue assignment operator rhs :: rest) context
          (.fault (.semantic (.danglingLocation location))) heap

  /-- Finite for iteration runs each post header in the original loop scope.
  Body/post local bindings are restored, while their heap effects persist. -/
  inductive ForLoop (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionId → List ForItemForm → List StatementId → BodyOutcome → Heap → Prop where
    | testFault {scope context environment before after condition post body failure}
        (test : Expression program registry scope context environment before condition (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | finished {scope context environment before after condition post body}
        (test : Expression program registry scope context environment before condition (.value (.bool false)) after) :
        ForLoop program registry scope context environment before condition post body (.fallthrough environment) after
    | bodyFailure {scope context innerContext environment before middle after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | returnedFromBody {scope context innerContext environment before middle after condition post body value}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.returned value) after) :
        ForLoop program registry scope context environment before condition post body (.returned value) after
    | forBreakFromBody {scope context innerContext environment before middle after condition post body innerEnvironment}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.breaking innerEnvironment) after) :
        ForLoop program registry scope context environment before condition post body (.fallthrough environment) after
    | postFailure {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | continuePostFailure {scope context innerContext postContext environment innerEnvironment before middle bodyHeap after condition post body failure}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.fault failure) after) :
        ForLoop program registry scope context environment before condition post body (.fault failure) after
    | iterate {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.fallthrough innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry scope context environment postHeap condition post body outcome after) :
        ForLoop program registry scope context environment before condition post body outcome after

    | continueIterate {scope context innerContext postContext environment innerEnvironment postEnvironment before middle bodyHeap postHeap after condition post body outcome}
        (test : Expression program registry scope context environment before condition (.value (.bool true)) middle)
        (branch : StatementsIn program registry false scope context environment middle body innerContext (.continuing innerEnvironment) bodyHeap)
        (postTrace : ForItems program registry scope context environment bodyHeap post postContext (.done postEnvironment) postHeap)
        (next : ForLoop program registry scope context environment postHeap condition post body outcome after) :
        ForLoop program registry scope context environment before condition post body outcome after

  /-- The original form before its retained output path. Child expressions keep
  the same source scope, full requirements and actual coercion partition. -/
  inductive RawForm (program : Program) (registry : Registry) :
      Scope → Context → Environment → Heap → ExpressionForm → List RequirementId →
      List SourceInference.CoercionStep → Outcome → Heap → Prop where
    | rawAtomicValue {scope context environment before after form requirements coercions value}
        (atomic : AtomicForm form)
        (valueRule : ExpressionFormEvaluates program context scope.evidence scope.source environment before
          form requirements coercions value after) :
        RawForm program registry scope context environment before form requirements coercions (.value value) after
    | rawAtomicFault {scope context environment before after form requirements coercions reason}
        (atomic : AtomicForm form)
        (faultRule : ExpressionFormFaults program context scope.evidence scope.source environment before
          form requirements coercions reason after) :
        RawForm program registry scope context environment before form requirements coercions (.fault (.semantic reason)) after
    | rawDirectArgumentsFault {scope context environment before after callee arguments instantiation name failure requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (children : Expressions program registry scope context environment before arguments (.fault failure) after) :
        RawForm program registry scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions (.fault failure) after
    | rawDirectApplied {scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions}
        (calleeOccurrence : Occurrence scope callee (.reference name (.declaration instantiation)))
        (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation)
        (children : Expressions program registry scope context environment before arguments (.values values) argumentsHeap)
        (callEvidence : DirectCallProducesEvidence context scope.evidence requirements coercions instantiation.predicates evidence)
        (invocation : Applies program registry scope context argumentsHeap (.global ⟨instantiation, evidence⟩) values outcome after) :
        RawForm program registry scope context environment before (.call callee arguments (.declaration instantiation))
          requirements coercions outcome after

  /-- An actual conversion edge uses either the independent primitive rule or
  a selected method body in its authentic staged scope. -/
  inductive CoercionStep (program : Program) (registry : Registry) :
      Scope → Context → Heap → SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionPrimitive {scope context heap step input output}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (applies : CoercionApplies context step input output) :
        CoercionStep program registry scope context heap step input (.value output) heap
    | coercionRequirement {scope context heap step input failed}
        (fault : RequirementListFaults context scope.evidence step.requirements failed) :
        CoercionStep program registry scope context heap step input (.fault (.semantic (.unsatisfiedRequirement failed))) heap
    | coercionPrimitiveInput {scope context heap step input actual}
        (noSourceMethod : ∀ bodyInstance dictionary,
          ¬ OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
            step.requirements bodyInstance dictionary)
        (invalid : PrimitiveCoercionInputInvalid step input)
        (actualType : ValueRuntimeType input actual) :
        CoercionStep program registry scope context heap step input (.fault (.semantic (.typeMismatch step.source actual))) heap
    | coercionMethod {scope context before bound after step input bodyInstance dictionary roots child
          parameterTypes bodyContext finalContext bodyEnvironment outcome result}
        (method : OperatorMethodSelected program context scope.evidence "Coerce" "coerce"
          step.requirements bodyInstance dictionary)
        (rootsEq : StatementRoots bodyInstance.source.roots roots)
        (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
        (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs [input] bodyEnvironment bound)
        (body : StatementsIn program registry true child bodyContext bodyEnvironment bound roots finalContext outcome after)
        (resultRule : BodyResult bodyInstance.resultType outcome result) :
        CoercionStep program registry scope context before step input result after

  /-- Ordered retained edges stop at the first semantic or staged failure. -/
  inductive CoercionPath (program : Program) (registry : Registry) :
      Scope → Context → Heap → List SourceInference.CoercionStep → Value → Outcome → Heap → Prop where
    | coercionsNil {scope context heap value} :
        CoercionPath program registry scope context heap [] value (.value value) heap
    | coercionsCons {scope context before middle after step steps input converted outcome}
        (head : CoercionStep program registry scope context before step input (.value converted) middle)
        (tail : CoercionPath program registry scope context middle steps converted outcome after) :
        CoercionPath program registry scope context before (step :: steps) input outcome after
    | coercionsFault {scope context before after step steps input failure}
        (head : CoercionStep program registry scope context before step input (.fault failure) after) :
        CoercionPath program registry scope context before (step :: steps) input (.fault failure) after

end

/-- Function bodies retain the original interface. Branch arms use `StatementsIn ... false`. -/
abbrev Statements (program : Program) (registry : Registry) := StatementsIn program registry true
namespace Statements
export StatementsIn (breaking continuing ifBreaking ifContinuing blockBreaking blockContinuing matchBreaking matchContinuing nil returnUnit returnValue returnFault tail discard expressionFault
  assignBare assignBareFault assignBareOperands assignBareUnbound assignBareDangling letUninitialized letInitialized letFault
  ifConditionFault ifReturned ifFault ifFallthrough blockReturned blockFault blockFallthrough whileReturned whileFault whileFallthrough matchReturned matchFault matchFallthrough
  forInitializerFault forReturned forFault forFallthrough)
end Statements

end Solcore.SourceSemantics.Staging.Recursive
