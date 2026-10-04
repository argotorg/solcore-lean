import Solcore.SourceSemantics.Staging.RecursiveTraceProperties
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Ordinary outcomes of the recursive staged profile project to the existing
independent Dynamic judgments. Stage rejection has no invented plain outcome.
The proof traverses callee, arguments and closure bodies together; it does not
assume an ordinary execution for compound expressions or function bodies. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

private def ExpressionPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (id : ExpressionId) (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => ExpressionEvaluates program context scope.evidence scope.source environment before id value after
  | .fault (.semantic reason) => ExpressionFaults program context scope.evidence scope.source environment before id reason after
  | .fault (.stage ..) => True

private def ExpressionsPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (ids : List ExpressionId) (outcome : ValuesOutcome) (after : Heap) : Prop :=
  match outcome with
  | .values values => ExpressionsEvaluate program context scope.evidence scope.source environment before ids values after
  | .fault (.semantic reason) => ExpressionsFault program context scope.evidence scope.source environment before ids reason after
  | .fault (.stage ..) => True

private def AppliesPlain (program : Program) (scope : Scope) (context : Context)
    (before : Heap) (callee : Value) (arguments : List Value) (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => ∃ invocationEvidence, CallableApplies program context scope.evidence invocationEvidence before callee arguments value after
  | .fault (.semantic reason) => ∃ invocationEvidence, CallableFaults program context scope.evidence invocationEvidence before callee arguments reason after
  | .fault (.stage ..) => True

private def StatementsPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (ids : List StatementId) (finalContext : Context)
    (outcome : BodyOutcome) (after : Heap) : Prop :=
  match outcome with
  | .fallthrough finalEnvironment => FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.fallthrough finalEnvironment) after
  | .returned value => FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.returned value) after
  | .fault (.semantic reason) => FunctionStatementsFault program context scope.evidence scope.source environment before ids finalContext reason after
  | .fault (.stage ..) => True

private theorem value_occurrence {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : ExpressionId} {form : ExpressionForm} {value : Value}
    (occurrence : Occurrence scope id form)
    (evaluates : ExpressionFormEvaluates program context scope.evidence scope.source environment before form [] [] value after) :
    ExpressionEvaluates program context scope.evidence scope.source environment before id value after := by
  obtain ⟨node, contains, shape, requirements, coercions⟩ := occurrence
  exact .intro contains (by simpa only [shape, requirements, coercions] using evaluates) (by simpa only [coercions] using CoercionPathExecutes.nil (program := program) (context := context) (evidence := scope.evidence) (heap := after) (value := value))

private theorem fault_occurrence {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : ExpressionId} {form : ExpressionForm} {reason : SemanticFault}
    (occurrence : Occurrence scope id form)
    (fault : ExpressionFormFaults program context scope.evidence scope.source environment before form [] [] reason after) :
    ExpressionFaults program context scope.evidence scope.source environment before id reason after := by
  obtain ⟨node, contains, shape, requirements, coercions⟩ := occurrence
  exact .form contains (by simpa only [shape, requirements, coercions] using fault)

private theorem prepend {program : Program} {scope : Scope} {context middleContext finalContext : Context}
    {environment middleEnvironment : Environment} {before middle after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {outcome : BodyOutcome}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id middleContext (.fallthrough middleEnvironment) middle)
    (tail : StatementsPlain program scope middleContext middleEnvironment middle rest finalContext outcome after) :
    StatementsPlain program scope context environment before (id :: rest) finalContext outcome after := by
  cases outcome with
  | fault failure =>
    cases failure with
    | stage => trivial
    | semantic reason =>
      cases rest with
      | nil => cases tail
      | cons next rest => exact .tail head tail
  | fallthrough next =>
    cases rest with
    | nil => cases tail; exact .singleton contains notTail head
    | cons next rest => exact .cons head tail
  | returned value =>
    cases rest with
    | nil => cases tail
    | cons next rest => exact .cons head tail

private theorem terminal {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {value : Value}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id context (.returned value) after) :
    StatementsPlain program scope context environment before (id :: rest) context (.returned value) after := by
  cases rest with
  | nil => exact .singleton contains notTail head
  | cons => exact .terminal head (.returned _)

private theorem head_fault {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {rest : List StatementId} {reason : SemanticFault}
    (head : StatementFaults program context scope.evidence scope.source environment before id reason after) :
    StatementsPlain program scope context environment before (id :: rest) context (.fault (.semantic reason)) after := by
  cases rest with
  | nil => exact .singleton head
  | cons => exact .head head

private theorem body_result {program : Program} {registry : Registry} {scope child : Scope}
    {context bodyContext finalContext : Context} {before bound after : Heap} {function : Closure}
    {arguments : List Value} {environment : Environment} {parameterTypes : List TypeSystem.Ty}
    {outcome : BodyOutcome} {result : Outcome}
    (selected : registry.Closure function child) (valid : ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
    (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
    (body : StatementsPlain program child bodyContext environment bound function.body finalContext outcome after)
    (resultRule : BodyResult function.resultType outcome result) :
    AppliesPlain program scope context before (.closure function) arguments result after := by
  have source := registry.source selected
  have evidence := registry.evidence selected
  generalize typeEq : function.resultType = type at resultRule
  cases resultRule with
  | returned =>
    exact ⟨function.evidence, .closure rfl valid parameters allocate (by simpa only [StatementsPlain, source, evidence] using body) rfl⟩
  | unit =>
    exact ⟨function.evidence, .closureUnit rfl valid typeEq parameters allocate (by simpa only [StatementsPlain, source, evidence] using body) ⟨_, rfl⟩⟩
  | @fault _ failure =>
    cases failure with
    | stage => trivial
    | semantic reason =>
      exact ⟨function.evidence, .closureBody rfl valid parameters allocate (by simpa only [StatementsPlain, source, evidence] using body)⟩

private theorem global_body_result {program : Program} {registry : Registry} {scope child : Scope}
    {context bodyContext finalContext : Context} {before bound after : Heap} {function : GlobalFunction}
    {bodyInstance : BodyInstance} {roots : List StatementId} {arguments : List Value}
    {environment : Environment} {parameterTypes : List TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (instantiates : FunctionInstantiates program function.instantiation bodyInstance)
    (covers : function.evidence.Covers bodyInstance.context)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance function.evidence roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : StatementsPlain program child bodyContext environment bound roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome result) :
    AppliesPlain program scope context before (.global function) arguments result after := by
  have source : child.source = bodyInstance.source := registry.source selected
  have evidence : child.evidence = function.evidence := registry.evidence selected
  generalize typeEq : bodyInstance.resultType = type at resultRule
  cases resultRule with
  | returned =>
    exact ⟨function.evidence, .global instantiates rfl covers
      (.returned covers rootsEq parameters allocate (by simpa only [StatementsPlain, source, evidence] using body) rfl)⟩
  | unit =>
    exact ⟨function.evidence, .global instantiates rfl covers
      (.unit covers typeEq rootsEq parameters allocate (by simpa only [StatementsPlain, source, evidence] using body) ⟨_, rfl⟩)⟩
  | @fault _ failure =>
    cases failure with
    | stage => trivial
    | semantic reason =>
      exact ⟨function.evidence, .globalBody instantiates rfl
        (.statements rootsEq parameters allocate (by simpa only [StatementsPlain, source, evidence] using body))⟩

private theorem projection {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry scope context environment before id outcome after) :
    ExpressionPlain program scope context environment before id outcome after := by
  induction trace using Expression.rec
    (motive_2 := fun scope context environment before ids outcome after _ => ExpressionsPlain program scope context environment before ids outcome after)
    (motive_3 := fun scope context before value arguments outcome after _ => AppliesPlain program scope context before value arguments outcome after)
    (motive_4 := fun scope context environment before ids finalContext outcome after _ => StatementsPlain program scope context environment before ids finalContext outcome after)
  case atomicValue contains _ uncoerced valueRule =>
    exact .intro contains (by simpa only [uncoerced] using valueRule) (by simpa only [uncoerced] using CoercionPathExecutes.nil)
  case atomicFault contains _ uncoerced faultRule =>
    exact .form contains (by simpa only [uncoerced] using faultRule)
  case group occurrence child ih =>
    rename_i outcome
    cases outcome with
    | value => exact value_occurrence occurrence (.group rfl ih)
    | fault failure => cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.group rfl ih)
  case pair occurrence first second a b =>
    exact value_occurrence occurrence (.tuple rfl (.cons a (.cons b .nil)) (.cons (.singleton _)))
  case pairLeftFault occurrence child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.tuple rfl (.head ih))
  case pairRightFault occurrence first second a b =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.tuple rfl (.tail a (.head b)))
  case tupleValue occurrence children pack ih =>
    exact value_occurrence occurrence (.tuple rfl ih pack)
  case tupleFault occurrence children ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.tuple rfl ih)
  case unary occurrence child applies ih =>
    exact value_occurrence occurrence (.unary (owned := []) rfl ih (.primitive applies))
  case unaryOperandFault occurrence child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.unaryOperand (owned := []) rfl ih)
  case unaryInvalid occurrence child invalid ih =>
    exact fault_occurrence occurrence (.unaryApply (owned := []) rfl ih (.primitive invalid))
  case binaryLeftFault occurrence first ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.binaryLeft (owned := []) rfl ih)
  case binaryLeftInvalid occurrence first invalid ih =>
    exact fault_occurrence occurrence (.binaryLeftOperand (owned := []) rfl ih invalid)
  case binaryShortCircuit occurrence first circuit ih =>
    exact value_occurrence occurrence (.binaryShortCircuit (owned := []) rfl ih circuit rfl)
  case binaryRightFault occurrence first continues second a b =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.binaryRight (owned := []) rfl a continues b)
  case binary occurrence first continues second applies a b =>
    exact value_occurrence occurrence (.binaryEvaluateRight (owned := []) rfl a continues b (.primitive applies))
  case binaryInvalid occurrence first continues second invalid a b =>
    exact fault_occurrence occurrence (.binaryApply (owned := []) rfl a continues b (.primitive invalid))
  case conditional occurrence test branch a b =>
    rename_i truth outcome
    cases outcome with
    | value => cases truth with
      | false => exact value_occurrence occurrence (.conditionalFalse rfl a b)
      | true => exact value_occurrence occurrence (.conditionalTrue rfl a b)
    | fault failure => cases failure with
      | stage => trivial
      | semantic => cases truth with
        | false => exact fault_occurrence occurrence (.conditionalFalseBranch rfl a b)
        | true => exact fault_occurrence occurrence (.conditionalTrueBranch rfl a b)
  case conditionalFault occurrence test ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.conditionalCondition rfl ih)
  case calleeFault occurrence child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.indirectCallee ih)
  case notCallable occurrence child invalid ih => exact fault_occurrence occurrence (.indirectNotCallable ih invalid)
  case rejected => trivial
  case argumentsFault occurrence child guard children a b =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact fault_occurrence occurrence (.indirectArguments a guard.callable b)
  case sourceArity occurrence child guard children mismatch a b =>
    exact fault_occurrence occurrence (.indirectSourceArity a b (Ne.symm mismatch))
  case applied occurrence uncoerced child guard children arity invocation a b c =>
    rename_i values outcome
    obtain ⟨packed, pack⟩ := ValuesPack.exists_pack values
    have appliedArity := children.length.symm.trans arity
    cases outcome with
    | value =>
      obtain ⟨invocationEvidence, applied⟩ := c
      exact value_occurrence occurrence (.indirectCall (by simp [uncoerced, coercionRequirementIds]) a b pack
        (by simpa only [uncoerced] using CoercionPathExecutes.nil) pack arity appliedArity applied)
    | fault failure => cases failure with
      | stage => trivial
      | semantic =>
        obtain ⟨invocationEvidence, applied⟩ := c
        exact fault_occurrence occurrence (.indirectApply a b pack (by simpa only [uncoerced] using CoercionPathExecutes.nil) pack arity appliedArity applied)
  case nil => exact ExpressionsEvaluate.nil
  case cons head tail a b => exact .cons a b
  case headFault head ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head ih
  case tailFault head tail a b =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .tail a b
  case builtin primitive => exact ⟨[], .builtin primitive⟩
  case builtinArity mismatch => exact ⟨[], .builtinArity mismatch⟩
  case builtinType arity mismatch => exact ⟨[], .builtinArgumentType arity mismatch⟩
  case closureArity mismatch => exact ⟨[], .closureArity mismatch⟩
  case globalArity instantiates mismatch => exact ⟨[], .globalArity instantiates mismatch⟩
  case global instantiates covers roots selected parameters allocate body result ih =>
    exact global_body_result instantiates covers roots selected parameters allocate ih result
  case closure selected valid parameters allocate body result ih => exact body_result selected valid parameters allocate ih result
  case nil => exact FunctionStatementsExecute.nil
  case returnUnit contains form => exact terminal contains (by intro e; simp [form]) (.returnUnit contains form)
  case returnValue contains form child ih => exact terminal contains (by intro e; simp [form]) (.returnValue contains form ih)
  case returnFault contains form child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact head_fault (.returnValue contains form ih)
  case tail contains form child ih => exact .tailExpression contains form ih
  case discard contains form child next a b => exact prepend contains (by intro e; simp [form]) (.expression contains form a) b
  case expressionFault contains form child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact head_fault (.expression contains form ih)
  case letUninitialized contains form mono extension allocate next ih =>
    exact prepend contains (by intro e; simp [form]) (.letUninitialized contains form mono extension allocate) ih
  case letInitialized contains form child mono extension allocate next a b =>
    exact prepend contains (by intro e; simp [form]) (.letInitialized contains form a mono extension allocate) b
  case letFault contains form mono child ih =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact head_fault (.letInitializer contains form mono ih)

/-- Successful recursively staged expressions retain their ordinary source
meaning, including all nested closure-body computations. -/
theorem Expression.value_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {value : Value}
    (trace : Expression program registry scope context environment before id (.value value) after) :
    ExpressionEvaluates program context scope.evidence scope.source environment before id value after := projection trace

/-- Ordinary semantic faults keep exactly their original reason and prefix
heap. The theorem does not erase a stage rejection into an unrelated fault. -/
theorem Expression.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {reason : SemanticFault}
    (trace : Expression program registry scope context environment before id (.fault (.semantic reason)) after) :
    ExpressionFaults program context scope.evidence scope.source environment before id reason after := projection trace

end Solcore.SourceSemantics.Staging.Recursive
