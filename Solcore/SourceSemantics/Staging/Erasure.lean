import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.Dynamic.Typing

/-!
# Erasure of staged traces

Ordinary outcomes of the recursive staged profile project to the independent dynamic semantics, and
ordinary executions lift back. Main declarations: `Staging.Recursive.Expression.value_plain`,
`Staging.Recursive.Expression.semanticFault_plain`, `Staging.Recursive.Expressions.values_plain`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveErasure
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

private def RawFormPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List SourceInference.CoercionStep)
    (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => ExpressionFormEvaluates program context scope.evidence scope.source environment before form requirements coercions value after
  | .fault (.semantic reason) => ExpressionFormFaults program context scope.evidence scope.source environment before form requirements coercions reason after
  | .fault (.stage ..) => True

private def CoercionStepPlain (program : Program) (scope : Scope) (context : Context)
    (before : Heap) (step : SourceInference.CoercionStep) (input : Value) (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => CoercionStepExecutes program context scope.evidence before step input value after
  | .fault (.semantic reason) => CoercionStepFaults program context scope.evidence before step input reason after
  | .fault (.stage ..) => True

private def CoercionPathPlain (program : Program) (scope : Scope) (context : Context)
    (before : Heap) (steps : List SourceInference.CoercionStep) (input : Value) (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => CoercionPathExecutes program context scope.evidence before steps input value after
  | .fault (.semantic reason) => CoercionPathFaults program context scope.evidence before steps input reason after
  | .fault (.stage ..) => True

def StatementsPlain (program : Program) (mode : Bool) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (ids : List StatementId) (finalContext : Context)
    (outcome : BodyOutcome) (after : Heap) : Prop :=
  match outcome with
  | .fallthrough finalEnvironment => if mode then
      FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.fallthrough finalEnvironment) after
    else StatementsExecute program context scope.evidence scope.source environment before ids finalContext (.fallthrough finalEnvironment) after
  | .returned value => if mode then
      FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.returned value) after
    else StatementsExecute program context scope.evidence scope.source environment before ids finalContext (.returned value) after
  | .breaking finalEnvironment => if mode then
      FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.breaking finalEnvironment) after
    else StatementsExecute program context scope.evidence scope.source environment before ids finalContext (.breaking finalEnvironment) after
  | .continuing finalEnvironment => if mode then
      FunctionStatementsExecute program context scope.evidence scope.source environment before ids finalContext (.continuing finalEnvironment) after
    else StatementsExecute program context scope.evidence scope.source environment before ids finalContext (.continuing finalEnvironment) after
  | .fault (.semantic reason) => if mode then
      FunctionStatementsFault program context scope.evidence scope.source environment before ids finalContext reason after
    else StatementsFault program context scope.evidence scope.source environment before ids finalContext reason after
  | .fault (.stage ..) => True


/-- Pattern selection itself contains no staged evaluation; only its actual
scrutinee and chosen body are erased, retaining the original allocations. -/
def MatchPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (resolution : MatchResolution)
    (outcome : BodyOutcome) (after : Heap) : Prop :=
  ∀ id node, ContainsStatement scope.source id node → node.form = .matchWith resolution →
  match outcome with
  | .fallthrough finalEnvironment => StatementExecutes program context scope.evidence scope.source environment before id
      context (.fallthrough finalEnvironment) after
  | .returned value => StatementExecutes program context scope.evidence scope.source environment before id context (.returned value) after
  | .breaking finalEnvironment => StatementExecutes program context scope.evidence scope.source environment before id context (.breaking finalEnvironment) after
  | .continuing finalEnvironment => StatementExecutes program context scope.evidence scope.source environment before id context (.continuing finalEnvironment) after
  | .fault (.semantic reason) => StatementFaults program context scope.evidence scope.source environment before id reason after
  | .fault (.stage ..) => True

theorem MatchPlain.arm {program : Program} {scope : Scope} {context armContext finalContext : Context}
    {environment armEnvironment : Environment} {before middle hidden bound after : Heap}
    {resolution : MatchResolution} {node : ExpressionNode} {value : Value} {location : Location}
    {statements : List StatementId} {bindings : List (TypedBinder × Value)} {outcome : BodyOutcome}
    (contains : ContainsExpression scope.source resolution.scrutinee node)
    (scrutinee : ExpressionEvaluates program context scope.evidence scope.source environment before resolution.scrutinee value middle)
    (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
    (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
    (extended : BindersExtend scope.source.owner context (bindings.map Prod.fst) armContext)
    (allocated : BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
    (body : StatementsPlain program false scope armContext armEnvironment bound statements finalContext outcome after) :
    MatchPlain program scope context environment before resolution (outcome.restore environment) after := by
  intro id statement found form
  cases outcome with
  | fallthrough => exact .matchArm found form contains scrutinee hiddenAllocated selected rfl rfl extended allocated body
  | returned => exact .matchArm found form contains scrutinee hiddenAllocated selected rfl rfl extended allocated body
  | breaking => exact .matchArm found form contains scrutinee hiddenAllocated selected rfl rfl extended allocated body
  | continuing => exact .matchArm found form contains scrutinee hiddenAllocated selected rfl rfl extended allocated body
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .matchArmBody found form contains scrutinee hiddenAllocated selected rfl rfl extended allocated body

theorem MatchPlain.default {program : Program} {scope : Scope} {context finalContext : Context}
    {environment : Environment} {before middle hidden after : Heap}
    {resolution : MatchResolution} {node : ExpressionNode} {value : Value} {location : Location}
    {statements : List StatementId} {outcome : BodyOutcome}
    (contains : ContainsExpression scope.source resolution.scrutinee node)
    (scrutinee : ExpressionEvaluates program context scope.evidence scope.source environment before resolution.scrutinee value middle)
    (hiddenAllocated : Heap.Allocates middle node.type (some value) location hidden)
    (selected : MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
    (body : StatementsPlain program false scope context environment hidden statements finalContext outcome after) :
    MatchPlain program scope context environment before resolution (outcome.restore environment) after := by
  intro id statement found form
  cases outcome with
  | fallthrough => exact .matchDefault found form contains scrutinee hiddenAllocated selected body
  | returned => exact .matchDefault found form contains scrutinee hiddenAllocated selected body
  | breaking => exact .matchDefault found form contains scrutinee hiddenAllocated selected body
  | continuing => exact .matchDefault found form contains scrutinee hiddenAllocated selected body
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .matchDefaultBody found form contains scrutinee hiddenAllocated selected body

/-- Ordinary loop outcomes retain their finite independent iterations. -/
def WhilePlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (condition : ExpressionId)
    (statements : List StatementId) (outcome : BodyOutcome) (after : Heap) : Prop :=
  match outcome with
  | .fallthrough finalEnvironment => WhileExecutes program context scope.evidence scope.source environment before
      condition statements context (.fallthrough finalEnvironment) after
  | .returned value => WhileExecutes program context scope.evidence scope.source environment before
      condition statements context (.returned value) after
  | .breaking finalEnvironment => WhileExecutes program context scope.evidence scope.source environment before
      condition statements context (.breaking finalEnvironment) after
  | .continuing finalEnvironment => WhileExecutes program context scope.evidence scope.source environment before
      condition statements context (.continuing finalEnvironment) after
  | .fault (.semantic reason) => WhileFaults program context scope.evidence scope.source environment before
      condition statements reason after
  | .fault (.stage ..) => True

theorem WhilePlain.next {program : Program} {scope : Scope} {context innerContext : Context}
    {environment innerEnvironment : Environment} {before middle bodyHeap after : Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : BodyOutcome}
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool true) middle)
    (body : StatementsExecute program context scope.evidence scope.source environment middle statements
      innerContext (.fallthrough innerEnvironment) bodyHeap)
    (next : WhilePlain program scope context environment bodyHeap condition statements outcome after) :
    WhilePlain program scope context environment before condition statements outcome after := by
  cases outcome with
  | returned => exact .nextFallthrough test body next
  | breaking => exact .nextFallthrough test body next
  | continuing => exact .nextFallthrough test body next
  | fallthrough => exact .nextFallthrough test body next
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .nextFallthrough test body next

theorem WhilePlain.continued {program : Program} {scope : Scope} {context innerContext : Context}
    {environment innerEnvironment : Environment} {before middle bodyHeap after : Heap}
    {condition : ExpressionId} {statements : List StatementId} {outcome : BodyOutcome}
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool true) middle)
    (body : StatementsExecute program context scope.evidence scope.source environment middle statements
      innerContext (.continuing innerEnvironment) bodyHeap)
    (next : WhilePlain program scope context environment bodyHeap condition statements outcome after) :
    WhilePlain program scope context environment before condition statements outcome after := by
  cases outcome with
  | returned => exact .nextContinue test body next
  | breaking => exact .nextContinue test body next
  | continuing => exact .nextContinue test body next
  | fallthrough => exact .nextContinue test body next
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .nextContinue test body next


/-- Successful header prefixes retain the exact stopping context and bindings. -/
def ForItemsPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (items : List ForItemForm) (finalContext : Context)
    (outcome : ForItemsOutcome) (after : Heap) : Prop :=
  match outcome with
  | .done finalEnvironment => ForItemsExecute program context scope.evidence scope.source environment before
      items finalContext finalEnvironment after
  | .fault (.semantic reason) => ForItemsFault program context scope.evidence scope.source environment before
      items finalContext reason after
  | .fault (.stage ..) => True

theorem ForItemsPlain.prepend {program : Program} {scope : Scope} {context middleContext finalContext : Context}
    {environment middleEnvironment : Environment} {before middle after : Heap}
    {item : ForItemForm} {items : List ForItemForm} {outcome : ForItemsOutcome}
    (head : ForItemExecutes program context scope.evidence scope.source environment before item middleContext middleEnvironment middle)
    (tail : ForItemsPlain program scope middleContext middleEnvironment middle items finalContext outcome after) :
    ForItemsPlain program scope context environment before (item :: items) finalContext outcome after := by
  cases outcome with
  | done => exact .cons head tail
  | fault failure => cases failure with
    | semantic => exact .tail head tail
    | stage => trivial

def ForLoopPlain (program : Program) (scope : Scope) (context : Context)
    (environment : Environment) (before : Heap) (condition : ExpressionId)
    (post : List ForItemForm) (body : List StatementId) (outcome : BodyOutcome) (after : Heap) : Prop :=
  match outcome with
  | .fallthrough finalEnvironment => ForLoopExecutes program context scope.evidence scope.source environment before
      condition post body context (.fallthrough finalEnvironment) after
  | .returned value => ForLoopExecutes program context scope.evidence scope.source environment before
      condition post body context (.returned value) after
  | .breaking finalEnvironment => ForLoopExecutes program context scope.evidence scope.source environment before
      condition post body context (.breaking finalEnvironment) after
  | .continuing finalEnvironment => ForLoopExecutes program context scope.evidence scope.source environment before
      condition post body context (.continuing finalEnvironment) after
  | .fault (.semantic reason) => ForLoopFaults program context scope.evidence scope.source environment before
      condition post body reason after
  | .fault (.stage ..) => True

theorem ForLoopPlain.next {program : Program} {scope : Scope} {context innerContext postContext : Context}
    {environment innerEnvironment postEnvironment : Environment} {before middle bodyHeap postHeap after : Heap}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {outcome : BodyOutcome}
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool true) middle)
    (branch : StatementsExecute program context scope.evidence scope.source environment middle body
      innerContext (.fallthrough innerEnvironment) bodyHeap)
    (postTrace : ForItemsExecute program context scope.evidence scope.source environment bodyHeap post
      postContext postEnvironment postHeap)
    (next : ForLoopPlain program scope context environment postHeap condition post body outcome after) :
    ForLoopPlain program scope context environment before condition post body outcome after := by
  cases outcome with
  | returned => exact .nextFallthrough test branch postTrace next
  | breaking => exact .nextFallthrough test branch postTrace next
  | continuing => exact .nextFallthrough test branch postTrace next
  | fallthrough => exact .nextFallthrough test branch postTrace next
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .nextFallthrough test branch postTrace next

theorem ForLoopPlain.continued {program : Program} {scope : Scope} {context innerContext postContext : Context}
    {environment innerEnvironment postEnvironment : Environment} {before middle bodyHeap postHeap after : Heap}
    {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId} {outcome : BodyOutcome}
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool true) middle)
    (branch : StatementsExecute program context scope.evidence scope.source environment middle body
      innerContext (.continuing innerEnvironment) bodyHeap)
    (postTrace : ForItemsExecute program context scope.evidence scope.source environment bodyHeap post
      postContext postEnvironment postHeap)
    (next : ForLoopPlain program scope context environment postHeap condition post body outcome after) :
    ForLoopPlain program scope context environment before condition post body outcome after := by
  cases outcome with
  | returned => exact .nextContinue test branch postTrace next
  | breaking => exact .nextContinue test branch postTrace next
  | continuing => exact .nextContinue test branch postTrace next
  | fallthrough => exact .nextContinue test branch postTrace next
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .nextContinue test branch postTrace next

private theorem value_occurrence {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : ExpressionId} {form : ExpressionForm} {value : Value}
    {requirements : List RequirementId}
    (occurrence : Occurrence scope id form requirements)
    (evaluates : ExpressionFormEvaluates program context scope.evidence scope.source environment before form requirements [] value after) :
    ExpressionEvaluates program context scope.evidence scope.source environment before id value after := by
  obtain ⟨node, contains, shape, actualRequirements, coercions⟩ := occurrence
  exact .intro contains (by simpa only [shape, actualRequirements, coercions] using evaluates) (by simpa only [coercions] using CoercionPathExecutes.nil (program := program) (context := context) (evidence := scope.evidence) (heap := after) (value := value))

private theorem fault_occurrence {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : ExpressionId} {form : ExpressionForm} {reason : SemanticFault}
    {requirements : List RequirementId}
    (occurrence : Occurrence scope id form requirements)
    (fault : ExpressionFormFaults program context scope.evidence scope.source environment before form requirements [] reason after) :
    ExpressionFaults program context scope.evidence scope.source environment before id reason after := by
  obtain ⟨node, contains, shape, actualRequirements, coercions⟩ := occurrence
  exact .form contains (by simpa only [shape, actualRequirements, coercions] using fault)

theorem StatementsPlain.prepend {mode : Bool} {program : Program} {scope : Scope} {context middleContext finalContext : Context}
    {environment middleEnvironment : Environment} {before middle after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {outcome : BodyOutcome}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id middleContext (.fallthrough middleEnvironment) middle)
    (tail : StatementsPlain program mode scope middleContext middleEnvironment middle rest finalContext outcome after) :
    StatementsPlain program mode scope context environment before (id :: rest) finalContext outcome after := by
  cases mode with
  | false =>
      cases outcome with
        | fault failure => cases failure with
          | stage => trivial
          | semantic => exact .tail head tail
        | fallthrough => exact .cons head tail
        | returned => exact .cons head tail
        | breaking => exact .cons head tail
        | continuing => exact .cons head tail
  | true =>
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
      | returned value | breaking value | continuing value =>
        cases rest with
        | nil => cases tail
        | cons next rest => exact .cons head tail

theorem StatementsPlain.terminal {mode : Bool} {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {value : Value}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id context (.returned value) after) :
    StatementsPlain program mode scope context environment before (id :: rest) context (.returned value) after := by
  cases mode with
  | false =>
      exact StatementsExecute.terminal head (.returned _)
  | true =>
      cases rest with
      | nil => exact .singleton contains notTail head
      | cons => exact FunctionStatementsExecute.terminal head (.returned _)
theorem StatementsPlain.terminal_breaking {mode : Bool} {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {finalEnvironment : Environment}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id context (.breaking finalEnvironment) after) :
    StatementsPlain program mode scope context environment before (id :: rest) context (.breaking finalEnvironment) after := by
  cases mode with
  | false =>
      exact StatementsExecute.terminal head (.breaking _)
  | true =>
      cases rest with
      | nil => exact .singleton contains notTail head
      | cons => exact FunctionStatementsExecute.terminal head (.breaking _)
theorem StatementsPlain.terminal_continuing {mode : Bool} {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {finalEnvironment : Environment}
    (contains : ContainsStatement scope.source id node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : StatementExecutes program context scope.evidence scope.source environment before id context (.continuing finalEnvironment) after) :
    StatementsPlain program mode scope context environment before (id :: rest) context (.continuing finalEnvironment) after := by
  cases mode with
  | false =>
      exact StatementsExecute.terminal head (.continuing _)
  | true =>
      cases rest with
      | nil => exact .singleton contains notTail head
      | cons => exact FunctionStatementsExecute.terminal head (.continuing _)

theorem StatementsPlain.head_fault {mode : Bool} {program : Program} {scope : Scope} {context : Context}
    {environment : Environment} {before after : Heap} {id : StatementId} {rest : List StatementId} {reason : SemanticFault}
    (head : StatementFaults program context scope.evidence scope.source environment before id reason after) :
    StatementsPlain program mode scope context environment before (id :: rest) context (.fault (.semantic reason)) after := by
  cases mode with
  | false =>
      exact .head head
  | true =>
      cases rest with
      | nil => exact .singleton head
      | cons => exact .head head

theorem StatementsPlain.discard_value {program : Program} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before middle after : Heap}
    {id : StatementId} {node : StatementNode} {rest : List StatementId} {expression : ExpressionId}
    {value : Value} {outcome : BodyOutcome}
    (contains : ContainsStatement scope.source id node) (form : node.form = .expression expression false)
    (child : ExpressionEvaluates program context scope.evidence scope.source environment before expression value middle)
    (tail : StatementsPlain program false scope context environment middle rest finalContext outcome after) :
    StatementsPlain program false scope context environment before (id :: rest) finalContext outcome after := by
  cases outcome with
  | fault failure => cases failure with
    | stage => trivial
    | semantic => exact .tail (.expression contains form child) tail
  | fallthrough => exact .cons (.expression contains form child) tail
  | returned => exact .cons (.expression contains form child) tail
  | breaking => exact .cons (.expression contains form child) tail
  | continuing => exact .cons (.expression contains form child) tail

theorem StatementsPlain.if_execute {program : Program} {scope : Scope}
    {context innerContext : Context} {environment : Environment} {before middle after : Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)} {truth : Bool}
    {outcome : ControlOutcome}
    (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool truth) middle)
    (branch : StatementsExecute program context scope.evidence scope.source environment middle
      (if truth then thenBody else elseBody.getD []) innerContext outcome after) :
    StatementExecutes program context scope.evidence scope.source environment before id context
      (restoreControl environment outcome) after := by
  cases truth with
  | true => exact .ifTrue contains form test branch
  | false =>
      cases elseBody with
      | none => cases branch; exact .ifFalseWithoutElse contains form test
      | some statements => exact .ifFalseWithElse contains form test branch

theorem StatementsPlain.if_fault {program : Program} {scope : Scope}
    {context innerContext : Context} {environment : Environment} {before middle after : Heap}
    {id : StatementId} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)} {truth : Bool} {reason : SemanticFault}
    (contains : ContainsStatement scope.source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (test : ExpressionEvaluates program context scope.evidence scope.source environment before condition (.bool truth) middle)
    (branch : StatementsFault program context scope.evidence scope.source environment middle
      (if truth then thenBody else elseBody.getD []) innerContext reason after) :
    StatementFaults program context scope.evidence scope.source environment before id reason after := by
  cases truth with
  | true => exact .ifTrueBody contains form test branch
  | false =>
      cases elseBody with
      | none => cases branch
      | some statements => exact .ifFalseBody contains form test branch

private theorem body_result {program : Program} {registry : Registry} {scope child : Scope}
    {context bodyContext finalContext : Context} {before copied bound after : Heap} {function : Closure}
    {arguments : List Value} {entry environment : Environment} {parameterTypes : List TypeSystem.Ty}
    {outcome : BodyOutcome} {result : Outcome}
    (selected : registry.Closure function child) (valid : ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters parameterTypes bodyContext)
    (copy : EnvironmentCopies function.source function.captured before entry copied)
    (allocate : BindersAllocate entry copied function.parameters arguments environment bound)
    (body : StatementsPlain program true child bodyContext environment bound function.body finalContext outcome after)
    (resultRule : BodyResult function.resultType outcome result) :
    AppliesPlain program scope context before (.closure function) arguments result after := by
  have source := registry.source selected
  have evidence := registry.evidence selected
  generalize typeEq : function.resultType = type at resultRule
  cases resultRule with
  | returned =>
    exact ⟨function.evidence, .closure rfl valid parameters copy allocate (by simpa [StatementsPlain, source, evidence] using body) rfl⟩
  | unit =>
    exact ⟨function.evidence, .closureUnit rfl valid typeEq parameters copy allocate (by simpa [StatementsPlain, source, evidence] using body) ⟨_, rfl⟩⟩
  | breaking =>
    exact ⟨function.evidence, .closureControlEscape rfl valid parameters copy allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inl ⟨_, rfl⟩)⟩
  | continuing =>
    exact ⟨function.evidence, .closureControlEscape rfl valid parameters copy allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inr ⟨_, rfl⟩)⟩
  | @fault _ failure =>
    cases failure with
    | stage => trivial
    | semantic reason =>
      exact ⟨function.evidence, .closureBody rfl valid parameters copy allocate (by simpa [StatementsPlain, source, evidence] using body)⟩

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
    (body : StatementsPlain program true child bodyContext environment bound roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome result) :
    AppliesPlain program scope context before (.global function) arguments result after := by
  have source : child.source = bodyInstance.source := registry.source selected
  have evidence : child.evidence = function.evidence := registry.evidence selected
  generalize typeEq : bodyInstance.resultType = type at resultRule
  cases resultRule with
  | returned =>
    exact ⟨function.evidence, .global instantiates rfl covers
      (.returned covers rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) rfl)⟩
  | unit =>
    exact ⟨function.evidence, .global instantiates rfl covers
      (.unit covers typeEq rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) ⟨_, rfl⟩)⟩
  | breaking =>
    exact ⟨function.evidence, .globalBody instantiates rfl (.controlEscape rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inl ⟨_, rfl⟩))⟩
  | continuing =>
    exact ⟨function.evidence, .globalBody instantiates rfl (.controlEscape rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inr ⟨_, rfl⟩))⟩
  | @fault _ failure =>
    cases failure with
    | stage => trivial
    | semantic reason =>
      exact ⟨function.evidence, .globalBody instantiates rfl
        (.statements rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body))⟩

private def MethodPlain (program : Program) (bodyInstance : BodyInstance)
    (dictionary : EvidenceEnvironment) (before : Heap) (arguments : List Value)
    (outcome : Outcome) (after : Heap) : Prop :=
  match outcome with
  | .value value => BodyInvokes program bodyInstance dictionary before arguments value after
  | .fault (.semantic reason) => BodyFaults program bodyInstance dictionary before arguments reason after
  | .fault (.stage ..) => True

private theorem method_body_result {program : Program} {registry : Registry} {child : Scope}
    {bodyContext finalContext : Context} {before bound after : Heap}
    {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {roots : List StatementId} {arguments : List Value}
    {environment : Environment} {parameterTypes : List TypeSystem.Ty} {outcome : BodyOutcome} {result : Outcome}
    (covers : dictionary.Covers bodyInstance.context)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : StatementsPlain program true child bodyContext environment bound roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome result) :
    MethodPlain program bodyInstance dictionary before arguments result after := by
  have source : child.source = bodyInstance.source := registry.source selected
  have evidence : child.evidence = dictionary := registry.evidence selected
  generalize typeEq : bodyInstance.resultType = type at resultRule
  cases resultRule with
  | returned =>
    exact .returned covers rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) rfl
  | unit =>
    exact .unit covers typeEq rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) ⟨_, rfl⟩
  | breaking =>
    exact .controlEscape rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inl ⟨_, rfl⟩)
  | continuing =>
    exact .controlEscape rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body) (Or.inr ⟨_, rfl⟩)
  | @fault _ failure =>
    cases failure with
    | stage => trivial
    | semantic =>
      exact .statements rootsEq parameters allocate (by simpa [StatementsPlain, source, evidence] using body)

private theorem global_applies_evidence {program : Program} {context : Context}
    {callerEvidence invocationEvidence : EvidenceEnvironment} {before after : Heap}
    {function : GlobalFunction} {arguments : List Value} {result : Value}
    (applies : CallableApplies program context callerEvidence invocationEvidence before
      (.global function) arguments result after) :
    CallableApplies program context callerEvidence function.evidence before
      (.global function) arguments result after := by
  cases applies with
  | global instantiates same covers body => cases same; exact .global instantiates rfl covers body

private theorem global_fault_evidence {program : Program} {context : Context}
    {callerEvidence invocationEvidence : EvidenceEnvironment} {before after : Heap}
    {function : GlobalFunction} {arguments : List Value} {reason : SemanticFault}
    (fault : CallableFaults program context callerEvidence invocationEvidence before
      (.global function) arguments reason after) :
    CallableFaults program context callerEvidence function.evidence before
      (.global function) arguments reason after := by
  cases fault with
  | notCallable invalid => exact False.elim (invalid trivial)
  | globalSignatureMissing missing => exact .globalSignatureMissing missing
  | globalBodyMissing missing => exact .globalBodyMissing missing
  | globalArity instantiates mismatch => exact .globalArity instantiates mismatch
  | globalBody instantiates same body => cases same; exact .globalBody instantiates rfl body

private theorem builtin_applies_evidence {program : Program} {context : Context}
    {callerEvidence invocationEvidence : EvidenceEnvironment} {before after : Heap}
    {function : BuiltinFunction} {arguments : List Value} {result : Value}
    (applies : CallableApplies program context callerEvidence invocationEvidence before
      (.builtin function) arguments result after) :
    CallableApplies program context callerEvidence [] before
      (.builtin function) arguments result after := by
  cases applies with
  | builtin primitive => exact .builtin primitive

private theorem builtin_fault_evidence {program : Program} {context : Context}
    {callerEvidence invocationEvidence : EvidenceEnvironment} {before after : Heap}
    {function : BuiltinFunction} {arguments : List Value} {reason : SemanticFault}
    (fault : CallableFaults program context callerEvidence invocationEvidence before
      (.builtin function) arguments reason after) :
    CallableFaults program context callerEvidence [] before
      (.builtin function) arguments reason after := by
  cases fault with
  | notCallable invalid => exact False.elim (invalid trivial)
  | builtinArity mismatch => exact .builtinArity mismatch
  | builtinArgumentType arity mismatch => exact .builtinArgumentType arity mismatch

local macro "erase_recursive_plain" : tactic =>
  `(tactic| (
    case generalizedLocal contains form layout lookup read descriptor contextFields instantiation coercions pathIH =>
      rename_i outcome
      cases outcome with
      | value => exact .generalizedLocal contains form layout lookup read descriptor contextFields instantiation pathIH
      | fault failure => cases failure with
        | semantic => exact .generalizedLocalCoercion contains form layout lookup read descriptor contextFields instantiation pathIH
        | stage => trivial
    case generalizedLocalRequirement contains form layout lookup read descriptor contextFields selection fault =>
      exact .generalizedLocalRequirement contains form layout lookup read descriptor contextFields selection fault
    case letGeneralized contains form snapshot captures polymorphic extension allocated next nextIH =>
      exact StatementsPlain.prepend contains (by intro e; simp [form])
        (.letInitializedGeneralized contains form snapshot captures polymorphic extension allocated) nextIH
    case initializedGeneralized snapshot captures polymorphic extension allocated next nextIH =>
      exact ForItemsPlain.prepend (.letInitializedGeneralized snapshot captures polymorphic extension allocated) nextIH
    case coercedValue contains _nonempty raw path rawIH pathIH =>
      rename_i outcome
      cases outcome with
      | value => exact .intro contains rawIH pathIH
      | fault failure => cases failure with
        | semantic => exact .coercion contains rawIH pathIH
        | stage => trivial
    case coercedFault contains _nonempty raw rawIH =>
      rename_i failure
      cases failure with
      | semantic => exact .form contains rawIH
      | stage => trivial
    case rawAtomicValue _ valueRule => exact valueRule
    case rawAtomicFault _ faultRule => exact faultRule
    case rawDirectArgumentsFault calleeOccurrence children childrenIH =>
      rename_i failure requirements coercions
      cases failure with
      | stage => trivial
      | semantic =>
        obtain ⟨node, found, form, _requirements, _coercions⟩ := calleeOccurrence
        exact .directArguments found form childrenIH
    case rawDirectApplied calleeOccurrence valid children callEvidence invocation childrenIH invocationIH =>
      rename_i evidence outcome requirements coercions
      cases outcome with
      | value =>
        obtain ⟨_, applied⟩ := invocationIH
        obtain ⟨node, found, form, requirements, coercions⟩ := calleeOccurrence
        exact .directCall found form requirements coercions valid childrenIH callEvidence (global_applies_evidence applied)
      | fault failure => cases failure with
        | stage => trivial
        | semantic =>
          obtain ⟨_, fault⟩ := invocationIH
          exact .directApply childrenIH callEvidence (global_fault_evidence fault)
    case coercionPrimitive noSource applies => exact .primitive noSource applies
    case coercionRequirement fault => exact .requirement fault
    case coercionPrimitiveInput noSource invalid actual => exact .primitiveInput noSource invalid actual
    case coercionMethod method roots selected parameters allocate body result bodyIH =>
      rename_i outcome resultOutcome
      have plain := method_body_result (by cases method; assumption) roots selected parameters allocate bodyIH result
      cases resultOutcome with
      | value => exact .method method plain
      | fault failure => cases failure with
        | semantic => exact .method method plain
        | stage => trivial
    case coercionsNil => exact .nil
    case coercionsCons head tail headIH tailIH =>
      rename_i outcome
      cases outcome with
      | value => exact .cons headIH tailIH
      | fault failure => cases failure with
        | semantic => exact .tail headIH tailIH
        | stage => trivial
    case coercionsFault head headIH =>
      rename_i failure
      cases failure with
      | semantic => exact .head headIH
      | stage => trivial
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
    case constructorValue occurrence valid children ih =>
      exact value_occurrence occurrence (.constructor rfl valid ih)
    case constructorFault occurrence children ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.constructorArgument rfl ih)
    case indexBaseFault occurrence first a =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.indexBase rfl a)
    case indexKeyFault occurrence first second a b =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.indexKey rfl a b)
    case indexResult occurrence first second result a b =>
      cases result with
      | found shape located => cases shape; exact value_occurrence occurrence (.indexFound rfl a b located)
      | default shape absent defaulted => cases shape; exact value_occurrence occurrence (.indexDefault rfl a b absent defaulted)
      | shape invalid => exact fault_occurrence occurrence (.indexShape rfl a b invalid)
      | keyType shape typed mismatch => cases shape; exact fault_occurrence occurrence (.indexKeyType rfl a b typed mismatch)
      | unavailable shape typed absent missing => cases shape; exact fault_occurrence occurrence (.indexDefaultUnavailable rfl a b typed absent missing)
    case unary occurrence child applies ih =>
      exact value_occurrence occurrence (.unary (owned := []) rfl ih (.primitive applies))
    case unaryOperandFault occurrence child ih =>
      rename_i failure requirements
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.unaryOperand (owned := requirements) (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) ih)
    case unaryInvalid occurrence child invalid ih =>
      exact fault_occurrence occurrence (.unaryApply (owned := []) rfl ih (.primitive invalid))
    case binaryLeftFault occurrence first ih =>
      rename_i failure requirements
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.binaryLeft (owned := requirements) (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) ih)
    case binaryLeftInvalid occurrence first invalid ih =>
      exact fault_occurrence occurrence (.binaryLeftOperand (owned := []) rfl ih invalid)
    case binaryShortCircuit occurrence first circuit ih =>
      exact value_occurrence occurrence (.binaryShortCircuit (owned := []) rfl ih circuit rfl)
    case binaryRightFault occurrence first continues second a b =>
      rename_i failure requirements
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.binaryRight (owned := requirements) (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) a continues b)
    case binary occurrence first continues second applies a b =>
      exact value_occurrence occurrence (.binaryEvaluateRight (owned := []) rfl a continues b (.primitive applies))
    case binaryInvalid occurrence first continues second invalid a b =>
      exact fault_occurrence occurrence (.binaryApply (owned := []) rfl a continues b (.primitive invalid))
    case unaryMethod occurrence dispatch method operand rootsEq selected parameters allocate body resultRule operandIH bodyIH =>
      rename_i outcome result
      have plain := method_body_result (by cases method; assumption) rootsEq selected parameters allocate bodyIH resultRule
      cases result with
      | value => exact value_occurrence occurrence (.unary (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) operandIH (.method dispatch method plain))
      | fault failure => cases failure with
        | stage => trivial
        | semantic => exact fault_occurrence occurrence (.unaryApply (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) operandIH (.method dispatch method plain))
    case binaryMethod occurrence dispatch method first continues second rootsEq selected parameters allocate body resultRule firstIH secondIH bodyIH =>
      rename_i outcome result
      have plain := method_body_result (by cases method; assumption) rootsEq selected parameters allocate bodyIH resultRule
      cases result with
      | value => exact value_occurrence occurrence (.binaryEvaluateRight (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) firstIH continues secondIH (.method dispatch method plain))
      | fault failure => cases failure with
        | stage => trivial
        | semantic => exact fault_occurrence occurrence (.binaryApply (by simp [OrdinaryRequirementLayout, coercionRequirementIds]) firstIH continues secondIH (.method dispatch method plain))
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
    case builtinArgumentsFault occurrence children ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact fault_occurrence occurrence (.builtinArguments rfl ih)
    case builtinApplied occurrence children invocation a b =>
      rename_i outcome
      cases outcome with
      | value =>
        obtain ⟨_, applied⟩ := b
        exact value_occurrence occurrence (.builtinCall rfl a (builtin_applies_evidence applied))
      | fault failure => cases failure with
        | stage => trivial
        | semantic =>
          obtain ⟨_, fault⟩ := b
          exact fault_occurrence occurrence (.builtinApply rfl a (builtin_fault_evidence fault))
    case directArgumentsFault occurrence calleeOccurrence children ih =>
      rename_i failure requirements
      cases failure with
      | stage => trivial
      | semantic =>
        obtain ⟨node, found, form, _requirements, _coercions⟩ := calleeOccurrence
        exact fault_occurrence occurrence (.directArguments found form ih)
    case directApplied occurrence calleeOccurrence valid children callEvidence invocation a b =>
      rename_i evidence outcome requirements
      cases outcome with
      | value =>
        obtain ⟨_, applied⟩ := b
        obtain ⟨node, found, form, requirements, coercions⟩ := calleeOccurrence
        exact value_occurrence occurrence (.directCall found form requirements coercions valid a
          callEvidence (global_applies_evidence applied))
      | fault failure => cases failure with
        | stage => trivial
        | semantic =>
          obtain ⟨_, fault⟩ := b
          exact fault_occurrence occurrence (.directApply a callEvidence (global_fault_evidence fault))
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
    case closure selected valid parameters copy allocate body result ih =>
      exact body_result selected valid parameters copy allocate ih result
    case nil => rename_i mode _ _ _; intro heap; cases mode <;> exact .nil
    case returnUnit contains form => exact StatementsPlain.terminal contains (by intro e; simp [form]) (.returnUnit contains form)
    case continuing contains form => exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (.continueStmt contains form)
    case breaking contains form => exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (.breakStmt contains form)
    case returnValue contains form child ih => exact StatementsPlain.terminal contains (by intro e; simp [form]) (.returnValue contains form ih)
    case returnFault contains form child ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.returnValue contains form ih)
    case tail contains form child ih => exact .tailExpression contains form ih
    case discard contains form child next a b => exact StatementsPlain.prepend contains (by intro e; simp [form]) (.expression contains form a) b
    case discardValue contains form child next a b => exact StatementsPlain.discard_value contains form a b
    case ifConditionFault contains form test ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.ifCondition contains form ih)
    case ifReturned contains form test branch a b =>
      exact StatementsPlain.terminal contains (by intro e; simp [form]) (StatementsPlain.if_execute contains form a b)
    case ifContinuing contains form test branch a b =>
      exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (StatementsPlain.if_execute contains form a b)
    case ifBreaking contains form test branch a b =>
      exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (StatementsPlain.if_execute contains form a b)
    case ifFault contains form test branch a b =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (StatementsPlain.if_fault contains form a b)
    case ifFallthrough contains form test branch next a b c =>
      exact StatementsPlain.prepend contains (by intro e; simp [form]) (StatementsPlain.if_execute contains form a b) c
    case expressionFault contains form child ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.expression contains form ih)
    case bitNotBare contains form snapshot write _next nextIH =>
      exact StatementsPlain.prepend contains (by intro expression; simp [form])
        (.assignBitNot contains form (.intro (snapshot.resolves _ _ _ _) write)) nextIH
    case bitNotBareFault contains form _bare failed =>
      exact StatementsPlain.head_fault (.assignBitNot contains form failed)
    case bitNotProjected contains form _projected keys snapshot write _next keysIH nextIH =>
      exact StatementsPlain.prepend contains (by intro expression; simp [form])
        (.assignBitNot contains form (.intro (snapshot.resolves keysIH) write)) nextIH
    case bitNotProjectedRootFault contains form _projected failed =>
      exact StatementsPlain.head_fault (.assignBitNot contains form (.target failed.source))
    case bitNotProjectedKeysFault contains form _projected ready keys keysIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.assignBitNot contains form (.target (ready.key_fault keysIH)))
    case bitNotProjectedGetterFault contains form _projected keys failed keysIH =>
      exact StatementsPlain.head_fault (.assignBitNot contains form (.target (failed.source keysIH)))
    case assignProjected contains form _projected keys snapshot child write _next keysIH childIH nextIH =>
      exact StatementsPlain.prepend contains (by intro expression; simp [form])
        (.assignValue contains form (.intro (snapshot.resolves keysIH) childIH write)) nextIH
    case assignProjectedRootFault contains form _projected failed =>
      exact StatementsPlain.head_fault (.assignValue contains form (.target failed.source))
    case assignProjectedKeysFault contains form _projected ready keys keysIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.assignValue contains form (.target (ready.key_fault keysIH)))
    case assignProjectedGetterFault contains form _projected keys failed keysIH =>
      exact StatementsPlain.head_fault (.assignValue contains form (.target (failed.source keysIH)))
    case assignProjectedRhsFault contains form _projected keys snapshot child keysIH childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.assignValue contains form (.rhs (snapshot.resolves keysIH) childIH))
    case assignProjectedWriteFault contains form _projected keys snapshot child failed keysIH childIH =>
      exact StatementsPlain.head_fault (.assignValue contains form (failed.source (snapshot.resolves keysIH) childIH))
    case assignBare contains form snapshot child write _next childIH nextIH =>
      exact StatementsPlain.prepend contains (by intro expression; simp [form])
        (.assignValue contains form (.intro (snapshot.resolves _ _ _ _) childIH write)) nextIH
    case assignBareFault contains form snapshot child childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.assignValue contains form
          (.rhs (snapshot.resolves _ _ _ _) childIH))
    case assignBareOperands contains form snapshot child currentRead rootType initialValue pathRead invalid childIH =>
      exact StatementsPlain.head_fault (.assignValue contains form
        (.operands (snapshot.resolves _ _ _ _) childIH currentRead rootType initialValue pathRead invalid))
    case assignBareUnbound contains form _bare missing =>
      exact StatementsPlain.head_fault (.assignValue contains form (.target (.unbound missing)))
    case assignBareDangling contains form _bare lookup missing =>
      exact StatementsPlain.head_fault (.assignValue contains form (.target (.dangling lookup missing)))
    case letUninitialized contains form mono extension allocate next ih =>
      exact StatementsPlain.prepend contains (by intro e; simp [form]) (.letUninitialized contains form mono extension allocate) ih
    case letInitialized contains form child mono extension allocate next a b =>
      exact StatementsPlain.prepend contains (by intro e; simp [form]) (.letInitialized contains form a mono extension allocate) b
    case letFault contains form mono child ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact StatementsPlain.head_fault (.letInitializer contains form mono ih)

    case blockReturned contains form inner ih =>
      exact StatementsPlain.terminal contains (by intro e; simp [form]) (.block contains form ih)
    case blockContinuing contains form inner ih =>
      exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (.block contains form ih)
    case blockBreaking contains form inner ih =>
      exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (.block contains form ih)
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
    case done test ih => exact .done ih
    case conditionFault test ih =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .condition ih
    case returned test body testIH bodyIH => exact .returns testIH bodyIH
    case breakFromBody test body testIH bodyIH => exact .breaks testIH bodyIH
    case bodyFault test body testIH bodyIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .body testIH bodyIH
    case next test body next testIH bodyIH nextIH => exact WhilePlain.next testIH bodyIH nextIH

    case continueNext test body next testIH bodyIH nextIH => exact WhilePlain.continued testIH bodyIH nextIH

    case matchReturned contains form matched ih =>
      exact StatementsPlain.terminal contains (by intro e; simp [form]) (ih _ _ contains form)
    case matchContinuing contains form matched ih =>
      exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (ih _ _ contains form)
    case matchBreaking contains form matched ih =>
      exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (ih _ _ contains form)
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
      | semantic => exact .matchScrutinee contains form ih
    case patternFault contains scrutinee allocated invalid ih =>
      intro id node found form
      exact .matchPattern found form contains ih allocated invalid
    case arm contains scrutinee hidden selected extended allocated body scrutineeIH bodyIH =>
      exact MatchPlain.arm contains scrutineeIH hidden selected extended allocated bodyIH
    case default contains scrutinee hidden selected body scrutineeIH bodyIH =>
      exact MatchPlain.default contains scrutineeIH hidden selected bodyIH
    case noBranch contains scrutinee hidden selected ih =>
      intro id node found form
      exact .matchNoBranch found form contains ih hidden selected

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
    case initialized mono extended child allocated next childIH nextIH =>
      exact ForItemsPlain.prepend (.letInitialized childIH mono extended allocated) nextIH
    case initializerFault mono child childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.letInitializer mono childIH)
    case expression child next childIH nextIH => exact ForItemsPlain.prepend (.expression childIH) nextIH
    case expressionFailure child childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.expression childIH)
    case bitNot snapshot write _next nextIH =>
      exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves _ _ _ _) write)) nextIH
    case bitNotFault _bare failed => exact .head (.assignBitNot failed)
    case projectedBitNot _projected keys snapshot write _next keysIH nextIH =>
      exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves keysIH) write)) nextIH
    case projectedBitNotRootFault _projected failed =>
      exact .head (.assignBitNot (.target failed.source))
    case projectedBitNotKeysFault _projected ready keys keysIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.assignBitNot (.target (ready.key_fault keysIH)))
    case projectedBitNotGetterFault _projected keys failed keysIH =>
      exact .head (.assignBitNot (.target (failed.source keysIH)))
    case projectedAssignment _projected keys snapshot child write _next keysIH childIH nextIH =>
      exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves keysIH) childIH write)) nextIH
    case projectedAssignmentRootFault _projected failed =>
      exact .head (.assignValue (.target failed.source))
    case projectedAssignmentKeysFault _projected ready keys keysIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.assignValue (.target (ready.key_fault keysIH)))
    case projectedAssignmentGetterFault _projected keys failed keysIH =>
      exact .head (.assignValue (.target (failed.source keysIH)))
    case projectedAssignmentRhsFault _projected keys snapshot child keysIH childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.assignValue (.rhs (snapshot.resolves keysIH) childIH))
    case projectedAssignmentWriteFault _projected keys snapshot child failed keysIH childIH =>
      exact .head (.assignValue (failed.source (snapshot.resolves keysIH) childIH))
    case assignment snapshot child write next childIH nextIH =>
      exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves _ _ _ _) childIH write)) nextIH
    case assignmentFailure snapshot child childIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .head (.assignValue (.rhs (snapshot.resolves _ _ _ _) childIH))
    case assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid childIH =>
      exact .head (.assignValue
        (.operands (snapshot.resolves _ _ _ _) childIH currentRead rootType initialValue pathRead invalid))
    case unbound _bare missing => exact .head (.assignValue (.target (.unbound missing)))
    case dangling _bare lookup missing => exact .head (.assignValue (.target (.dangling lookup missing)))
    case testFault test testIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .condition testIH
    case finished test testIH => exact .done testIH
    case bodyFailure test branch testIH branchIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .body testIH branchIH
    case returnedFromBody test branch testIH branchIH => exact .returns testIH branchIH
    case forBreakFromBody test branch testIH branchIH => exact .breaks testIH branchIH
    case postFailure test branch postTrace testIH branchIH postIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .postFallthrough testIH branchIH postIH
    case continuePostFailure test branch postTrace testIH branchIH postIH =>
      rename_i failure
      cases failure with
      | stage => trivial
      | semantic => exact .postContinue testIH branchIH postIH
    case iterate test branch postTrace next testIH branchIH postIH nextIH =>
      exact ForLoopPlain.next testIH branchIH postIH nextIH
    case continueIterate test branch postTrace next testIH branchIH postIH nextIH =>
      exact ForLoopPlain.continued testIH branchIH postIH nextIH
  ))

private theorem projection {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap} {id : ExpressionId} {outcome : Outcome}
    (trace : Expression program registry scope context environment before id outcome after) :
    ExpressionPlain program scope context environment before id outcome after := by
  induction trace using Expression.rec
    (motive_2 := fun scope context environment before ids outcome after _ => ExpressionsPlain program scope context environment before ids outcome after)
    (motive_3 := fun scope context before value arguments outcome after _ => AppliesPlain program scope context before value arguments outcome after)
    (motive_4 := fun mode scope context environment before ids finalContext outcome after _ => StatementsPlain program mode scope context environment before ids finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => WhilePlain program scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => MatchPlain program scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ForItemsPlain program scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ForLoopPlain program scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => RawFormPlain program scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => CoercionStepPlain program scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => CoercionPathPlain program scope context before steps input outcome after)
  erase_recursive_plain

private theorem rawform_projection {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    (trace : RawForm program registry scope context environment before form requirements coercions outcome after) :
    RawFormPlain program scope context environment before form requirements coercions outcome after := by
  induction trace using RawForm.rec
    (motive_1 := fun scope context environment before id outcome after _ => ExpressionPlain program scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ExpressionsPlain program scope context environment before ids outcome after)
    (motive_3 := fun scope context before value arguments outcome after _ => AppliesPlain program scope context before value arguments outcome after)
    (motive_4 := fun mode scope context environment before ids finalContext outcome after _ => StatementsPlain program mode scope context environment before ids finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => WhilePlain program scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => MatchPlain program scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ForItemsPlain program scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ForLoopPlain program scope context environment before condition post body outcome after)
    (motive_10 := fun scope context before step input outcome after _ => CoercionStepPlain program scope context before step input outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => CoercionPathPlain program scope context before steps input outcome after)
  erase_recursive_plain

theorem RawForm.value_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {value : Value}
    (trace : RawForm program registry scope context environment before form requirements coercions (.value value) after) :
    ExpressionFormEvaluates program context scope.evidence scope.source environment before form requirements coercions value after := rawform_projection trace

theorem RawForm.semanticFault_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {environment : Environment} {before after : Heap}
    {form : ExpressionForm} {requirements : List RequirementId} {coercions : List SourceInference.CoercionStep} {reason : SemanticFault}
    (trace : RawForm program registry scope context environment before form requirements coercions (.fault (.semantic reason)) after) :
    ExpressionFormFaults program context scope.evidence scope.source environment before form requirements coercions reason after := rawform_projection trace

private theorem coercionstep_projection {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionStep program registry scope context before step input outcome after) :
    CoercionStepPlain program scope context before step input outcome after := by
  induction trace using CoercionStep.rec
    (motive_1 := fun scope context environment before id outcome after _ => ExpressionPlain program scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ExpressionsPlain program scope context environment before ids outcome after)
    (motive_3 := fun scope context before value arguments outcome after _ => AppliesPlain program scope context before value arguments outcome after)
    (motive_4 := fun mode scope context environment before ids finalContext outcome after _ => StatementsPlain program mode scope context environment before ids finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => WhilePlain program scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => MatchPlain program scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ForItemsPlain program scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ForLoopPlain program scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => RawFormPlain program scope context environment before form requirements coercions outcome after)
    (motive_11 := fun scope context before steps input outcome after _ => CoercionPathPlain program scope context before steps input outcome after)
  erase_recursive_plain

theorem CoercionStep.value_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {value : Value}
    (trace : CoercionStep program registry scope context before step input (.value value) after) :
    CoercionStepExecutes program context scope.evidence before step input value after := coercionstep_projection trace

theorem CoercionStep.semanticFault_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {step : SourceInference.CoercionStep}
    {input : Value} {reason : SemanticFault}
    (trace : CoercionStep program registry scope context before step input (.fault (.semantic reason)) after) :
    CoercionStepFaults program context scope.evidence before step input reason after := coercionstep_projection trace

private theorem coercionpath_projection {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {outcome : Outcome}
    (trace : CoercionPath program registry scope context before steps input outcome after) :
    CoercionPathPlain program scope context before steps input outcome after := by
  induction trace using CoercionPath.rec
    (motive_1 := fun scope context environment before id outcome after _ => ExpressionPlain program scope context environment before id outcome after)
    (motive_2 := fun scope context environment before ids outcome after _ => ExpressionsPlain program scope context environment before ids outcome after)
    (motive_3 := fun scope context before value arguments outcome after _ => AppliesPlain program scope context before value arguments outcome after)
    (motive_4 := fun mode scope context environment before ids finalContext outcome after _ => StatementsPlain program mode scope context environment before ids finalContext outcome after)
    (motive_5 := fun scope context environment before condition statements outcome after _ => WhilePlain program scope context environment before condition statements outcome after)
    (motive_6 := fun scope context environment before resolution outcome after _ => MatchPlain program scope context environment before resolution outcome after)
    (motive_7 := fun scope context environment before items finalContext outcome after _ => ForItemsPlain program scope context environment before items finalContext outcome after)
    (motive_8 := fun scope context environment before condition post body outcome after _ => ForLoopPlain program scope context environment before condition post body outcome after)
    (motive_9 := fun scope context environment before form requirements coercions outcome after _ => RawFormPlain program scope context environment before form requirements coercions outcome after)
    (motive_10 := fun scope context before step input outcome after _ => CoercionStepPlain program scope context before step input outcome after)
  erase_recursive_plain

theorem CoercionPath.value_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {value : Value}
    (trace : CoercionPath program registry scope context before steps input (.value value) after) :
    CoercionPathExecutes program context scope.evidence before steps input value after := coercionpath_projection trace

theorem CoercionPath.semanticFault_plain {program : Program} {registry : Registry}
    {scope : Scope} {context : Context} {before after : Heap} {steps : List SourceInference.CoercionStep}
    {input : Value} {reason : SemanticFault}
    (trace : CoercionPath program registry scope context before steps input (.fault (.semantic reason)) after) :
    CoercionPathFaults program context scope.evidence before steps input reason after := coercionpath_projection trace

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

/-- A key row erases in its original order and at the same reached heap. -/
theorem Expressions.plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {outcome : ValuesOutcome}
    (trace : Expressions program registry scope context environment before ids outcome after) :
    ExpressionsPlain program scope context environment before ids outcome after := by
  induction trace using Expressions.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ _ _ _ => True)
  all_goals try exact True.intro
  case nil => exact .nil
  case cons head _tail _headIH tailIH => exact .cons head.value_plain tailIH
  case headFault head _headIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head head.semanticFault_plain
  case tailFault head _tail _headIH tailIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .tail head.value_plain tailIH

theorem Expressions.values_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {values : List Value}
    (trace : Expressions program registry scope context environment before ids (.values values) after) :
    ExpressionsEvaluate program context scope.evidence scope.source environment before ids values after := trace.plain

theorem Expressions.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Environment} {before after : Heap}
    {ids : List ExpressionId} {reason : SemanticFault}
    (trace : Expressions program registry scope context environment before ids (.fault (.semantic reason)) after) :
    ExpressionsFault program context scope.evidence scope.source environment before ids reason after := trace.plain

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
/-! Results of lifting an ordinary execution into recursive staged semantics.
Ordinary results retain their exact heap. A stage rejection retains the heap
reached by its genuine staged trace, before the rejected call's arguments. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.Lifting
open Frontend Frontend.SourceInference

def embed (outcome : Dynamic.ExpressionOutcome) : Outcome :=
  match outcome with
  | .value value => .value value
  | .fault reason => .fault (.semantic reason)

/-- A rejection can stop before the ordinary trace's endpoint. Its trace,
rather than an unrelated heap condition, records the actual reached prefix. -/
inductive Adapted (plain : Dynamic.ExpressionOutcome) (plainAfter : Dynamic.Heap) :
    Outcome → Dynamic.Heap → Prop where
  | completed : Adapted plain plainAfter (embed plain) plainAfter
  | rejected (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault)
      (reached : Dynamic.Heap) :
      Adapted plain plainAfter (.fault (.stage scope call reason)) reached

def ExpressionLift (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (id : ExpressionId) (plain : Dynamic.ExpressionOutcome) (plainAfter : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Expression program registry scope context environment before id staged reached ∧
    Adapted plain plainAfter staged reached

def ApplicationLift (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (before : Dynamic.Heap) (function : Dynamic.Value)
    (arguments : List Dynamic.Value) (plain : Dynamic.ExpressionOutcome)
    (plainAfter : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Applies program registry scope context before function arguments staged reached ∧
    Adapted plain plainAfter staged reached

theorem ExpressionLift.completed {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (trace : Expression program registry scope context environment before id (embed plain) after) :
    ExpressionLift program registry scope context environment before id plain after :=
  ⟨_, _, trace, .completed⟩

theorem ExpressionLift.rejected {program : Program} {registry : Registry} {scope origin : Scope}
    {context : Context} {environment : Dynamic.Environment} {before reached after : Dynamic.Heap}
    {id call : ExpressionId} {reason : CallGuard.Fault} {plain : Dynamic.ExpressionOutcome}
    (trace : Expression program registry scope context environment before id
      (.fault (.stage origin call reason)) reached) :
    ExpressionLift program registry scope context environment before id plain after :=
  ⟨_, _, trace, .rejected origin call reason reached⟩

/-- Successful and semantic-fault results match the ordinary trace exactly;
the only other result is an authenticated stage rejection. -/
theorem ExpressionLift.cases {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (lifted : ExpressionLift program registry scope context environment before id plain after) :
    Expression program registry scope context environment before id (embed plain) after ∨
      ∃ origin call reason reached,
        Expression program registry scope context environment before id
          (.fault (.stage origin call reason)) reached ∧ Generated origin call reason := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  cases adapted with
  | completed => exact .inl trace
  | rejected origin call reason reached =>
    exact .inr ⟨origin, call, reason, reached, trace, trace.stage_origin rfl⟩

theorem ExpressionLift.sized {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {plain : Dynamic.ExpressionOutcome}
    (lifted : ExpressionLift program registry scope context environment before id plain after) :
    ∃ size staged reached,
      Size.Expression program registry size scope context environment before id staged reached ∧
      Adapted plain after staged reached := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  obtain ⟨size, measured⟩ := Size.Expression.of_trace trace
  exact ⟨size, staged, reached, measured, adapted⟩

theorem ApplicationLift.cases {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Dynamic.Heap} {function : Dynamic.Value}
    {arguments : List Dynamic.Value} {plain : Dynamic.ExpressionOutcome}
    (lifted : ApplicationLift program registry scope context before function arguments plain after) :
    Applies program registry scope context before function arguments (embed plain) after ∨
      ∃ origin call reason reached,
        Applies program registry scope context before function arguments
          (.fault (.stage origin call reason)) reached ∧ Generated origin call reason := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  cases adapted with
  | completed => exact .inl trace
  | rejected origin call reason reached =>
    exact .inr ⟨origin, call, reason, reached, trace, trace.stage_origin rfl⟩

theorem ApplicationLift.sized {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Dynamic.Heap} {function : Dynamic.Value}
    {arguments : List Dynamic.Value} {plain : Dynamic.ExpressionOutcome}
    (lifted : ApplicationLift program registry scope context before function arguments plain after) :
    ∃ size staged reached,
      Size.Applies program registry size scope context before function arguments staged reached ∧
      Adapted plain after staged reached := by
  obtain ⟨staged, reached, trace, adapted⟩ := lifted
  obtain ⟨size, measured⟩ := Size.Applies.of_trace trace
  exact ⟨size, staged, reached, measured, adapted⟩

end Solcore.SourceSemantics.Staging.Recursive.Lifting
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveAtomicLifting
/-! Atomic ordinary traces enter staged semantics without changing their
result or heap. Readable local cells retain their actual descriptor; a
generalized closure read cannot be substituted for an ordinary cell read. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.Lifting
open Frontend Frontend.SourceInference

def OrdinaryReadAt (node : ExpressionNode) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) : Prop :=
  ∀ name binder location cell,
    node.form = .reference name (.local binder) →
    Dynamic.Environment.LooksUp environment binder location →
    Dynamic.Heap.Reads heap location cell → cell.generalized = none

theorem OrdinaryReadAt.of_read {node : ExpressionNode} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (form : node.form = .reference name (.local binder))
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none) :
    OrdinaryReadAt node environment heap := by
  intro otherName otherBinder otherLocation otherCell otherForm otherLookup otherRead
  rw [form] at otherForm
  cases otherForm
  cases otherLookup.functional lookup
  cases otherRead.functional read
  exact ordinary

theorem atomic {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : AtomicForm node.form) (uncoerced : node.coercions = [])
    (ordinary : OrdinaryReadAt node environment before)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after := by
  have align : ∀ {other}, ContainsExpression scope.source id other → other = node := by
    intro other found
    exact Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique contains))
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro found raw coercions =>
      cases align found
      rw [uncoerced] at coercions
      cases coercions
      rw [uncoerced] at raw
      exact .atomicValue contains form uncoerced raw
    | generalizedLocal found reference _ lookup read descriptor _ _ _ =>
      cases align found
      rw [ordinary _ _ _ _ reference lookup read] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form found raw =>
      cases align found
      rw [uncoerced] at raw
      exact .atomicFault contains form uncoerced raw
    | coercion found _ failed =>
      cases align found
      rw [uncoerced] at failed
      cases failed
    | generalizedLocalRequirement found reference _ lookup read descriptor _ _ _
    | generalizedLocalCoercion found reference _ lookup read descriptor _ _ _ =>
      cases align found
      rw [ordinary _ _ _ _ reference lookup read] at descriptor
      cases descriptor

theorem atomic_nonlocal {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : AtomicForm node.form) (uncoerced : node.coercions = [])
    (nonlocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after :=
  atomic unique contains form uncoerced
    (fun name binder _ _ reference _ _ => False.elim (nonlocal name binder reference)) trace

theorem atomic_read {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {outcome : Dynamic.ExpressionOutcome}
    {name : String} {binder : Resolved.LocalId} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (unique : NodeOccurrencesUnique scope.source)
    (contains : ContainsExpression scope.source id node)
    (form : node.form = .reference name (.local binder)) (uncoerced : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location cell) (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context scope.evidence scope.source
      environment before id outcome after) :
    Expression program registry scope context environment before id (embed outcome) after :=
  atomic unique contains (form.symm ▸ .reference name (.local binder)) uncoerced
    (OrdinaryReadAt.of_read form lookup read ordinary) trace

end Solcore.SourceSemantics.Staging.Recursive.Lifting
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveBareBitNotFacts
/-! The actual ordinary unary update is exactly a bare snapshot followed by
its real write. Its failure form retains the same incoming heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

variable {program : Program} {context : Context} {evidence : EvidenceEnvironment}
  {source : TypedSource} {environment : Environment} {before after : Heap}
  {place : PlaceResolution}

theorem bitNot_update_iff {updated : Value} (bare : place.projections = []) :
    SourcePlaceSnapshotUpdate program context evidence source BitNotSnapshot
      environment before place updated after ↔
    ∃ target, BareTarget environment before place target ∧
      ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
        before target updated after := by
  constructor
  · intro executed
    cases executed with
    | intro resolved written =>
      obtain ⟨rfl, snapshot⟩ := BareTarget.of_resolves bare resolved
      exact ⟨_, snapshot, written⟩
  · rintro ⟨target, snapshot, written⟩
    exact .intro (snapshot.resolves _ _ _ _) written

theorem bitNot_fault_iff {reason : SemanticFault} (bare : place.projections = []) :
    SourcePlaceBitNotFaults program context evidence source environment before place reason after ↔
    after = before ∧
      SourcePlaceBitNotFaults program context evidence source environment before place reason before := by
  constructor
  · intro failed
    have same := bitNot_fault_heap bare failed
    exact ⟨same, same ▸ failed⟩
  · rintro ⟨rfl, failed⟩
    exact failed

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveBodyErasure
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
  case continuing contains form =>
    exact StatementsPlain.terminal_continuing contains (by intro expression; simp [form]) (.continueStmt contains form)
  case breaking contains form =>
    exact StatementsPlain.terminal_breaking contains (by intro expression; simp [form]) (.breakStmt contains form)
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
  case ifContinuing contains form test _branch _testIH branchIH =>
    exact StatementsPlain.terminal_continuing contains (by intro e; simp [form])
      (StatementsPlain.if_execute contains form test.value_plain branchIH)
  case ifBreaking contains form test _branch _testIH branchIH =>
    exact StatementsPlain.terminal_breaking contains (by intro e; simp [form])
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
  case bitNotBare contains form snapshot write _next nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.assignBitNot contains form (.intro (snapshot.resolves _ _ _ _) write)) nextIH
  case bitNotBareFault contains form _bare failed =>
    exact StatementsPlain.head_fault (.assignBitNot contains form failed)
  case bitNotProjected contains form _projected keys snapshot write _next _keysIH nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.assignBitNot contains form (.intro (snapshot.resolves keys.values_plain) write)) nextIH
  case bitNotProjectedRootFault contains form _projected failed =>
    exact StatementsPlain.head_fault (.assignBitNot contains form (.target failed.source))
  case bitNotProjectedKeysFault contains form _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.assignBitNot contains form (.target (ready.key_fault keys.semanticFault_plain)))
  case bitNotProjectedGetterFault contains form _projected keys failed _keysIH =>
    exact StatementsPlain.head_fault (.assignBitNot contains form (.target (failed.source keys.values_plain)))
  case assignProjected contains form _projected keys snapshot child write _next _keysIH _childIH nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.assignValue contains form (.intro (snapshot.resolves keys.values_plain) child.value_plain write)) nextIH
  case assignProjectedRootFault contains form _projected failed =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target failed.source))
  case assignProjectedKeysFault contains form _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.assignValue contains form (.target (ready.key_fault keys.semanticFault_plain)))
  case assignProjectedGetterFault contains form _projected keys failed _keysIH =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target (failed.source keys.values_plain)))
  case assignProjectedRhsFault contains form _projected keys snapshot child _keysIH _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.assignValue contains form (.rhs (snapshot.resolves keys.values_plain) child.semanticFault_plain))
  case assignProjectedWriteFault contains form _projected keys snapshot child failed _keysIH _childIH =>
    exact StatementsPlain.head_fault (.assignValue contains form (failed.source (snapshot.resolves keys.values_plain) child.value_plain))
  case assignBare contains form snapshot child write _next _childIH nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.assignValue contains form (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignBareFault contains form snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact StatementsPlain.head_fault (.assignValue contains form
        (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case assignBareOperands contains form snapshot child currentRead rootType initialValue pathRead invalid _childIH =>
    exact StatementsPlain.head_fault (.assignValue contains form
      (.operands (snapshot.resolves _ _ _ _) child.value_plain currentRead rootType initialValue pathRead invalid))
  case assignBareUnbound contains form _bare missing =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target (.unbound missing)))
  case assignBareDangling contains form _bare lookup missing =>
    exact StatementsPlain.head_fault (.assignValue contains form (.target (.dangling lookup missing)))
  case letUninitialized contains form mono extension allocate _next ih =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.letUninitialized contains form mono extension allocate) ih
  case letGeneralized contains form snapshot captures polymorphic extension allocated _next nextIH =>
    exact StatementsPlain.prepend contains (by intro expression; simp [form])
      (.letInitializedGeneralized contains form snapshot captures polymorphic extension allocated) nextIH
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
  case blockContinuing contains form inner ih =>
    exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (.block contains form ih)
  case blockBreaking contains form inner ih =>
    exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (.block contains form ih)
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
  case breakFromBody test body _testIH bodyIH => exact .breaks test.value_plain bodyIH
  case bodyFault test body _testIH bodyIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain bodyIH
  case next test body next _testIH bodyIH nextIH => exact WhilePlain.next test.value_plain bodyIH nextIH

  case continueNext test body next _testIH bodyIH nextIH => exact WhilePlain.continued test.value_plain bodyIH nextIH

  case matchReturned contains form matched ih =>
    exact StatementsPlain.terminal contains (by intro e; simp [form]) (ih _ _ contains form)
  case matchContinuing contains form matched ih =>
    exact StatementsPlain.terminal_continuing contains (by intro e; simp [form]) (ih _ _ contains form)
  case matchBreaking contains form matched ih =>
    exact StatementsPlain.terminal_breaking contains (by intro e; simp [form]) (ih _ _ contains form)
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
  case initializedGeneralized snapshot captures polymorphic extension allocated _next nextIH =>
    exact ForItemsPlain.prepend (.letInitializedGeneralized snapshot captures polymorphic extension allocated) nextIH
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
  case bitNot snapshot write _next nextIH =>
    exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves _ _ _ _) write)) nextIH
  case bitNotFault _bare failed => exact .head (.assignBitNot failed)
  case projectedBitNot _projected keys snapshot write _next _keysIH nextIH =>
    exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves keys.values_plain) write)) nextIH
  case projectedBitNotRootFault _projected failed =>
    exact .head (.assignBitNot (.target failed.source))
  case projectedBitNotKeysFault _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignBitNot (.target (ready.key_fault keys.semanticFault_plain)))
  case projectedBitNotGetterFault _projected keys failed _keysIH =>
    exact .head (.assignBitNot (.target (failed.source keys.values_plain)))
  case projectedAssignment _projected keys snapshot child write _next _keysIH _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves keys.values_plain) child.value_plain write)) nextIH
  case projectedAssignmentRootFault _projected failed =>
    exact .head (.assignValue (.target failed.source))
  case projectedAssignmentKeysFault _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.target (ready.key_fault keys.semanticFault_plain)))
  case projectedAssignmentGetterFault _projected keys failed _keysIH =>
    exact .head (.assignValue (.target (failed.source keys.values_plain)))
  case projectedAssignmentRhsFault _projected keys snapshot child _keysIH _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves keys.values_plain) child.semanticFault_plain))
  case projectedAssignmentWriteFault _projected keys snapshot child failed _keysIH _childIH =>
    exact .head (.assignValue (failed.source (snapshot.resolves keys.values_plain) child.value_plain))
  case assignment snapshot child write next _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignmentFailure snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid _childIH =>
    exact .head (.assignValue
      (.operands (snapshot.resolves _ _ _ _) child.value_plain currentRead rootType initialValue pathRead invalid))
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
  case forBreakFromBody test branch _testIH branchIH => exact .breaks test.value_plain branchIH
  case postFailure test branch postTrace _testIH branchIH postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postFallthrough test.value_plain branchIH postIH
  case continuePostFailure test branch postTrace _testIH branchIH postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postContinue test.value_plain branchIH postIH
  case iterate test branch postTrace next _testIH branchIH postIH nextIH =>
    exact ForLoopPlain.next test.value_plain branchIH postIH nextIH

  case continueIterate test branch postTrace next _testIH branchIH postIH nextIH =>
    exact ForLoopPlain.continued test.value_plain branchIH postIH nextIH

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
  case breakFromBody test body _testIH _bodyIH => exact .breaks test.value_plain body.body_plain
  case bodyFault test body _testIH _bodyIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .body test.value_plain body.body_plain
  case next test body next _testIH _bodyIH nextIH => exact WhilePlain.next test.value_plain body.body_plain nextIH

  case continueNext test body next _testIH _bodyIH nextIH => exact WhilePlain.continued test.value_plain body.body_plain nextIH

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
  case initializedGeneralized snapshot captures polymorphic extension allocated _next nextIH =>
    exact ForItemsPlain.prepend (.letInitializedGeneralized snapshot captures polymorphic extension allocated) nextIH
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
  case bitNot snapshot write _next nextIH =>
    exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves _ _ _ _) write)) nextIH
  case bitNotFault _bare failed => exact .head (.assignBitNot failed)
  case projectedBitNot _projected keys snapshot write _next _keysIH nextIH =>
    exact ForItemsPlain.prepend (.assignBitNot (.intro (snapshot.resolves keys.values_plain) write)) nextIH
  case projectedBitNotRootFault _projected failed =>
    exact .head (.assignBitNot (.target failed.source))
  case projectedBitNotKeysFault _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignBitNot (.target (ready.key_fault keys.semanticFault_plain)))
  case projectedBitNotGetterFault _projected keys failed _keysIH =>
    exact .head (.assignBitNot (.target (failed.source keys.values_plain)))
  case projectedAssignment _projected keys snapshot child write _next _keysIH _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves keys.values_plain) child.value_plain write)) nextIH
  case projectedAssignmentRootFault _projected failed =>
    exact .head (.assignValue (.target failed.source))
  case projectedAssignmentKeysFault _projected ready keys _keysIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.target (ready.key_fault keys.semanticFault_plain)))
  case projectedAssignmentGetterFault _projected keys failed _keysIH =>
    exact .head (.assignValue (.target (failed.source keys.values_plain)))
  case projectedAssignmentRhsFault _projected keys snapshot child _keysIH _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves keys.values_plain) child.semanticFault_plain))
  case projectedAssignmentWriteFault _projected keys snapshot child failed _keysIH _childIH =>
    exact .head (.assignValue (failed.source (snapshot.resolves keys.values_plain) child.value_plain))
  case assignment snapshot child write next _childIH nextIH =>
    exact ForItemsPlain.prepend (.assignValue (.intro (snapshot.resolves _ _ _ _) child.value_plain write)) nextIH
  case assignmentFailure snapshot child _childIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .head (.assignValue (.rhs (snapshot.resolves _ _ _ _) child.semanticFault_plain))
  case assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid _childIH =>
    exact .head (.assignValue
      (.operands (snapshot.resolves _ _ _ _) child.value_plain currentRead rootType initialValue pathRead invalid))
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
  case forBreakFromBody test branch _testIH _branchIH => exact .breaks test.value_plain branch.body_plain
  case postFailure test branch postTrace _testIH _branchIH _postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postFallthrough test.value_plain branch.body_plain postTrace.plain
  case continuePostFailure test branch postTrace _testIH _branchIH _postIH =>
    rename_i failure
    cases failure with
    | stage => trivial
    | semantic => exact .postContinue test.value_plain branch.body_plain postTrace.plain
  case iterate test branch postTrace next _testIH _branchIH _postIH nextIH =>
    exact ForLoopPlain.next test.value_plain branch.body_plain postTrace.plain nextIH

  case continueIterate test branch postTrace next _testIH _branchIH _postIH nextIH =>
    exact ForLoopPlain.continued test.value_plain branch.body_plain postTrace.plain nextIH

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

theorem StatementsIn.breaking_scoped {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : StatementsIn program registry false scope context environment before ids finalContext
      (.breaking finalEnvironment) after) :
    StatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.breaking finalEnvironment) after := trace.body_plain

theorem StatementsIn.continuing_scoped {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : StatementsIn program registry false scope context environment before ids finalContext
      (.continuing finalEnvironment) after) :
    StatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.continuing finalEnvironment) after := trace.body_plain

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

theorem Statements.breaking_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : Statements program registry scope context environment before ids finalContext
      (.breaking finalEnvironment) after) :
    FunctionStatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.breaking finalEnvironment) after := trace.body_plain

theorem Statements.continuing_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment finalEnvironment : Environment} {before after : Heap}
    {ids : List StatementId}
    (trace : Statements program registry scope context environment before ids finalContext
      (.continuing finalEnvironment) after) :
    FunctionStatementsExecute program context scope.evidence scope.source environment before ids
      finalContext (.continuing finalEnvironment) after := trace.body_plain


/-- A semantic fault keeps its actual reason, stopping context and prefix heap. -/
theorem Statements.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context finalContext : Context} {environment : Environment} {before after : Heap}
    {ids : List StatementId} {reason : SemanticFault}
    (trace : Statements program registry scope context environment before ids finalContext
      (.fault (.semantic reason)) after) :
    FunctionStatementsFault program context scope.evidence scope.source environment before ids
      finalContext reason after := trace.body_plain

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveCallableErasure
/-! Ordinary callable outcomes retain their exact independent Dynamic
application, including argument allocation, nested bodies and final heap.
The invocation dictionary is the one stored by the actual callable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Builtins carry no dictionary; named and anonymous functions retain theirs. -/
def callableEvidence : Value → EvidenceEnvironment
  | .closure function => function.evidence
  | .global function => function.evidence
  | _ => []

theorem Applies.value_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {callable : Value} {arguments : List Value} {value : Value}
    (trace : Applies program registry scope context before callable arguments (.value value) after) :
    CallableApplies program context scope.evidence (callableEvidence callable)
      before callable arguments value after := by
  cases trace with
  | builtin primitive => exact .builtin primitive
  | @global _ _ _ _ _ function _ _ _ _ _ bodyInstance _ child _ _
      instantiates covers roots selected parameters allocate body resultRule =>
    have source : child.source = bodyInstance.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : bodyInstance.resultType = type at resultRule
    cases resultRule with
    | returned =>
      exact .global instantiates rfl covers
        (.returned covers roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.returned_plain body) rfl)
    | unit =>
      exact .global instantiates rfl covers
        (.unit covers typeEq roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.fallthrough_plain body) ⟨_, rfl⟩)
  | @closure _ _ _ _ _ _ function _ _ _ _ _ _ child _ _
      selected valid parameters copy allocate body resultRule =>
    have source : child.source = function.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : function.resultType = type at resultRule
    cases resultRule with
    | returned =>
      exact .closure rfl valid parameters copy allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.returned_plain body) rfl
    | unit =>
      exact .closureUnit rfl valid typeEq parameters copy allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.fallthrough_plain body) ⟨_, rfl⟩

theorem Applies.semanticFault_plain {program : Program} {registry : Registry} {scope : Scope}
    {context : Context} {before after : Heap} {callable : Value} {arguments : List Value} {reason : SemanticFault}
    (trace : Applies program registry scope context before callable arguments (.fault (.semantic reason)) after) :
    CallableFaults program context scope.evidence (callableEvidence callable)
      before callable arguments reason after := by
  cases trace with
  | builtinArity mismatch => exact .builtinArity mismatch
  | builtinType arity mismatch => exact .builtinArgumentType arity mismatch
  | closureArity mismatch => exact .closureArity mismatch
  | globalArity instantiates mismatch => exact .globalArity instantiates mismatch
  | @global _ _ _ _ _ function _ _ _ _ _ bodyInstance _ child _ _
      instantiates _covers roots selected parameters allocate body resultRule =>
    have source : child.source = bodyInstance.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : bodyInstance.resultType = type at resultRule
    cases resultRule with
    | breaking =>
      exact .globalBody instantiates rfl (.controlEscape roots parameters allocate (by simpa only [source, evidence, callableEvidence] using Statements.breaking_plain body) (Or.inl ⟨_, rfl⟩))
    | continuing =>
      exact .globalBody instantiates rfl (.controlEscape roots parameters allocate (by simpa only [source, evidence, callableEvidence] using Statements.continuing_plain body) (Or.inr ⟨_, rfl⟩))
    | fault =>
      exact .globalBody instantiates rfl
        (.statements roots parameters allocate
          (by simpa only [source, evidence, callableEvidence] using Statements.semanticFault_plain body))
  | @closure _ _ _ _ _ _ function _ _ _ _ _ _ child _ _
      selected valid parameters copy allocate body resultRule =>
    have source : child.source = function.source := registry.source selected
    have evidence : child.evidence = function.evidence := registry.evidence selected
    generalize typeEq : function.resultType = type at resultRule
    cases resultRule with
    | breaking =>
      exact .closureControlEscape rfl valid parameters copy allocate (by simpa only [source, evidence, callableEvidence] using Statements.breaking_plain body) (Or.inl ⟨_, rfl⟩)
    | continuing =>
      exact .closureControlEscape rfl valid parameters copy allocate (by simpa only [source, evidence, callableEvidence] using Statements.continuing_plain body) (Or.inr ⟨_, rfl⟩)
    | fault =>
      exact .closureBody rfl valid parameters copy allocate
        (by simpa only [source, evidence, callableEvidence] using Statements.semanticFault_plain body)

end Solcore.SourceSemantics.Staging.Recursive
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

theorem RootFault.excluded {context : Context} {environment : Environment} {heap : Heap}
    {place : PlaceResolution} {root : TypeSystem.Ty} {reason : SemanticFault}
    (failed : RootFault environment heap place reason)
    (writable : WritableLocal context place.root root)
    (locals : EnvironmentAgrees heap context.locals environment) : False := by
  obtain ⟨scheme, declared, _wellFormed, _mono, _body⟩ := writable.scheme
  obtain ⟨location, cell, lookup, read, _type, _storage⟩ := locals.lookup declared
  cases failed with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling present missing =>
      cases present.functional lookup
      exact missing.excludes_read read

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
end
