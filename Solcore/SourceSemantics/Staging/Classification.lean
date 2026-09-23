import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Staging.Assignment
import Solcore.SourceSemantics.Staging.Stage
import Solcore.Resolved.LocalScope
import Solcore.Frontend.SourceInference.Types

/-!
Independent, scope-aware staging classification for resolved typed source.

The rules mirror the lexical behavior of the executable source-stage pass but
are stated solely over the forgeable typed-source carrier.  Recursive edges
use declarative table membership, mutable locals are classified by
`AssignedIn`, and no rule invokes the executable analysis.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging

open Frontend
open Frontend.SourceInference

/-- First-match stage environment for stable lexical identities. -/
abbrev StageScope := Resolved.LocalScope Stage

namespace StageScope

/-- Declarative lookup of a binder's current lexical stage. -/
abbrev Lookup (scope : StageScope) (binder : Resolved.LocalId)
    (stage : Stage) : Prop :=
  Resolved.LocalScope.Lookup scope binder stage

end StageScope

/-- Enter one binder at the requested stage.  Any assignment to its place root
anywhere in the declaration conservatively changes the retained stage to
`deferred`. -/
inductive BinderGetsStage (source : TypedSource) (scope : StageScope)
    (binder : Resolved.LocalId) (requested : Stage) :
    Stage → StageScope → Prop where
  | assigned
      (owned : binder.owner = source.owner)
      (assigned : AssignedIn source binder) :
      BinderGetsStage source scope binder requested .deferred
        ((binder, .deferred) :: scope)
  | stable
      (owned : binder.owner = source.owner)
      (notAssigned : ¬ AssignedIn source binder) :
      BinderGetsStage source scope binder requested requested
        ((binder, requested) :: scope)

/-- Stage requested by an ordinary parameter before mutation is considered. -/
inductive BinderDefaultStage : TypedBinder → Stage → Prop where
  | marked
      {binder : TypedBinder}
      (marked : binder.comptime = true) :
      BinderDefaultStage binder .comptime
  | comptimeType
      {binder : TypedBinder}
      (unmarked : binder.comptime = false)
      (comptimeOnly : ComptimeOnlyType binder.scheme.body) :
      BinderDefaultStage binder .comptime
  | runtime
      {binder : TypedBinder}
      (unmarked : binder.comptime = false)
      (notComptimeOnly : ¬ ComptimeOnlyType binder.scheme.body) :
      BinderDefaultStage binder .runtime

/-- Extend a scope with every retained binder at one requested stage. -/
inductive BindersGetStage (source : TypedSource) (requested : Stage) :
    StageScope → List TypedBinder → StageScope → Prop where
  | nil (scope : StageScope) :
      BindersGetStage source requested scope [] scope
  | cons
      {scope middle final : StageScope}
      {binder : TypedBinder} {binders : List TypedBinder}
      {actual : Stage}
      (head : BinderGetsStage source scope binder.id requested actual middle)
      (tail : BindersGetStage source requested middle binders final) :
      BindersGetStage source requested scope (binder :: binders) final

/-- Extend a scope with every retained binder at its ordinary requested stage. -/
inductive BindersGetDefaultStages (source : TypedSource) :
    StageScope → List TypedBinder → StageScope → Prop where
  | nil (scope : StageScope) :
      BindersGetDefaultStages source scope [] scope
  | cons
      {scope middle final : StageScope}
      {binder : TypedBinder} {binders : List TypedBinder}
      {requested actual : Stage}
      (requestedStage : BinderDefaultStage binder requested)
      (head : BinderGetsStage source scope binder.id requested actual middle)
      (tail : BindersGetDefaultStages source middle binders final) :
      BindersGetDefaultStages source scope (binder :: binders) final

/-- Index expressions appearing in a place, in projection order. -/
def placeIndexExpressions (place : PlaceResolution) : List ExpressionId :=
  place.projections.filterMap fun projection =>
    match projection with
    | .index key => some key
    | .member _ _ => none

/-- Every binder retained by one flat prefix-pattern instruction. -/
def instructionBinders : MatchPatternInstruction → List TypedBinder
  | .binder binder => [binder]
  | .wildcard
  | .integerLiteral _ _
  | .constructor _ _
  | .tuple _ => []

/-- Every binder retained by a pattern resolution, including nested prefix
instructions, in source order. -/
def patternBinders : MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions
  | .tuple instructions => instructions.flatMap instructionBinders
  | .wildcard
  | .integerLiteral _ _ => []

/-- All argument occurrences of a direct call are compile-time values. -/
def AllComptime (stages : List Stage) : Prop :=
  ∀ stage, stage ∈ stages → stage = .comptime

/-- A direct declaration call can be executed during staging either because
the declaration is marked or because an uncoerced result is stage-only. -/
def DirectResultComptime (node : ExpressionNode)
    (instantiation : DeclarationInstantiation) : Prop :=
  instantiation.returnComptime = true ∨
    (node.coercions = [] ∧ ComptimeOnlyType node.type)

/-- Exact result classification for a direct declaration call. -/
inductive DirectCallGetsStage (node : ExpressionNode)
    (instantiation : DeclarationInstantiation) (argumentStages : List Stage) :
    Stage → Prop where
  | comptime
      (resultComptime : DirectResultComptime node instantiation)
      (argumentsComptime : AllComptime argumentStages) :
      DirectCallGetsStage node instantiation argumentStages .comptime
  | deferred
      (notExecutable : ¬
        (DirectResultComptime node instantiation ∧ AllComptime argumentStages)) :
      DirectCallGetsStage node instantiation argumentStages .deferred

mutual

  /-- Declarative stage of one expression occurrence. -/
  inductive HasStage (source : TypedSource) :
      StageScope → ExpressionId → Stage → Prop where
    | literal
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {literal : Syntax.CoreLiteralValue}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .literal literal) :
        HasStage source scope id .comptime
    | integerLiteral
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {literal : Syntax.CoreLiteralValue}
        {resolution : IntegerLiteralResolution}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .integerLiteral literal resolution) :
        HasStage source scope id .comptime
    | builtinBoolean
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {name : String} {value : Bool}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .reference name (.builtinBoolean value)) :
        HasStage source scope id .comptime
    | local
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {name : String} {binder : Resolved.LocalId} {stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .reference name (.local binder))
        (owned : binder.owner = source.owner)
        (lookup : scope.Lookup binder stage) :
        HasStage source scope id stage
    | declaration
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {name : String} {instantiation : DeclarationInstantiation}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .reference name (.declaration instantiation)) :
        HasStage source scope id .deferred
    | builtinFunction
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {name : String} {function : BuiltinFunctionId}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .reference name (.builtinFunction function)) :
        HasStage source scope id .deferred
    | group
        {scope : StageScope} {id inner : ExpressionId}
        {node : ExpressionNode} {stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .group inner)
        (innerStage : HasStage source scope inner stage) :
        HasStage source scope id stage
    | tuple
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {elements : List ExpressionId} {stages : List Stage} {stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .tuple elements)
        (elementStages : ExpressionsHaveStages source scope elements stages)
        (joined : StagesJoin stages stage) :
        HasStage source scope id stage
    | unary
        {scope : StageScope} {id operand : ExpressionId}
        {node : ExpressionNode} {operator : Syntax.UnaryOp} {stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .unary operator operand)
        (operandStage : HasStage source scope operand stage) :
        HasStage source scope id stage
    | binary
        {scope : StageScope} {id left right : ExpressionId}
        {node : ExpressionNode} {operator : Syntax.BinaryOp}
        {leftStage rightStage stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .binary left operator right)
        (leftStages : HasStage source scope left leftStage)
        (rightStages : HasStage source scope right rightStage)
        (joined : StagesJoin [leftStage, rightStage] stage) :
        HasStage source scope id stage
    | conditional
        {scope : StageScope} {id condition thenBranch elseBranch : ExpressionId}
        {node : ExpressionNode}
        {conditionStage thenStage elseStage stage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .conditional condition thenBranch elseBranch)
        (conditionStages : HasStage source scope condition conditionStage)
        (thenStages : HasStage source scope thenBranch thenStage)
        (elseStages : HasStage source scope elseBranch elseStage)
        (joined : StagesJoin [conditionStage, thenStage, elseStage] stage) :
        HasStage source scope id stage
    | lambda
        {scope lambdaScope finalScope : StageScope}
        {id : ExpressionId} {node : ExpressionNode}
        {parameters : List TypedBinder} {returnType : TypeSystem.Ty}
        {body : List StatementId}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .lambda parameters returnType body)
        (parametersStage :
          BindersGetDefaultStages source scope parameters lambdaScope)
        (bodyStage : StatementsStage source lambdaScope body finalScope) :
        HasStage source scope id .deferred
    | directCall
        {scope : StageScope} {id callee : ExpressionId}
        {node : ExpressionNode} {arguments : List ExpressionId}
        {instantiation : DeclarationInstantiation}
        {calleeStage stage : Stage} {argumentStages : List Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form =
          .call callee arguments (.declaration instantiation))
        (calleeStages : HasStage source scope callee calleeStage)
        (argumentsStage :
          ExpressionsHaveStages source scope arguments argumentStages)
        (callStage : DirectCallGetsStage node instantiation argumentStages stage) :
        HasStage source scope id stage
    | indirectCall
        {scope : StageScope} {id callee : ExpressionId}
        {node : ExpressionNode} {arguments : List ExpressionId}
        {metadata : IndirectCallResolution}
        {calleeStage : Stage} {argumentStages : List Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .call callee arguments (.indirect metadata))
        (calleeStages : HasStage source scope callee calleeStage)
        (argumentsStage :
          ExpressionsHaveStages source scope arguments argumentStages) :
        HasStage source scope id .deferred
    | builtinCall
        {scope : StageScope} {id callee : ExpressionId}
        {node : ExpressionNode} {arguments : List ExpressionId}
        {function : BuiltinFunctionId}
        {calleeStage : Stage} {argumentStages : List Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form =
          .call callee arguments (.builtinFunction function))
        (calleeStages : HasStage source scope callee calleeStage)
        (argumentsStage :
          ExpressionsHaveStages source scope arguments argumentStages) :
        HasStage source scope id .deferred
    | constructor
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {instantiation : DataConstructorInstantiation}
        {arguments : List ExpressionId} {argumentStages : List Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .constructor instantiation arguments)
        (argumentsStage :
          ExpressionsHaveStages source scope arguments argumentStages) :
        HasStage source scope id .deferred
    | member
        {scope : StageScope} {id base : ExpressionId} {node : ExpressionNode}
        {name : String} {index : Nat} {baseStage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .member base name index)
        (baseStages : HasStage source scope base baseStage) :
        HasStage source scope id .deferred
    | proxy
        {scope : StageScope} {id : ExpressionId} {node : ExpressionNode}
        {inner : TypeSystem.Ty}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .proxy inner) :
        HasStage source scope id .deferred
    | index
        {scope : StageScope} {id base key : ExpressionId}
        {node : ExpressionNode} {baseStage keyStage : Stage}
        (contains : SourceSemantics.ContainsExpression source id node)
        (form_eq : node.form = .index base key)
        (baseStages : HasStage source scope base baseStage)
        (keyStages : HasStage source scope key keyStage) :
        HasStage source scope id .deferred

  /-- Pointwise expression classification in source order. -/
  inductive ExpressionsHaveStages (source : TypedSource) :
      StageScope → List ExpressionId → List Stage → Prop where
    | nil (scope : StageScope) : ExpressionsHaveStages source scope [] []
    | cons
        {scope : StageScope} {expression : ExpressionId}
        {expressions : List ExpressionId} {stage : Stage}
        {stages : List Stage}
        (head : HasStage source scope expression stage)
        (tail : ExpressionsHaveStages source scope expressions stages) :
        ExpressionsHaveStages source scope (expression :: expressions)
          (stage :: stages)

  /-- Stage every child occurrence of one statement and expose its lexical
  scope effect. -/
  inductive StatementStages (source : TypedSource) :
      StageScope → StatementId → StageScope → Prop where
    | letUninitialized
        {scope final : StageScope} {id : StatementId} {node : StatementNode}
        {binder : TypedBinder} {actual : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder none)
        (binderStage : BinderGetsStage source scope binder.id .deferred
          actual final) :
        StatementStages source scope id final
    | letInitialized
        {scope final : StageScope} {id : StatementId} {node : StatementNode}
        {binder : TypedBinder} {initializer : ExpressionId}
        {initializerStage actual : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (initializerStages : HasStage source scope initializer initializerStage)
        (binderStage : BinderGetsStage source scope binder.id initializerStage
          actual final) :
        StatementStages source scope id final
    | returnUnit
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .returnStmt none) :
        StatementStages source scope id scope
    | returnValue
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        {value : ExpressionId} {stage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some value))
        (valueStages : HasStage source scope value stage) :
        StatementStages source scope id scope
    | expression
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        {expression : ExpressionId} {semicolon : Bool} {stage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .expression expression semicolon)
        (expressionStages : HasStage source scope expression stage) :
        StatementStages source scope id scope
    | assignValue
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
        {value : ExpressionId} {projectionStages : List Stage}
        {valueStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator value)
        (projectionsStage : ExpressionsHaveStages source scope
          (placeIndexExpressions assignment.target) projectionStages)
        (valueStages : HasStage source scope value valueStage) :
        StatementStages source scope id scope
    | assignBitNot
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        {assignment : AssignmentResolution} {projectionStages : List Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (projectionsStage : ExpressionsHaveStages source scope
          (placeIndexExpressions assignment.target) projectionStages) :
        StatementStages source scope id scope
    | ifWithoutElse
        {scope thenFinal : StageScope} {id : StatementId}
        {node : StatementNode} {condition : ExpressionId}
        {thenBody : List StatementId} {conditionStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody none)
        (conditionStages : HasStage source scope condition conditionStage)
        (thenStages : StatementsStage source scope thenBody thenFinal) :
        StatementStages source scope id scope
    | ifWithElse
        {scope thenFinal elseFinal : StageScope} {id : StatementId}
        {node : StatementNode} {condition : ExpressionId}
        {thenBody elseBody : List StatementId} {conditionStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some elseBody))
        (conditionStages : HasStage source scope condition conditionStage)
        (thenStages : StatementsStage source scope thenBody thenFinal)
        (elseStages : StatementsStage source scope elseBody elseFinal) :
        StatementStages source scope id scope
    | block
        {scope innerFinal : StageScope} {id : StatementId}
        {node : StatementNode} {body : List StatementId}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (bodyStages : StatementsStage source scope body innerFinal) :
        StatementStages source scope id scope
    | matchWithoutDefault
        {scope hiddenScope : StageScope} {id : StatementId}
        {node : StatementNode} {resolution : MatchResolution}
        {scrutineeStage hiddenStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (default_eq : resolution.defaultBody = none)
        (scrutineeStages :
          HasStage source scope resolution.scrutinee scrutineeStage)
        (hiddenBinder : BinderGetsStage source scope
          resolution.hiddenScrutinee scrutineeStage hiddenStage hiddenScope)
        (caseStages : MatchCasesStage source scope scrutineeStage
          resolution.cases) :
        StatementStages source scope id scope
    | matchWithDefault
        {scope hiddenScope defaultFinal : StageScope} {id : StatementId}
        {node : StatementNode} {resolution : MatchResolution}
        {defaultBody : List StatementId}
        {scrutineeStage hiddenStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (default_eq : resolution.defaultBody = some defaultBody)
        (scrutineeStages :
          HasStage source scope resolution.scrutinee scrutineeStage)
        (hiddenBinder : BinderGetsStage source scope
          resolution.hiddenScrutinee scrutineeStage hiddenStage hiddenScope)
        (caseStages : MatchCasesStage source scope scrutineeStage
          resolution.cases)
        (defaultStages :
          StatementsStage source scope defaultBody defaultFinal) :
        StatementStages source scope id scope
    | forLoop
        {scope loopScope bodyFinal postFinal : StageScope}
        {id : StatementId} {node : StatementNode}
        {initializer post : List ForItemForm} {condition : ExpressionId}
        {body : List StatementId} {conditionStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializerStages : ForItemsStage source scope initializer loopScope)
        (conditionStages : HasStage source loopScope condition conditionStage)
        (bodyStages : StatementsStage source loopScope body bodyFinal)
        (postStages : ForItemsStage source loopScope post postFinal) :
        StatementStages source scope id scope
    | whileLoop
        {scope bodyFinal : StageScope} {id : StatementId}
        {node : StatementNode} {condition : ExpressionId}
        {body : List StatementId} {conditionStage : Stage}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (conditionStages : HasStage source scope condition conditionStage)
        (bodyStages : StatementsStage source scope body bodyFinal) :
        StatementStages source scope id scope
    | breakStmt
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .breakStmt) :
        StatementStages source scope id scope
    | continueStmt
        {scope : StageScope} {id : StatementId} {node : StatementNode}
        (contains : SourceSemantics.ContainsStatement source id node)
        (form_eq : node.form = .continueStmt) :
        StatementStages source scope id scope

  /-- Source-ordered statement classification with lexical scope threading. -/
  inductive StatementsStage (source : TypedSource) :
      StageScope → List StatementId → StageScope → Prop where
    | nil (scope : StageScope) : StatementsStage source scope [] scope
    | cons
        {scope middle final : StageScope} {statement : StatementId}
        {statements : List StatementId}
        (head : StatementStages source scope statement middle)
        (tail : StatementsStage source middle statements final) :
        StatementsStage source scope (statement :: statements) final

  /-- Stage one restricted `for` initializer or post item. -/
  inductive ForItemStages (source : TypedSource) :
      StageScope → ForItemForm → StageScope → Prop where
    | letUninitialized
        {scope final : StageScope} {binder : TypedBinder} {actual : Stage}
        (binderStage : BinderGetsStage source scope binder.id .deferred
          actual final) :
        ForItemStages source scope (.letDecl binder none) final
    | letInitialized
        {scope final : StageScope} {binder : TypedBinder}
        {initializer : ExpressionId} {initializerStage actual : Stage}
        (initializerStages : HasStage source scope initializer initializerStage)
        (binderStage : BinderGetsStage source scope binder.id initializerStage
          actual final) :
        ForItemStages source scope (.letDecl binder (some initializer)) final
    | expression
        {scope : StageScope} {expression : ExpressionId} {stage : Stage}
        (expressionStages : HasStage source scope expression stage) :
        ForItemStages source scope (.expression expression) scope
    | assignValue
        {scope : StageScope} {assignment : AssignmentResolution}
        {operator : Syntax.ValueAssignOp} {value : ExpressionId}
        {projectionStages : List Stage} {valueStage : Stage}
        (projectionsStage : ExpressionsHaveStages source scope
          (placeIndexExpressions assignment.target) projectionStages)
        (valueStages : HasStage source scope value valueStage) :
        ForItemStages source scope
          (.assignValue assignment operator value) scope
    | assignBitNot
        {scope : StageScope} {assignment : AssignmentResolution}
        {projectionStages : List Stage}
        (projectionsStage : ExpressionsHaveStages source scope
          (placeIndexExpressions assignment.target) projectionStages) :
        ForItemStages source scope (.assignBitNot assignment) scope

  /-- Sequential lexical threading for all `for` header items. -/
  inductive ForItemsStage (source : TypedSource) :
      StageScope → List ForItemForm → StageScope → Prop where
    | nil (scope : StageScope) : ForItemsStage source scope [] scope
    | cons
        {scope middle final : StageScope} {item : ForItemForm}
        {items : List ForItemForm}
        (head : ForItemStages source scope item middle)
        (tail : ForItemsStage source middle items final) :
        ForItemsStage source scope (item :: items) final

  /-- Classify one match arm after entering every binder retained by its flat
  prefix pattern. -/
  inductive MatchCaseStages (source : TypedSource) :
      StageScope → Stage → TypedMatchCase → Prop where
    | intro
        {scope armScope finalScope : StageScope} {scrutineeStage : Stage}
        {matchCase : TypedMatchCase}
        (bindersStage : BindersGetStage source scrutineeStage scope
          (patternBinders matchCase.pattern.resolution) armScope)
        (bodyStage : StatementsStage source armScope matchCase.body finalScope) :
        MatchCaseStages source scope scrutineeStage matchCase

  /-- Classify every explicit match arm in source order. -/
  inductive MatchCasesStage (source : TypedSource) :
      StageScope → Stage → List TypedMatchCase → Prop where
    | nil (scope : StageScope) (scrutineeStage : Stage) :
        MatchCasesStage source scope scrutineeStage []
    | cons
        {scope : StageScope} {scrutineeStage : Stage}
        {matchCase : TypedMatchCase} {cases : List TypedMatchCase}
        (head : MatchCaseStages source scope scrutineeStage matchCase)
        (tail : MatchCasesStage source scope scrutineeStage cases) :
        MatchCasesStage source scope scrutineeStage (matchCase :: cases)

end

/-- Initial function inputs are forced to compile time when the declaration is
marked or its complete result is stage-only; otherwise each input uses its own
marker and type. -/
inductive FunctionInputsStage (source : TypedSource)
    (returnComptime : Bool) (resultType : TypeSystem.Ty) :
    StageScope → Prop where
  | forced
      {scope : StageScope}
      (available : returnComptime = true ∨ ComptimeOnlyType resultType)
      (inputs : BindersGetStage source .comptime [] source.inputs scope) :
      FunctionInputsStage source returnComptime resultType scope
  | ordinary
      {scope : StageScope}
      (unmarked : returnComptime = false)
      (runtimeResult : ¬ ComptimeOnlyType resultType)
      (inputs : BindersGetDefaultStages source [] source.inputs scope) :
      FunctionInputsStage source returnComptime resultType scope

/-- Classify one root while preserving category and lexical scope behavior. -/
inductive RootStages (source : TypedSource) :
    StageScope → NodeId → StageScope → Prop where
  | expression
      {scope : StageScope} {expression : ExpressionId} {stage : Stage}
      (stages : HasStage source scope expression stage) :
      RootStages source scope (.expression expression) scope
  | statement
      {scope final : StageScope} {statement : StatementId}
      (stages : StatementStages source scope statement final) :
      RootStages source scope (.statement statement) final

/-- Classify all declaration roots in source order. -/
inductive RootsStage (source : TypedSource) :
    StageScope → List NodeId → StageScope → Prop where
  | nil (scope : StageScope) : RootsStage source scope [] scope
  | cons
      {scope middle final : StageScope} {root : NodeId}
      {roots : List NodeId}
      (head : RootStages source scope root middle)
      (tail : RootsStage source middle roots final) :
      RootsStage source scope (root :: roots) final

/-- Complete independent stage classification of a checked-function carrier. -/
inductive FunctionHasStages (function : CheckedFunction) : Prop where
  | intro
      {inputScope finalScope : StageScope}
      (sourceOwner : function.typedBody.owner = function.declaration)
      (graphClosed : SourceSemantics.OccurrenceGraphClosed function.typedBody)
      (localIdentities :
        SourceSemantics.LocalIdentityOwnership function.typedBody)
      (inputsStage : FunctionInputsStage function.typedBody
        function.returnComptime function.inferredBodyType inputScope)
      (rootsStage : RootsStage function.typedBody inputScope
        function.typedBody.roots finalScope) :
      FunctionHasStages function

end Solcore.SourceSemantics.Staging
