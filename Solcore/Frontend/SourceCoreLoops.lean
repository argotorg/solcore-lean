import Solcore.Frontend.SourceCoreControl
import Solcore.Frontend.SourceCorePrimitive
import Solcore.Core.LocalLoop

/-! Scalar/product source loops compiled to ordinary Core. Initializer bindings
are visible to a for loop's condition, body and post, then discharged before
the outer continuation. Body/post local scopes are discharged each iteration.
The generated recursive closure adds administrative heap cells; full source
heap correspondence for those cells is pending. Entry consumers must check the
generated Core type before execution. No source evaluator is imported.
Assignment callbacks can supply a broader bare Word profile; the default
retains ordinary equal assignment. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLoops

open SourceInference

abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev Context := SourceCorePrimitive.Context
abbrev ExpressionLowerer := SourceCoreControl.ExpressionLowerer

/-- Entry profiles supply type and binder projection independently of control. -/
structure Policy where
  lowerExpression : ExpressionLowerer
  readStatement : TypedSource → StatementId → Except Error (StatementNode × Core.Ty) :=
    SourceCoreBasic.readStatement
  lowerBinder : TypedSource → Scope → TypedBinder → Except Error Core.Ty :=
    SourceCoreBasic.lowerBinder
  lowerAssignment : TypedSource → Scope → AssignmentResolution → Syntax.ValueAssignOp →
    Except Error (Nat × Core.Ty) := SourceCoreBasic.lowerAssignment
  assignValue : Option (ExpressionLowerer → Nat → TypedSource → Scope → SourceCoreElaboration.ErrorSite →
    AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Core.Ty → Core.Expr →
    (ExpressionId → Core.Word) → Except Error Core.Expr) := none
  assignBitNot : Option (TypedSource → Scope → SourceCoreElaboration.ErrorSite →
    AssignmentResolution → Core.Ty → Core.Expr → Except Error Core.Expr) := none

private def assignValue (policy : Policy) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (reasonAt : ExpressionId → Core.Word) : Except Error Core.Expr := do
  match operator, policy.assignValue with
  | .equal, _ | _, none =>
      let (index, payloadType) ← policy.lowerAssignment source scope assignment operator
      let rhs ← policy.lowerExpression fuel source scope rhs reasonAt
      SourceCoreBasic.ensureType (.binder assignment.target.root) payloadType rhs.type
      pure (Core.LocalSequence.assign outputType (.var index) rhs.expression next)
  | _, some callback =>
      callback policy.lowerExpression fuel source scope site assignment operator rhs outputType next reasonAt

/-- Header items have no statement identity. They use the same authenticated
binder/expression/assignment checks and thread newly allocated lexical cells.
Only the supplied continuation determines whether that scope persists. -/
private def lowerForItems (policy : Policy) (parentSite : SourceCoreElaboration.ErrorSite) : Nat → TypedSource → Scope →
    List ForItemForm → Core.Ty → (ExpressionId → Core.Word) → (Scope → Except Error Core.Expr) →
    Except Error Core.Expr
  | _, _, scope, [], _, _, next => next scope
  | 0, source, _, _ :: _, _, _, _ => .error (.traversalExhausted (.declaration source.owner))
  | fuel + 1, source, scope, item :: rest, resultType, reasonAt, next => do
      let controlType := Core.LocalLoop.controlType resultType
      match item with
      | .letDecl binder initializer =>
          let payloadType ← policy.lowerBinder source scope binder
          let body ← lowerForItems policy parentSite fuel source ((binder.id, payloadType) :: scope)
            rest resultType reasonAt next
          match initializer with
          | none => pure (Core.LocalSequence.letUninitialized payloadType body)
          | some initializer =>
              let initializer ← policy.lowerExpression fuel source scope initializer reasonAt
              SourceCoreBasic.ensureType (.binder binder.id) payloadType initializer.type
              pure (Core.LocalSequence.letInitialized controlType payloadType initializer.expression body)
      | .expression expression =>
          let expression ← policy.lowerExpression fuel source scope expression reasonAt
          let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
          pure (Core.LocalSequence.discard controlType expression.expression body)
      | .assignValue assignment operator rhs =>
          let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
          assignValue policy fuel source scope parentSite assignment operator rhs controlType body reasonAt
      | .assignBitNot assignment =>
          match policy.assignBitNot with
          | none => .error (.unsupportedForItem item)
          | some callback =>
              let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
              callback source scope parentSite assignment controlType body

def lowerFlowStatementsWithPolicy (policy : Policy) : Nat → TypedSource → Scope →
    List StatementId → Core.Ty → (ExpressionId → Core.Word) → Bool → Core.Word → Except Error Core.Expr
  | _, _, _, [], resultType, _, _, _ => .ok (Core.LocalLoop.fallthrough resultType)
  | 0, _, _, id :: _, _, _, _, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id :: rest, resultType, reasonAt, tailReturns, selfReason => do
      let (node, type) ← policy.readStatement source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      let controlType := Core.LocalLoop.controlType resultType
      match node.form with
      | .letDecl binder initializer =>
          SourceCoreBasic.ensureType site .unit type
          let payloadType ← policy.lowerBinder source scope binder
          match initializer with
          | none =>
              let body ← lowerFlowStatementsWithPolicy policy fuel source ((binder.id, payloadType) :: scope)
                rest resultType reasonAt tailReturns selfReason
              pure (Core.LocalSequence.letUninitialized payloadType body)
          | some initializer =>
              let initializer ← policy.lowerExpression fuel source scope initializer reasonAt
              SourceCoreBasic.ensureType (.binder binder.id) payloadType initializer.type
              let body ← lowerFlowStatementsWithPolicy policy fuel source ((binder.id, payloadType) :: scope)
                rest resultType reasonAt tailReturns selfReason
              pure (Core.LocalSequence.letInitialized controlType payloadType initializer.expression body)
      | .assignValue assignment operator value =>
          SourceCoreBasic.ensureType site .unit type
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          assignValue policy fuel source scope site assignment operator value controlType body reasonAt
      | .assignBitNot assignment =>
          SourceCoreBasic.ensureType site .unit type
          match policy.assignBitNot with
          | none => .error (.unsupportedStatement id node.form)
          | some callback =>
              let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
              callback source scope site assignment controlType body
      | .returnStmt none =>
          SourceCoreBasic.ensureType site resultType type
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalLoop.returned .unit)
      | .returnStmt (some value) =>
          SourceCoreBasic.ensureType site resultType type
          let value ← policy.lowerExpression fuel source scope value reasonAt
          SourceCoreBasic.ensureType site resultType value.type
          pure (Core.LocalLoop.returnValue resultType value.expression)
      | .expression value trailingSemicolon =>
          let value ← policy.lowerExpression fuel source scope value reasonAt
          if !trailingSemicolon && tailReturns && rest.isEmpty then
            SourceCoreBasic.ensureType site resultType type
            SourceCoreBasic.ensureType site resultType value.type
            pure (Core.LocalLoop.returnValue resultType value.expression)
          else
            if trailingSemicolon then SourceCoreBasic.ensureType site .unit type
            else SourceCoreBasic.ensureType site type value.type
            let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
            pure (Core.LocalSequence.discard controlType value.expression body)
      | .block statements =>
          let block ← lowerFlowStatementsWithPolicy policy fuel source scope statements resultType reasonAt false selfReason
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          pure (Core.LocalLoop.sequence resultType block body)
      | .ifThen condition thenBody elseBody =>
          let condition ← policy.lowerExpression fuel source scope condition reasonAt
          SourceCoreBasic.ensureType site .bool condition.type
          let thenBranch ← lowerFlowStatementsWithPolicy policy fuel source scope thenBody resultType reasonAt false selfReason
          let elseBranch ← match elseBody with
            | none => pure (Core.LocalLoop.fallthrough resultType)
            | some statements => lowerFlowStatementsWithPolicy policy fuel source scope statements resultType reasonAt false selfReason
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          pure (Core.LocalLoop.sequence resultType
            (Core.LocalLoop.conditional resultType condition.expression thenBranch elseBranch) body)
      | .whileLoop condition statements =>
          SourceCoreBasic.ensureType site .unit type
          let condition ← policy.lowerExpression fuel source scope condition reasonAt
          SourceCoreBasic.ensureType site .bool condition.type
          let loopBody ← lowerFlowStatementsWithPolicy policy fuel source scope statements resultType reasonAt false selfReason
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          pure (Core.LocalLoop.sequence resultType
            (Core.LocalLoop.whileLoop resultType condition.expression loopBody selfReason) body)
      | .forLoop initializer condition post statements =>
          SourceCoreBasic.ensureType site .unit type
          let loop ← lowerForItems policy site fuel source scope initializer resultType reasonAt fun loopScope => do
            let condition ← policy.lowerExpression fuel source loopScope condition reasonAt
            SourceCoreBasic.ensureType site .bool condition.type
            let loopBody ← lowerFlowStatementsWithPolicy policy fuel source loopScope statements resultType reasonAt false selfReason
            let post ← lowerForItems policy site fuel source loopScope post resultType reasonAt
              (fun _ => pure (Core.LocalLoop.fallthrough resultType))
            pure (Core.LocalLoop.iterate resultType condition.expression loopBody post selfReason)
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          pure (Core.LocalLoop.sequence resultType loop body)
      | .breakStmt =>
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalLoop.breaking resultType)
      | .continueStmt =>
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalLoop.continuing resultType)
      | form => .error (.unsupportedStatement id form)

/-- Compatibility wrapper for the ordinary scalar/product profile. -/
def lowerFlowStatementsWithExpression (lowerExpression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (statements : List StatementId)
    (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (tailReturns : Bool) (selfReason : Core.Word) : Except Error Core.Expr :=
  lowerFlowStatementsWithPolicy { lowerExpression := lowerExpression } fuel source scope statements
    resultType reasonAt tailReturns selfReason

/-- Entry policies supply their authenticated expression profile and diagnostic
table. Consumers check the open result against `sum Word resultType` before
execution; escaped loop control becomes the distinct supplied failure token. -/
def lowerStatementsWithPolicy (policy : Policy)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (statements : List StatementId)
    (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (fellThroughReason escapedReason : Core.Word) : Except Error Core.Expr := do
  let flow ← lowerFlowStatementsWithPolicy policy fuel source scope statements
    resultType reasonAt true escapedReason
  let fallback := if resultType = .unit then Core.LanguageResult.success .unit
    else Core.LanguageResult.failure resultType (.word fellThroughReason)
  pure (Core.LocalControl.finish resultType (Core.LocalLoop.toControl resultType flow escapedReason) fallback)

/-- Compatibility wrapper retaining the ordinary expression-policy API. -/
def lowerStatementsWithExpression (lowerExpression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (statements : List StatementId)
    (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (fellThroughReason escapedReason : Core.Word) : Except Error Core.Expr :=
  lowerStatementsWithPolicy { lowerExpression := lowerExpression } fuel source scope statements resultType
    reasonAt fellThroughReason escapedReason

def lowerStatementsWithReasons (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty) (reasonAt : ExpressionId → Core.Word)
    (fellThroughReason escapedReason : Core.Word) : Except Error Core.Expr :=
  lowerStatementsWithExpression
    (fun fuel source scope id reasonAt => SourceCorePrimitive.lowerExpressionWithReasons
      fuel context source scope id reasonAt)
    fuel source scope statements resultType reasonAt fellThroughReason escapedReason

def lowerStatements (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (uninitializedReason fellThroughReason escapedReason : Core.Word) : Except Error Core.Expr :=
  lowerStatementsWithReasons fuel context source scope statements resultType
    (fun _ => uninitializedReason) fellThroughReason escapedReason

end Solcore.Frontend.SourceCoreLoops
