import Solcore.Frontend.SourceCoreBasic
import Solcore.Core.LocalControl

/-! Scalar/product expressions and scoped local control compiled to ordinary
Core. Function tails may return an expression; block and conditional bodies
discard such expressions unless they contain an explicit return. The control
envelope preserves early returns and restores the outer lexical scope while
keeping the shared heap. Loops, calls, evidence and polymorphism remain outside
this fragment. Compilation depth and runtime fuel are separate quantities. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreControl

open SourceInference

abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

/-- Recurse through conditional/group/tuple expressions so conditional children
can occur at any of those positions. Scalar leaves retain Basic's owner, type,
requirement, coercion and local-slot validation. -/
def lowerExpressionWithReasons : Nat → TypedSource → Scope → ExpressionId → (ExpressionId → Core.Word) →
    Except Error LoweredExpr
  | 0, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id, reasonAt => do
      let (node, type) ← SourceCoreBasic.readExpression source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      match node.form with
      | .conditional condition thenBranch elseBranch =>
          let condition ← lowerExpressionWithReasons fuel source scope condition reasonAt
          SourceCoreBasic.ensureType site .bool condition.type
          let thenBranch ← lowerExpressionWithReasons fuel source scope thenBranch reasonAt
          let elseBranch ← lowerExpressionWithReasons fuel source scope elseBranch reasonAt
          SourceCoreBasic.ensureType site type thenBranch.type
          SourceCoreBasic.ensureType site type elseBranch.type
          pure ⟨type, Core.LocalControl.choose type condition.expression
            thenBranch.expression elseBranch.expression⟩
      | .group inner =>
          let inner ← lowerExpressionWithReasons fuel source scope inner reasonAt
          SourceCoreBasic.ensureType site type inner.type
          pure inner
      | .tuple [left, right] =>
          let left ← lowerExpressionWithReasons fuel source scope left reasonAt
          let right ← lowerExpressionWithReasons fuel source scope right reasonAt
          SourceCoreBasic.ensureType site type (.product left.type right.type)
          pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
      | _ => SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id)

/-- `tailReturns` is true only for a function's top-level list. Nested blocks
and conditional bodies execute statement sequences, so their last expression
falls through. Temporary Core binders are introduced by the helper layer. -/
abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId →
  (ExpressionId → Core.Word) → Except Error LoweredExpr

/-- Statement control is independent of the authenticated expression profile. -/
def lowerFlowStatementsWithExpression (lowerExpression : ExpressionLowerer) : Nat → TypedSource → Scope → List StatementId → Core.Ty →
    (ExpressionId → Core.Word) → Bool →
    Except Error Core.Expr
  | _, _, _, [], resultType, _, _ => .ok (Core.LocalControl.fallthrough resultType)
  | 0, _, _, id :: _, _, _, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id :: rest, resultType, reasonAt, tailReturns => do
      let (node, type) ← SourceCoreBasic.readStatement source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      let controlType := Core.LocalControl.controlType resultType
      match node.form with
      | .letDecl binder initializer =>
          SourceCoreBasic.ensureType site .unit type
          let payloadType ← SourceCoreBasic.lowerBinder source scope binder
          match initializer with
          | none =>
              let body ← lowerFlowStatementsWithExpression lowerExpression fuel source ((binder.id, payloadType) :: scope)
                rest resultType reasonAt tailReturns
              pure (Core.LocalSequence.letUninitialized payloadType body)
          | some initializer =>
              let initializer ← lowerExpression fuel source scope initializer reasonAt
              SourceCoreBasic.ensureType (.binder binder.id) payloadType initializer.type
              let body ← lowerFlowStatementsWithExpression lowerExpression fuel source ((binder.id, payloadType) :: scope)
                rest resultType reasonAt tailReturns
              pure (Core.LocalSequence.letInitialized controlType payloadType initializer.expression body)
      | .assignValue assignment operator value =>
          SourceCoreBasic.ensureType site .unit type
          let (index, payloadType) ← SourceCoreBasic.lowerAssignment source scope assignment operator
          let value ← lowerExpression fuel source scope value reasonAt
          SourceCoreBasic.ensureType site payloadType value.type
          let body ← lowerFlowStatementsWithExpression lowerExpression fuel source scope rest resultType reasonAt tailReturns
          pure (Core.LocalSequence.assign controlType (.var index) value.expression body)
      | .returnStmt none =>
          SourceCoreBasic.ensureType site resultType type
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalControl.returned .unit)
      | .returnStmt (some value) =>
          SourceCoreBasic.ensureType site resultType type
          let value ← lowerExpression fuel source scope value reasonAt
          SourceCoreBasic.ensureType site resultType value.type
          pure (Core.LocalControl.returnValue resultType value.expression)
      | .expression value trailingSemicolon =>
          let value ← lowerExpression fuel source scope value reasonAt
          if !trailingSemicolon && tailReturns && rest.isEmpty then
            SourceCoreBasic.ensureType site resultType type
            SourceCoreBasic.ensureType site resultType value.type
            pure (Core.LocalControl.returnValue resultType value.expression)
          else
            if trailingSemicolon then SourceCoreBasic.ensureType site .unit type
            else SourceCoreBasic.ensureType site type value.type
            let body ← lowerFlowStatementsWithExpression lowerExpression fuel source scope rest resultType reasonAt tailReturns
            pure (Core.LocalSequence.discard controlType value.expression body)
      | .block statements =>
          let block ← lowerFlowStatementsWithExpression lowerExpression fuel source scope statements resultType reasonAt false
          let body ← lowerFlowStatementsWithExpression lowerExpression fuel source scope rest resultType reasonAt tailReturns
          pure (Core.LocalControl.sequence resultType block body)
      | .ifThen condition thenBody elseBody =>
          let condition ← lowerExpression fuel source scope condition reasonAt
          SourceCoreBasic.ensureType site .bool condition.type
          let thenBranch ← lowerFlowStatementsWithExpression lowerExpression fuel source scope thenBody resultType reasonAt false
          let elseBranch ← match elseBody with
            | none => pure (Core.LocalControl.fallthrough resultType)
            | some statements => lowerFlowStatementsWithExpression lowerExpression fuel source scope statements resultType reasonAt false
          let body ← lowerFlowStatementsWithExpression lowerExpression fuel source scope rest resultType reasonAt tailReturns
          pure (Core.LocalControl.sequence resultType
            (Core.LocalControl.conditional resultType condition.expression thenBranch elseBranch) body)
      | form => .error (.unsupportedStatement id form)

def lowerFlowStatementsWithReasons (fuel : Nat) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (reasonAt : ExpressionId → Core.Word) (tailReturns : Bool) : Except Error Core.Expr :=
  lowerFlowStatementsWithExpression lowerExpressionWithReasons fuel source scope statements
    resultType reasonAt tailReturns

/-- Use a checked expression profile without changing scope or control rules. -/
def lowerStatementsWithExpression (lowerExpression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (reasonAt : ExpressionId → Core.Word) (fellThroughReason : Core.Word) : Except Error Core.Expr := do
  let flow ← lowerFlowStatementsWithExpression lowerExpression fuel source scope statements
    resultType reasonAt true
  let fallback := if resultType = .unit then Core.LanguageResult.success .unit
    else Core.LanguageResult.failure resultType (.word fellThroughReason)
  pure (Core.LocalControl.finish resultType flow fallback)

/-- A constant token is convenient for fragment proofs and small callers. -/
def lowerExpression (fuel : Nat) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reason : Core.Word) : Except Error LoweredExpr :=
  lowerExpressionWithReasons fuel source scope id (fun _ => reason)

def lowerFlowStatements (fuel : Nat) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (reason : Core.Word) (tailReturns : Bool) : Except Error Core.Expr :=
  lowerFlowStatementsWithReasons fuel source scope statements resultType (fun _ => reason) tailReturns

/-- Finish a function's control envelope. Falling through a non-Unit function
produces the caller's language-failure token and retains preceding heap effects.
The provider lets authenticated callers retain each uninitialized-read site. -/
def lowerStatementsWithReasons (fuel : Nat) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (reasonAt : ExpressionId → Core.Word) (fellThroughReason : Core.Word) : Except Error Core.Expr := do
  let flow ← lowerFlowStatementsWithReasons fuel source scope statements resultType reasonAt true
  let fallback := if resultType = .unit then Core.LanguageResult.success .unit
    else Core.LanguageResult.failure resultType (.word fellThroughReason)
  pure (Core.LocalControl.finish resultType flow fallback)

def lowerStatements (fuel : Nat) (source : TypedSource) (scope : Scope)
    (statements : List StatementId) (resultType : Core.Ty)
    (uninitializedReason fellThroughReason : Core.Word) : Except Error Core.Expr :=
  lowerStatementsWithReasons fuel source scope statements resultType
    (fun _ => uninitializedReason) fellThroughReason

/-! Equations for composition with independent source/Core child derivations. -/

theorem lowerExpression_conditional
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty} {condition thenId elseId : ExpressionId}
    {conditionCode thenCode elseCode : Core.Expr} {reasonAt : ExpressionId → Core.Word}
    (metadata : SourceCoreBasic.readExpression source id = .ok (node, type))
    (form : node.form = .conditional condition thenId elseId)
    (conditionLowered : lowerExpressionWithReasons fuel source scope condition reasonAt =
      .ok ⟨.bool, conditionCode⟩)
    (thenLowered : lowerExpressionWithReasons fuel source scope thenId reasonAt = .ok ⟨type, thenCode⟩)
    (elseLowered : lowerExpressionWithReasons fuel source scope elseId reasonAt = .ok ⟨type, elseCode⟩) :
    lowerExpressionWithReasons (fuel + 1) source scope id reasonAt =
      .ok ⟨type, Core.LocalControl.choose type conditionCode thenCode elseCode⟩ := by
  simp [lowerExpressionWithReasons, metadata, form, conditionLowered, thenLowered, elseLowered,
    SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lowerFlowStatements_block
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest statements : List StatementId}
    {node : StatementNode} {type resultType : Core.Ty} {blockCode next : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool}
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, type))
    (form : node.form = .block statements)
    (blockLowered : lowerFlowStatementsWithReasons fuel source scope statements resultType reasonAt false =
      .ok blockCode)
    (tailLowered : lowerFlowStatementsWithReasons fuel source scope rest resultType reasonAt tailReturns =
      .ok next) :
    lowerFlowStatementsWithReasons (fuel + 1) source scope (id :: rest) resultType reasonAt tailReturns =
      .ok (Core.LocalControl.sequence resultType blockCode next) := by
  simp only [lowerFlowStatementsWithReasons] at blockLowered tailLowered
  simp [lowerFlowStatementsWithReasons, lowerFlowStatementsWithExpression, metadata, form, blockLowered, tailLowered,
    bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lowerFlowStatements_ifWithElse
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest thenBody elseBody : List StatementId}
    {node : StatementNode} {type resultType : Core.Ty} {condition : ExpressionId}
    {conditionCode thenCode elseCode next : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool}
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, type))
    (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionLowered : lowerExpressionWithReasons fuel source scope condition reasonAt = .ok ⟨.bool, conditionCode⟩)
    (thenLowered : lowerFlowStatementsWithReasons fuel source scope thenBody resultType reasonAt false = .ok thenCode)
    (elseLowered : lowerFlowStatementsWithReasons fuel source scope elseBody resultType reasonAt false = .ok elseCode)
    (tailLowered : lowerFlowStatementsWithReasons fuel source scope rest resultType reasonAt tailReturns = .ok next) :
    lowerFlowStatementsWithReasons (fuel + 1) source scope (id :: rest) resultType reasonAt tailReturns =
      .ok (Core.LocalControl.sequence resultType
        (Core.LocalControl.conditional resultType conditionCode thenCode elseCode) next) := by
  simp only [lowerFlowStatementsWithReasons] at thenLowered elseLowered tailLowered
  simp [lowerFlowStatementsWithReasons, lowerFlowStatementsWithExpression, metadata, form, conditionLowered, thenLowered, elseLowered,
    tailLowered, SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lowerFlowStatements_ifWithoutElse
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest thenBody : List StatementId}
    {node : StatementNode} {type resultType : Core.Ty} {condition : ExpressionId}
    {conditionCode thenCode next : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {tailReturns : Bool}
    (metadata : SourceCoreBasic.readStatement source id = .ok (node, type))
    (form : node.form = .ifThen condition thenBody none)
    (conditionLowered : lowerExpressionWithReasons fuel source scope condition reasonAt = .ok ⟨.bool, conditionCode⟩)
    (thenLowered : lowerFlowStatementsWithReasons fuel source scope thenBody resultType reasonAt false = .ok thenCode)
    (tailLowered : lowerFlowStatementsWithReasons fuel source scope rest resultType reasonAt tailReturns = .ok next) :
    lowerFlowStatementsWithReasons (fuel + 1) source scope (id :: rest) resultType reasonAt tailReturns =
      .ok (Core.LocalControl.sequence resultType
        (Core.LocalControl.conditional resultType conditionCode thenCode (Core.LocalControl.fallthrough resultType)) next) := by
  simp only [lowerFlowStatementsWithReasons] at thenLowered tailLowered
  simp [lowerFlowStatementsWithReasons, lowerFlowStatementsWithExpression, metadata, form, conditionLowered, thenLowered,
    tailLowered, SourceCoreBasic.ensureType, bind, Except.bind, pure, Pure.pure, Except.pure]

end Solcore.Frontend.SourceCoreControl
