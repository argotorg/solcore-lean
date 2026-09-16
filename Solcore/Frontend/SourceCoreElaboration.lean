import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.WordLiteral
import Solcore.Resolved.Typing

/-!
The first executable bridge from occurrence-addressed typed source to Semantic
Core.  This deliberately small profile accepts only the closed builtin local
fragment already represented by `Resolved.Expr`; every staged source feature
fails with a located elaboration error instead of being assigned an invented
runtime meaning.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreElaboration

open SourceInference TypeSystem

/-- A failure is attached either to the declaration boundary, a typed source
occurrence, or an input binder whose type could not be specialized. -/
inductive ErrorSite where
  | declaration (id : Resolved.DeclarationId)
  | occurrence (id : OccurrenceId)
  | binder (id : Resolved.LocalId)
  deriving Repr, DecidableEq

/-- Typed expression forms intentionally left outside the first Core bridge. -/
inductive UnsupportedExpression where
  | declarationReference
  | call
  | lambda
  | proxy
  | index
  deriving Repr, BEq, DecidableEq

/-- Statement forms outside the tail-normal executable profile. -/
inductive UnsupportedStatement where
  | expression
  deriving Repr, BEq, DecidableEq

/-- Statements whose control-flow meaning cannot be preserved before the end
of the current statement list. -/
inductive NonTailStatement where
  | returnStmt
  | ifThen
  | block
  deriving Repr, BEq, DecidableEq

/-- Identify the branch of a tail conditional that can fall through. -/
inductive ConditionalBranch where
  | thenBranch
  | elseBranch
  deriving Repr, BEq, DecidableEq

/-- Precise rejection reasons at the typed-source-to-Core boundary. -/
inductive ErrorReason where
  | ownerMismatch
      (expected actual : Resolved.DeclarationId)
  | missingNode
  | expectedExpressionNode
  | expectedStatementNode
  | coercionsPresent (coercions : List CoercionStep)
  | requirementsPresent (requirements : List RequirementId)
  | flexibleTypeVariable (id : TypeVarId)
  | rigidTypeParameter (id : TypeParameterId)
  | nominalType (id : Resolved.DeclarationId)
  | unsupportedType (type : Ty)
  | polymorphicInput (variables : List TypeVarId)
  | duplicateInput (id : Resolved.LocalId)
  | polymorphicLocal (variables : List TypeVarId)
  | duplicateLocal (id : Resolved.LocalId)
  | unsupportedExpression (kind : UnsupportedExpression)
  | unsupportedStatement (kind : UnsupportedStatement)
  | uninitializedLet
  | nonTailStatement (kind : NonTailStatement)
  | missingElseBranch
  | statementListFallthrough
  | blockFallthrough
  | conditionalBranchFallthrough (branch : ConditionalBranch)
  | invalidWordLiteral (literal : Syntax.CoreLiteralValue)
  | unknownLocal (id : Resolved.LocalId)
  | expressionDepthLimit
  | statementDepthLimit
  | typedNodeTypeMismatch (expected actual : Core.Ty)
  | resolvedLoweringFailed
  | coreInferenceFailed
  | returnTypeMismatch (expected actual : Core.Ty)
  | unconsumedRequirements (requirements : List RequirementId)
  deriving Repr, DecidableEq

structure Error where
  site : ErrorSite
  reason : ErrorReason
  deriving Repr, DecidableEq

/-- A checked source function lowered to an open Semantic Core expression.
`inputs` fixes both stable resolved identities and the positional Core context. -/
structure ElaboratedFunction where
  declaration : Resolved.DeclarationId
  inputs : Resolved.Context
  resolved : Resolved.Expr
  core : Core.Expr
  returnType : Core.Ty
  resolvedLowered : resolved.lower? inputs.ids = some core
  coreTypeChecked : Core.infer? inputs.values core = some returnType
  deriving Repr

private def fail {alpha : Type} (site : ErrorSite) (reason : ErrorReason) :
    Except Error alpha :=
  .error { site, reason }

private def nominalHead? : Ty → Option Resolved.DeclarationId
  | .constructor (.declaration id) => some id
  | .application function _ => nominalHead? function
  | _ => none

/-- Project exactly the closed builtin structural types admitted by this
bridge.  Source functions, nominal data, mappings and staging forms remain at
the specialization boundary. -/
def lowerType (site : ErrorSite) : Ty → Except Error Core.Ty
  | .variable id => fail site (.flexibleTypeVariable id)
  | .parameter id => fail site (.rigidTypeParameter id)
  | .constructor (.builtin .unit) => .ok .unit
  | .constructor (.builtin .bool) => .ok .bool
  | .constructor (.builtin .word) => .ok .word
  | .constructor (.declaration id) => fail site (.nominalType id)
  | .product left right => do
      pure (.product (← lowerType site left) (← lowerType site right))
  | type@(.application _ _) =>
      match nominalHead? type with
      | some id => fail site (.nominalType id)
      | none => fail site (.unsupportedType type)
  | type@(.function _ _)
  | type@(.mapping _ _)
  | type@(.proxy _)
  | type@(.comptime _)
  | type@(.error) => fail site (.unsupportedType type)

private def lowerInputsAux (seen : List Resolved.LocalId) :
    List TypedBinder → Except Error Resolved.Context
  | [] => .ok []
  | binder :: rest => do
      if seen.contains binder.id then
        fail (.binder binder.id) (.duplicateInput binder.id)
      else if binder.scheme.quantified.isEmpty then
        let type ← lowerType (.binder binder.id) binder.scheme.body
        pure ((binder.id, type) :: (← lowerInputsAux (binder.id :: seen) rest))
      else
        fail (.binder binder.id) (.polymorphicInput binder.scheme.quantified)

private def lowerInputs (binders : List TypedBinder) :
    Except Error Resolved.Context :=
  lowerInputsAux [] binders

private def lookupExpression (source : TypedSource) (id : ExpressionId) :
    Except Error ExpressionNode :=
  match source.lookupNode? id.occurrence with
  | none => fail (.occurrence id.occurrence) .missingNode
  | some (.statement _) =>
      fail (.occurrence id.occurrence) .expectedExpressionNode
  | some (.expression node) => .ok node

private def lookupStatement (source : TypedSource) (id : StatementId) :
    Except Error StatementNode :=
  match source.lookupNode? id.occurrence with
  | none => fail (.occurrence id.occurrence) .missingNode
  | some (.expression _) =>
      fail (.occurrence id.occurrence) .expectedStatementNode
  | some (.statement node) => .ok node

private def directBinary (operator : Syntax.BinaryOp)
    (left right : Resolved.Expr) : Resolved.Expr :=
  match operator with
  | .multiply => .binary .wordMul left right
  | .divide => .binary .wordDiv left right
  | .modulo => .binary .wordMod left right
  | .add => .binary .wordAdd left right
  | .subtract => .binary .wordSub left right
  | .bitAnd => .binary .wordAnd left right
  | .bitXor => .binary .wordXor left right
  | .bitOr => .binary .wordOr left right
  | .greater => .binary .wordGt left right
  | .equal => .binary .wordEq left right
  | .less => .wordLt left right
  | .lessEqual => .unary .boolNot (.binary .wordGt left right)
  | .greaterEqual => .unary .boolNot (.wordLt left right)
  | .notEqual => .unary .boolNot (.binary .wordEq left right)
  | .logicalAnd => .ifE left right (.bool false)
  | .logicalOr => .ifE left (.bool true) right

private def productExpression : List Resolved.Expr → Resolved.Expr
  | [] => .unit
  | [element] => element
  | element :: rest => .pair element (productExpression rest)

/-- Lower one expression by following category-safe occurrence edges.  Fuel is
derived from the finite node table and turns malformed cyclic tables into a
located error. -/
private def lowerExpressionFuel (fuel : Nat) (source : TypedSource)
    (scope : List Resolved.LocalId) (id : ExpressionId) :
    Except Error Resolved.Expr :=
  match fuel with
  | 0 => fail (.occurrence id.occurrence) .expressionDepthLimit
  | fuel + 1 =>
    match lookupExpression source id with
    | .error error => .error error
    | .ok node =>
        if !node.coercions.isEmpty then
          fail (.occurrence id.occurrence) (.coercionsPresent node.coercions)
        else if !node.requirements.isEmpty then
          fail (.occurrence id.occurrence)
            (.requirementsPresent node.requirements)
        else
          match lowerType (.occurrence id.occurrence) node.type with
          | .error error => .error error
          | .ok _ =>
            match node.form with
            | .literal literal =>
                match interpretWordLiteral? ⟨node.span, literal⟩ with
                | some word => pure (.word word)
                | none =>
                    fail (.occurrence id.occurrence) (.invalidWordLiteral literal)
            | .reference _ (.local binder) =>
                if scope.contains binder then
                  pure (.var binder)
                else
                  fail (.occurrence id.occurrence) (.unknownLocal binder)
            | .reference _ (.builtinBoolean value) => pure (.bool value)
            | .reference _ (.declaration _) =>
                fail (.occurrence id.occurrence)
                  (.unsupportedExpression .declarationReference)
            | .group inner => lowerExpressionFuel fuel source scope inner
            | .tuple elements => do
                let resolved ← elements.mapM fun element =>
                  lowerExpressionFuel fuel source scope element
                pure (productExpression resolved)
            | .unary operator operand => do
                let operand ← lowerExpressionFuel fuel source scope operand
                pure <| match operator with
                  | .logicalNot => .unary .boolNot operand
                  | .bitNot => .unary .wordNot operand
            | .binary left operator right => do
                let left ← lowerExpressionFuel fuel source scope left
                let right ← lowerExpressionFuel fuel source scope right
                pure (directBinary operator left right)
            | .conditional condition thenBranch elseBranch => do
                pure (.ifE
                  (← lowerExpressionFuel fuel source scope condition)
                  (← lowerExpressionFuel fuel source scope thenBranch)
                  (← lowerExpressionFuel fuel source scope elseBranch))
            | .call _ _ _ => fail (.occurrence id.occurrence)
                (.unsupportedExpression .call)
            | .lambda _ _ _ => fail (.occurrence id.occurrence)
                (.unsupportedExpression .lambda)
            | .proxy _ => fail (.occurrence id.occurrence)
                (.unsupportedExpression .proxy)
            | .index _ _ => fail (.occurrence id.occurrence)
                (.unsupportedExpression .index)

private def ensureType (site : ErrorSite) (expected : Core.Ty)
    (type : Ty) : Except Error Unit := do
  let actual ← lowerType site type
  if actual = expected then
    pure ()
  else
    fail site (.typedNodeTypeMismatch expected actual)

private def lowerExpressionAs (fuel : Nat) (source : TypedSource)
    (scope : Resolved.Context) (expected : Core.Ty) (id : ExpressionId) :
    Except Error Resolved.Expr := do
  let node ← lookupExpression source id
  ensureType (.occurrence id.occurrence) expected node.type
  lowerExpressionFuel fuel source scope.ids id

private def statementRoots : List NodeId → Except Error (List StatementId)
  | [] => .ok []
  | .statement id :: rest => do
      pure (id :: (← statementRoots rest))
  | .expression id :: _ =>
      fail (.occurrence id.occurrence) .expectedStatementNode

private def finalStatement? : List StatementId → Option StatementId
  | [] => none
  | [id] => some id
  | _ :: rest => finalStatement? rest

/-- Lower the tail-normal statement profile.  Each statement edge consumes
fuel, while expression edges consume the remaining fuel independently. -/
private def lowerStatementsFuel : Nat → TypedSource → Resolved.Context →
    Core.Ty → ErrorSite → ErrorReason → List StatementId →
    Except Error Resolved.Expr
  | _, _, _, _, fallthroughSite, fallthroughReason, [] =>
      fail fallthroughSite fallthroughReason
  | 0, _, _, _, _, _, id :: _ =>
      fail (.occurrence id.occurrence) .statementDepthLimit
  | fuel + 1, source, scope, expected, fallthroughSite, fallthroughReason,
      id :: rest => do
    let node ← lookupStatement source id
    let site := ErrorSite.occurrence id.occurrence
    match node.form with
    | .letDecl binder initializer => do
        ensureType site .unit node.type
        if scope.ids.contains binder.id then
          fail (.binder binder.id) (.duplicateLocal binder.id)
        else if !binder.scheme.quantified.isEmpty then
          fail (.binder binder.id)
            (.polymorphicLocal binder.scheme.quantified)
        else
          let binderType ← lowerType (.binder binder.id) binder.scheme.body
          let initializer ← match initializer with
            | none => fail site .uninitializedLet
            | some initializer =>
                lowerExpressionAs fuel source scope binderType initializer
          let body ← lowerStatementsFuel fuel source
            ((binder.id, binderType) :: scope) expected
            fallthroughSite fallthroughReason rest
          pure (.letE binder.id initializer body)
    | .returnStmt value => do
        if !rest.isEmpty then
          fail site (.nonTailStatement .returnStmt)
        else
          ensureType site expected node.type
          match value with
          | none =>
              if expected = .unit then
                pure .unit
              else
                fail site (.typedNodeTypeMismatch expected .unit)
          | some value => lowerExpressionAs fuel source scope expected value
    | .ifThen condition thenBody elseBody => do
        if !rest.isEmpty then
          fail site (.nonTailStatement .ifThen)
        else
          match elseBody with
          | none => fail site .missingElseBranch
          | some elseBody => do
              ensureType site expected node.type
              let condition ← lowerExpressionAs fuel source scope .bool condition
              let thenBranch ← lowerStatementsFuel fuel source scope expected
                site (.conditionalBranchFallthrough .thenBranch) thenBody
              let elseBranch ← lowerStatementsFuel fuel source scope expected
                site (.conditionalBranchFallthrough .elseBranch) elseBody
              pure (.ifE condition thenBranch elseBranch)
    | .block body => do
        if !rest.isEmpty then
          fail site (.nonTailStatement .block)
        else
          ensureType site expected node.type
          lowerStatementsFuel fuel source scope expected site .blockFallthrough body
    | .expression _ _ =>
        fail site (.unsupportedStatement .expression)

/-- Lower a checked monomorphic builtin function body to the existing resolved
local fragment and then to an open, independently rechecked Core expression. -/
def elaborateFunction (function : CheckedFunction) :
    Except Error ElaboratedFunction := do
  let source := function.typedBody
  if source.owner != function.declaration then
    fail (.declaration function.declaration)
      (.ownerMismatch function.declaration source.owner)
  else
    let roots ← statementRoots source.roots
    let rootOccurrence ← match roots with
      | [] =>
          fail (.declaration function.declaration) .statementListFallthrough
      | root :: _ => pure root.occurrence
    let inputs ← lowerInputs source.inputs
    let expected ← lowerType (.declaration function.declaration)
      function.inferredBodyType
    let fallthroughSite := match finalStatement? roots with
      | some statement => ErrorSite.occurrence statement.occurrence
      | none => ErrorSite.declaration function.declaration
    let resolved ← lowerStatementsFuel (source.nodes.length + 1) source inputs
      expected fallthroughSite .statementListFallthrough roots
    unless function.solvedRequirements.isEmpty do
      throw {
        site := .declaration function.declaration
        reason := .unconsumedRequirements
          (function.solvedRequirements.map (·.id))
      }
    match lowered : resolved.lower? inputs.ids with
    | none => fail (.occurrence rootOccurrence) .resolvedLoweringFailed
    | some core =>
        match inferred : Core.infer? inputs.values core with
        | none => fail (.occurrence rootOccurrence) .coreInferenceFailed
        | some actual =>
            if equal : actual = expected then
              pure {
                declaration := function.declaration
                inputs
                resolved
                core
                returnType := expected
                resolvedLowered := lowered
                coreTypeChecked := by simpa [equal] using inferred
              }
            else
              fail (.occurrence rootOccurrence)
                (.returnTypeMismatch expected actual)

end Solcore.Frontend.SourceCoreElaboration
