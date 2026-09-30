import Solcore.Frontend.SourceCoreLocalCell
import Solcore.Core.LocalSequence

/-! A scalar/product source fragment compiled to ordinary Core language results.
The traversal budget bounds compilation depth; it is unrelated to runtime fuel.
Scopes contain only optional-cell references. Temporary payload binders are
introduced and weakened by Core.LocalSequence, never added to the source scope.
There is no runtime evaluator fallback. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreBasic

open SourceInference

abbrev Scope := SourceCoreLocalCell.Scope

structure LoweredExpr where
  type : Core.Ty
  expression : Core.Expr
  deriving Repr, BEq, DecidableEq

inductive Error where
  | traversalExhausted (site : SourceCoreElaboration.ErrorSite)
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  | missingExpression (id : ExpressionId)
  | missingStatement (id : StatementId)
  | requirementsPresent (id : ExpressionId)
  | coercionsPresent (id : ExpressionId)
  | typeProjection (error : SourceCoreElaboration.Error)
  | typeMismatch (site : SourceCoreElaboration.ErrorSite) (expected actual : Core.Ty)
  | invalidWordLiteral (id : ExpressionId) (literal : Syntax.CoreLiteralValue)
  | localRead (error : SourceCoreLocalCell.Error)
  | unsupportedExpression (id : ExpressionId) (form : ExpressionForm)
  | unsupportedStatement (id : StatementId) (form : StatementForm)
  | polymorphicBinding (id : Resolved.LocalId)
  | bindingRequirementsPresent (id : Resolved.LocalId)
  | comptimeBinding (id : Resolved.LocalId)
  | duplicateBinding (id : Resolved.LocalId)
  | assignmentRequirementsPresent (id : Resolved.LocalId)
  | projectedAssignment (id : Resolved.LocalId)
  | unsupportedAssignmentOperator (operator : Syntax.ValueAssignOp)
  | missingBinding (id : Resolved.LocalId)
  | nonTailExpression (id : StatementId)
  | missingReturn (resultType : Core.Ty)
  deriving Repr

def ensureType (site : SourceCoreElaboration.ErrorSite) (expected actual : Core.Ty) :
    Except Error Unit :=
  if expected = actual then .ok () else .error (.typeMismatch site expected actual)

def projectType (site : SourceCoreElaboration.ErrorSite) (type : TypeSystem.Ty) :
    Except Error Core.Ty :=
  (SourceCoreElaboration.lowerType site type).mapError Error.typeProjection

/-- Every compiled occurrence must belong to the source and carry closed,
evidence-free scalar/product metadata. Integer-literal evidence is a later slice. -/
def readExpression (source : TypedSource) (id : ExpressionId) :
    Except Error (ExpressionNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then
    throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => .error (.missingExpression id)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  let type ← projectType (.occurrence id.occurrence) node.type
  pure (node, type)

def readStatement (source : TypedSource) (id : StatementId) :
    Except Error (StatementNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then
    throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupStatement? id with
    | some node => pure node
    | none => .error (.missingStatement id)
  let type ← projectType (.occurrence id.occurrence) node.type
  pure (node, type)

def lowerBinder (source : TypedSource) (scope : Scope) (binder : TypedBinder) :
    Except Error Core.Ty := do
  if binder.id.owner ≠ source.owner then
    throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then
    throw (.duplicateBinding binder.id)
  projectType (.binder binder.id) binder.scheme.body

def lowerAssignment (source : TypedSource) (scope : Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) :
    Except Error (Nat × Core.Ty) := do
  if operator ≠ .equal then throw (.unsupportedAssignmentOperator operator)
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← projectType (.binder binder) assignment.target.type
  ensureType (.binder binder) type projected
  pure (index, type)

def lowerExpression : Nat → TypedSource → Scope → ExpressionId → Core.Word →
    Except Error LoweredExpr
  | 0, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id, reason => do
      let (node, type) ← readExpression source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      match node.form with
      | .literal literal =>
          ensureType site .word type
          let value ← match interpretWordLiteral? ⟨node.span, literal⟩ with
            | some value => pure value
            | none => .error (.invalidWordLiteral id literal)
          pure ⟨.word, Core.LanguageResult.success (.word value)⟩
      | .reference _ (.builtinBoolean value) =>
          ensureType site .bool type
          pure ⟨.bool, Core.LanguageResult.success (.bool value)⟩
      | .reference _ (.local _) =>
          let expression ← (SourceCoreLocalCell.lowerRead source scope id reason).mapError Error.localRead
          pure ⟨type, expression⟩
      | .group inner =>
          let inner ← lowerExpression fuel source scope inner reason
          ensureType site type inner.type
          pure inner
      | .tuple [] =>
          ensureType site .unit type
          pure ⟨.unit, Core.LanguageResult.success .unit⟩
      | .tuple [left, right] =>
          let left ← lowerExpression fuel source scope left reason
          let right ← lowerExpression fuel source scope right reason
          ensureType site type (.product left.type right.type)
          pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
      | form => .error (.unsupportedExpression id form)

/-- Explicit returns finish this list immediately. A final expression without
a semicolon is its implicit return. Other expression statements discard their
successful value, while preserving failure and store effects. -/
def lowerStatements : Nat → TypedSource → Scope → List StatementId → Core.Ty → Core.Word →
    Except Error Core.Expr
  | _, _, _, [], resultType, _ =>
      if resultType = .unit then .ok (Core.LanguageResult.success .unit)
      else .error (.missingReturn resultType)
  | 0, _, _, id :: _, _, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, source, scope, id :: rest, resultType, reason => do
      let (node, type) ← readStatement source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      match node.form with
      | .letDecl binder initializer =>
          ensureType site .unit type
          let payloadType ← lowerBinder source scope binder
          match initializer with
          | none =>
              let body ← lowerStatements fuel source ((binder.id, payloadType) :: scope)
                rest resultType reason
              pure (Core.LocalSequence.letUninitialized payloadType body)
          | some initializer =>
              let initializer ← lowerExpression fuel source scope initializer reason
              ensureType (.binder binder.id) payloadType initializer.type
              let body ← lowerStatements fuel source ((binder.id, payloadType) :: scope)
                rest resultType reason
              pure (Core.LocalSequence.letInitialized resultType payloadType initializer.expression body)
      | .assignValue assignment operator value =>
          ensureType site .unit type
          let (index, payloadType) ← lowerAssignment source scope assignment operator
          let value ← lowerExpression fuel source scope value reason
          ensureType site payloadType value.type
          let body ← lowerStatements fuel source scope rest resultType reason
          pure (Core.LocalSequence.assign resultType (.var index) value.expression body)
      | .returnStmt none =>
          ensureType site resultType type
          ensureType site .unit type
          pure (Core.LanguageResult.success .unit)
      | .returnStmt (some value) =>
          ensureType site resultType type
          let value ← lowerExpression fuel source scope value reason
          ensureType site resultType value.type
          pure value.expression
      | .expression value trailingSemicolon =>
          if trailingSemicolon then
            ensureType site .unit type
            let value ← lowerExpression fuel source scope value reason
            let body ← lowerStatements fuel source scope rest resultType reason
            pure (Core.LocalSequence.discard resultType value.expression body)
          else if rest.isEmpty then
            ensureType site resultType type
            let value ← lowerExpression fuel source scope value reason
            ensureType site resultType value.type
            pure value.expression
          else throw (.nonTailExpression id)
      | form => .error (.unsupportedStatement id form)

/-! Equations expose the actual compiler branches for semantic composition.
Metadata checks are separate executable operations, so proof consumers can
establish them from structural source certificates without assuming lowering. -/

theorem readExpression_eq
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (projection : SourceCoreElaboration.lowerType (.occurrence id.occurrence) node.type = .ok type) :
    readExpression source id = .ok (node, type) := by
  simp [readExpression, owner, found, requirements, coercions, projectType, projection,
    bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem readStatement_eq
    {source : TypedSource} {id : StatementId} {node : StatementNode} {type : Core.Ty}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupStatement? id = some node)
    (projection : SourceCoreElaboration.lowerType (.occurrence id.occurrence) node.type = .ok type) :
    readStatement source id = .ok (node, type) := by
  simp [readStatement, owner, found, projectType, projection,
    bind, Except.bind, pure, Pure.pure, Except.pure, Except.mapError]

theorem lowerExpression_unit
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {node : ExpressionNode} {reason : Core.Word}
    (metadata : readExpression source id = .ok (node, .unit))
    (form : node.form = .tuple []) :
    lowerExpression (fuel + 1) source scope id reason =
      .ok ⟨.unit, Core.LanguageResult.success .unit⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, ensureType]

theorem lowerExpression_bool
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {value : Bool} {reason : Core.Word}
    (metadata : readExpression source id = .ok (node, .bool))
    (form : node.form = .reference name (.builtinBoolean value)) :
    lowerExpression (fuel + 1) source scope id reason =
      .ok ⟨.bool, Core.LanguageResult.success (.bool value)⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, ensureType]

theorem lowerExpression_word
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {value reason : Core.Word}
    (metadata : readExpression source id = .ok (node, .word))
    (form : node.form = .literal literal)
    (decoded : interpretWordLiteral? ⟨node.span, literal⟩ = some value) :
    lowerExpression (fuel + 1) source scope id reason =
      .ok ⟨.word, Core.LanguageResult.success (.word value)⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, ensureType, decoded]

theorem lowerExpression_local
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {type : Core.Ty} {reason : Core.Word} {expression : Core.Expr}
    (metadata : readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.local binder))
    (read : SourceCoreLocalCell.lowerRead source scope id reason = .ok expression) :
    lowerExpression (fuel + 1) source scope id reason = .ok ⟨type, expression⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, read, Except.mapError]

theorem lowerExpression_group
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id inner : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty} {reason : Core.Word} {expression : Core.Expr}
    (metadata : readExpression source id = .ok (node, type))
    (form : node.form = .group inner)
    (lowered : lowerExpression fuel source scope inner reason = .ok ⟨type, expression⟩) :
    lowerExpression (fuel + 1) source scope id reason = .ok ⟨type, expression⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, lowered, ensureType]

theorem lowerExpression_pair
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id leftId rightId : ExpressionId}
    {node : ExpressionNode} {leftType rightType : Core.Ty} {reason : Core.Word}
    {left right : Core.Expr}
    (metadata : readExpression source id = .ok (node, .product leftType rightType))
    (form : node.form = .tuple [leftId, rightId])
    (leftLowered : lowerExpression fuel source scope leftId reason = .ok ⟨leftType, left⟩)
    (rightLowered : lowerExpression fuel source scope rightId reason = .ok ⟨rightType, right⟩) :
    lowerExpression (fuel + 1) source scope id reason =
      .ok ⟨.product leftType rightType, Core.LocalSequence.pair leftType rightType left right⟩ := by
  simp [lowerExpression, bind, Except.bind, pure, Pure.pure, Except.pure,
    metadata, form, leftLowered, rightLowered, ensureType]

theorem lowerStatements_nil (fuel : Nat) (source : TypedSource) (scope : Scope) (reason : Core.Word) :
    lowerStatements fuel source scope [] .unit reason = .ok (Core.LanguageResult.success .unit) := by
  cases fuel <;> rfl

theorem lowerStatements_letUninitialized
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {binder : TypedBinder} {payloadType resultType : Core.Ty}
    {reason : Core.Word} {body : Core.Expr}
    (metadata : readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder none)
    (binding : lowerBinder source scope binder = .ok payloadType)
    (tail : lowerStatements fuel source ((binder.id, payloadType) :: scope) rest resultType reason = .ok body) :
    lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
      .ok (Core.LocalSequence.letUninitialized payloadType body) := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, binding, tail]

theorem lowerStatements_letInitialized
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {binder : TypedBinder} {payloadType resultType : Core.Ty}
    {initializer : ExpressionId} {reason : Core.Word} {value body : Core.Expr}
    (metadata : readStatement source id = .ok (node, .unit))
    (form : node.form = .letDecl binder (some initializer))
    (binding : lowerBinder source scope binder = .ok payloadType)
    (initialization : lowerExpression fuel source scope initializer reason = .ok ⟨payloadType, value⟩)
    (tail : lowerStatements fuel source ((binder.id, payloadType) :: scope) rest resultType reason = .ok body) :
    lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
      .ok (Core.LocalSequence.letInitialized resultType payloadType value body) := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, binding, initialization, tail]

theorem lowerStatements_assign
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {index : Nat}
    {payloadType resultType : Core.Ty} {rhs : ExpressionId} {reason : Core.Word} {value body : Core.Expr}
    (metadata : readStatement source id = .ok (node, .unit))
    (form : node.form = .assignValue assignment .equal rhs)
    (target : lowerAssignment source scope assignment .equal = .ok (index, payloadType))
    (rhsLowered : lowerExpression fuel source scope rhs reason = .ok ⟨payloadType, value⟩)
    (tail : lowerStatements fuel source scope rest resultType reason = .ok body) :
    lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
      .ok (Core.LocalSequence.assign resultType (.var index) value body) := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, target, rhsLowered, tail]

theorem lowerStatements_return
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {resultType : Core.Ty} {value : ExpressionId}
    {reason : Core.Word} {expression : Core.Expr}
    (metadata : readStatement source id = .ok (node, resultType))
    (form : node.form = .returnStmt (some value))
    (lowered : lowerExpression fuel source scope value reason = .ok ⟨resultType, expression⟩) :
    lowerStatements (fuel + 1) source scope (id :: rest) resultType reason = .ok expression := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, lowered]

theorem lowerStatements_returnUnit
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {reason : Core.Word}
    (metadata : readStatement source id = .ok (node, .unit))
    (form : node.form = .returnStmt none) :
    lowerStatements (fuel + 1) source scope (id :: rest) .unit reason =
      .ok (Core.LanguageResult.success .unit) := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType]

theorem lowerStatements_tail
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId}
    {node : StatementNode} {resultType : Core.Ty} {value : ExpressionId}
    {reason : Core.Word} {expression : Core.Expr}
    (metadata : readStatement source id = .ok (node, resultType))
    (form : node.form = .expression value false)
    (lowered : lowerExpression fuel source scope value reason = .ok ⟨resultType, expression⟩) :
    lowerStatements (fuel + 1) source scope [id] resultType reason = .ok expression := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, lowered]

theorem lowerStatements_discard
    {fuel : Nat} {source : TypedSource} {scope : Scope} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {valueType resultType : Core.Ty} {value : ExpressionId}
    {reason : Core.Word} {expression body : Core.Expr}
    (metadata : readStatement source id = .ok (node, .unit))
    (form : node.form = .expression value true)
    (lowered : lowerExpression fuel source scope value reason = .ok ⟨valueType, expression⟩)
    (tail : lowerStatements fuel source scope rest resultType reason = .ok body) :
    lowerStatements (fuel + 1) source scope (id :: rest) resultType reason =
      .ok (Core.LocalSequence.discard resultType expression body) := by
  simp [lowerStatements, bind, Except.bind, pure, Pure.pure, Except.pure, metadata, form, ensureType, lowered, tail]

end Solcore.Frontend.SourceCoreBasic
