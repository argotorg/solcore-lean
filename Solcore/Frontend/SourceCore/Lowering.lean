import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.Internal.ConventionLaws
import Solcore.Frontend.SourceCompilationPlan
import Solcore.SourceSemantics.CaptureBinders
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Panics

/-!
# Lowering of expressions and statements

Scalars, products, locals, control, loops, assignments, named calls and function values, all
compiled to ordinary Core. Main declarations: `SourceCoreLocalCell.Scope`,
`SourceCoreBasic.LoweredExpr`, `SourceCoreCalls.Signature`, `SourceCoreFunctions.Context`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreLocalCell
/-!
Executable lowering of monomorphic local reads to optional Core cells.

This is the local-reference boundary of the new runtime lowering path. Its
closed type profile is the existing unit/Bool/Word/product projection; other
source forms, generalized binders and coercions require their own lowering.
The reason word is supplied by the compiler's fault-site table.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLocalCell

open SourceInference

/-- Slots retain source identities and the payload type of each Core cell. -/
abbrev Scope := List (Resolved.LocalId × Core.Ty)

def lookup? : Scope → Resolved.LocalId → Option (Nat × Core.Ty)
  | [], _ => none
  | (other, type) :: rest, id =>
      if other = id then some (0, type)
      else (lookup? rest id).map fun (index, type) => (index + 1, type)

def coreContext (scope : Scope) : Core.Context :=
  scope.map fun entry => .cell (Core.OptionalCell.cellType entry.2)

inductive Error where
  | missingExpression (id : ExpressionId)
  | expectedLocalReference (id : ExpressionId)
  | ownerMismatch (id : Resolved.LocalId)
  | missingBinding (id : Resolved.LocalId)
  | requirementsPresent (id : ExpressionId)
  | coercionsPresent (id : ExpressionId)
  | typeProjection (error : SourceCoreElaboration.Error)
  | slotTypeMismatch (expected actual : Core.Ty)
  deriving Repr, DecidableEq

/-- Compile a local occurrence without reading or evaluating a source heap. -/
def lowerRead (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reason : Core.Word) : Except Error Core.Expr := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => .error (.missingExpression id)
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder
    | _ => .error (.expectedLocalReference id)
  if binder.owner != source.owner then
    throw (.ownerMismatch binder)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  let (index, payloadType) ← match lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← (SourceCoreElaboration.lowerType
    (.occurrence id.occurrence) node.type).mapError Error.typeProjection
  if projected ≠ payloadType then
    throw (.slotTypeMismatch projected payloadType)
  pure (Core.OptionalCell.read payloadType (.var index) reason)

/-- Exact metadata and a resolved slot suffice for actual lowering success. -/
theorem lowerRead_eq {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {binder : Resolved.LocalId}
    {name : String} {index : Nat} {payloadType : Core.Ty}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (owner : binder.owner = source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (slot : lookup? scope binder = some (index, payloadType))
    (projection : SourceCoreElaboration.lowerType
      (.occurrence id.occurrence) node.type = .ok payloadType)
    (reason : Core.Word) :
    lowerRead source scope id reason =
      .ok (Core.OptionalCell.read payloadType (.var index) reason) := by
  simp [lowerRead, found, form, owner, requirements, coercions, slot, projection,
    Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lookup?_context {scope : Scope} {id : Resolved.LocalId}
    {index : Nat} {payloadType : Core.Ty}
    (slot : lookup? scope id = some (index, payloadType)) :
    (coreContext scope)[index]? =
      some (.cell (Core.OptionalCell.cellType payloadType)) := by
  induction scope generalizing index with
  | nil => simp [lookup?] at slot
  | cons head tail inductionHypothesis =>
      rcases head with ⟨other, type⟩
      by_cases same : other = id
      · simp [lookup?, same] at slot
        rcases slot with ⟨rfl, rfl⟩
        rfl
      · simp only [lookup?, same, ↓reduceIte] at slot
        cases found : lookup? tail id with
        | none => simp [found] at slot
        | some pair =>
            rcases pair with ⟨previous, foundType⟩
            simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at slot
            rcases slot with ⟨rfl, rfl⟩
            exact inductionHypothesis found

end Solcore.Frontend.SourceCoreLocalCell
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreBasic
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
  | literalEvidence (error : SourceCoreElaboration.Error)
  | callPreparation (error : SourceTypedRuntime.RuntimeError)
  | typeMismatch (site : SourceCoreElaboration.ErrorSite) (expected actual : Core.Ty)
  | invalidWordLiteral (id : ExpressionId) (literal : Syntax.CoreLiteralValue)
  | localRead (error : SourceCoreLocalCell.Error)
  | unsupportedExpression (id : ExpressionId) (form : ExpressionForm)
  | unsupportedStatement (id : StatementId) (form : StatementForm)
  | unsupportedForItem (form : ForItemForm)
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
  | sourceAllocation (details : String)
  | callableMetadata (details : String)
  deriving Repr, DecidableEq

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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreControl
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreScalar
/-! The runtime scalar boundary extends the legacy staged carrier with native
Integer. Legacy elaboration and comptime evaluation retain their own projection.
Input conversion inspects complete product trees and never accepts closures or
references through their outer type alone. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreScalar

open SourceInference

def lowerType (site : SourceCoreElaboration.ErrorSite)
    (type : TypeSystem.Ty) : Except SourceCoreElaboration.Error Core.Ty :=
  match SourceCoreElaboration.lowerType site type with
  | .ok projected => .ok projected
  | .error error => match type with
    | .constructor (.builtin .integer) => .ok .integer
    | .product left right => do pure (.product (← lowerType site left) (← lowerType site right))
    | .comptime inner => lowerType site inner
    | _ => .error error

theorem lowerType_extends {site : SourceCoreElaboration.ErrorSite}
    {type : TypeSystem.Ty} {projected : Core.Ty}
    (legacy : SourceCoreElaboration.lowerType site type = .ok projected) :
    lowerType site type = .ok projected := by
  simp [lowerType, legacy]

def lowerBinder (source : TypedSource) (scope : SourceCoreBasic.Scope)
    (binder : TypedBinder) : Except SourceCoreBasic.Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  (lowerType (.binder binder.id) binder.scheme.body).mapError SourceCoreBasic.Error.typeProjection

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : Value)
  deriving Repr

def Value.toCore : Value → Core.Value
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .product left right => .pair left.toCore right.toCore

def Value.type : Value → Core.Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .integer _ => .integer
  | .product left right => .product left.type right.type

def Value.ofCore? : Core.Value → Option Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.product (← ofCore? left) (← ofCore? right))
  | _ => none

theorem Value.typed (value : Value) (world : Core.StoreTyping)
    (definitions : Core.DataEnvironment := []) :
    Core.RuntimeValueHasType world value.toCore value.type definitions := by
  induction value with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .pair left right

@[simp] theorem Value.ofCore?_toCore (value : Value) :
    Value.ofCore? value.toCore = some value := by
  induction value <;> simp_all [ofCore?, toCore]

theorem Value.ofCore?_reflect {core : Core.Value} {value : Value}
    (accepted : Value.ofCore? core = some value) : core = value.toCore := by
  cases core with
  | unit | bool | word | integer =>
      simp only [ofCore?, Option.some.injEq] at accepted
      subst value
      rfl
  | pair left right =>
      simp only [ofCore?, bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨leftValue, leftAccepted, rightValue, rightAccepted, equality⟩ := accepted
      cases Option.some.inj equality
      simp only [toCore]
      rw [ofCore?_reflect leftAccepted, ofCore?_reflect rightAccepted]
  | hostFunction | closure | inLeft | inRight | cellRef | constructed =>
      simp only [ofCore?, reduceCtorEq] at accepted
termination_by sizeOf core
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Solcore.Frontend.SourceCoreScalar
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAssignments
/-! Assignment policy for bare scalar/product equal assignments and builtin
Word/Integer compound/unary assignments. Requirements and projections are
rejected; method evidence remains separate lowering work. The caller
supplies each assignment's diagnostic reason and a lexical continuation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignments

open SourceInference

abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

/-- Close the expression reason provider before passing this policy. -/
abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId → Except Error LoweredExpr

def operator? : Syntax.ValueAssignOp → Option Core.LocalAssignment.Operator
  | .equal | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract
  | .uncheckedMultiply | .uncheckedDivide | .uncheckedModulo => none
  | .add => some .add
  | .subtract => some .subtract
  | .multiply => some .multiply
  | .divide => some .divide
  | .modulo => some .modulo
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor

/-- The Core operation of a Word-only compound assignment (a shift or the
arithmetic of an `unchecked` block), applied to the stored Word and the
right-hand side. -/
def wordOnly? : Syntax.ValueAssignOp → Option Core.BinaryOp
  | .shiftLeft => some .wordShl
  | .shiftRight => some .wordShr
  | .uncheckedAdd => some .wordAdd
  | .uncheckedSubtract => some .wordSub
  | .uncheckedMultiply => some .wordMul
  | .uncheckedDivide => some .wordDiv
  | .uncheckedModulo => some .wordMod
  | _ => none

/-- The write of a Word-only compound assignment, under the stored Word, the
right-hand side, the loaded cell and the reference. When the operator may
panic, a zero right-hand side fails with `Panic(0x12)` and writes nothing. -/
def wordOnlyWrite (outputType : Core.Ty) (operation : Core.BinaryOp) (panics : Bool)
    (next : Core.Expr) : Core.Expr :=
  let write := .letE (.storeCell (.var 3) (.inRight .unit (.binary operation (.var 0) (.var 1))))
    (Core.LocalAssignment.weakenFive next)
  if panics then
    .ifE (.binary .wordEq (.var 1) (.word Core.Word.zero))
      (Core.LanguageResult.failure outputType
        (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)))
      write
  else write

/-- `Core.LocalAssignment.compound` with any Core Word operation in place of
its arithmetic operator: the stored Word is read before the right-hand side is
evaluated, an uninitialized target fails with the assignment's reason, and a
panicking operator then checks its divisor. -/
def wordOnlyCompound (outputType : Core.Ty) (operation : Core.BinaryOp) (panics : Bool)
    (reference rhs next : Core.Expr) (invalidReason : Core.Word) : Core.Expr :=
  .letE reference (.letE (.loadCell (.var 0))
    (Core.LanguageResult.bind outputType (Core.LocalAssignment.weakenTwo rhs)
      (.caseE (.var 1) (Core.LanguageResult.failure outputType (.word invalidReason))
        (wordOnlyWrite outputType operation panics next))))

/-- Scalar target validation checks the owner, binding, declared payload type,
empty requirements and absence of projections. Equal function assignments
continue through the enclosing function profile's own callback. -/
def target (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution) :
    Except Error (Nat × Core.Ty) := do
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← (SourceCoreScalar.lowerType (.binder binder) assignment.target.type).mapError SourceCoreBasic.Error.typeProjection
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

private def integerOperator : Core.LocalAssignment.Operator → Core.IntegerAssignment.Operator
  | .add => .add
  | .subtract => .subtract
  | .multiply => .multiply
  | .divide => .divide
  | .modulo => .modulo
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor

def assignValue (lowerExpression : ExpressionLowerer) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (invalidReason : Core.Word) : Except Error Core.Expr := do
  let (index, payloadType) ← target source scope assignment
  match operator? operator, wordOnly? operator with
  | none, some operation =>
      SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
      let rhs ← lowerExpression fuel source scope rhs
      SourceCoreBasic.ensureType (.binder assignment.target.root) .word rhs.type
      pure (wordOnlyCompound outputType operation operator.mayPanic (.var index) rhs.expression
        next invalidReason)
  | none, none =>
      let rhs ← lowerExpression fuel source scope rhs
      SourceCoreBasic.ensureType (.binder assignment.target.root) payloadType rhs.type
      pure (Core.LocalSequence.assign outputType (.var index) rhs.expression next)
  | some operator, _ =>
      if payloadType = .integer then
        let rhs ← lowerExpression fuel source scope rhs
        SourceCoreBasic.ensureType (.binder assignment.target.root) .integer rhs.type
        pure (Core.IntegerAssignment.compound outputType (integerOperator operator) (.var index)
          rhs.expression next invalidReason)
      else
        SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
        let rhs ← lowerExpression fuel source scope rhs
        SourceCoreBasic.ensureType (.binder assignment.target.root) .word rhs.type
        pure (Core.LocalAssignment.compound outputType operator (.var index) rhs.expression next invalidReason)

def assignValueWithReasons (lowerExpression : SourceCoreControl.ExpressionLowerer) (fuel : Nat)
    (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (invalidReason : Core.Word) (reasonAt : ExpressionId → Core.Word) :
    Except Error Core.Expr :=
  assignValue (fun fuel source scope id => lowerExpression fuel source scope id reasonAt)
    fuel source scope assignment operator rhs outputType next invalidReason

def assignBitNot (source : TypedSource) (scope : Scope) (assignment : AssignmentResolution)
    (outputType : Core.Ty) (next : Core.Expr) (invalidReason : Core.Word) : Except Error Core.Expr := do
  let (index, payloadType) ← target source scope assignment
  if payloadType = .integer then
    pure (Core.IntegerAssignment.bitNot outputType (.var index) next invalidReason)
  else
    SourceCoreBasic.ensureType (.binder assignment.target.root) .word payloadType
    pure (Core.LocalAssignment.bitNot outputType (.var index) next invalidReason)

end Solcore.Frontend.SourceCoreAssignments
end

section
-- leanmerge: from Solcore.Frontend.SourceCorePrimitive
/-! Word/Bool primitive expressions over optional local cells. Integer literals
use the shared exact Word-evidence validator. Other primitive nodes retain the
empty requirement/coercion boundary; user methods and Integer-valued runtime
operations remain explicit rejections. No source evaluator is imported. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCorePrimitive

open SourceInference

abbrev Error := SourceCoreBasic.Error
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

/-- Supplied from the canonical specialized function at the entry boundary.
Literal lowering still authenticates the exact matching retained obligation. -/
structure Context where
  solvedRequirements : List SolvedRequirement
  deriving Repr

def unaryOperator : Syntax.UnaryOp → Core.UnaryOp
  | .logicalNot => .boolNot
  | .bitNot => .wordNot

def binaryOperandType : Syntax.BinaryOp → Core.Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .word

def binaryResultType : Syntax.BinaryOp → Core.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .shiftLeft | .shiftRight
  | .bitAnd | .bitXor | .bitOr | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .uncheckedDivide | .uncheckedModulo => .word
  | _ => .bool

/-- Comparisons swap already evaluated payloads, so operand side effects keep
their original order. Boolean short circuit is handled separately below. -/
def strictBinaryBody : Syntax.BinaryOp → Core.Expr
  | .multiply => .binary .wordMul (.var 1) (.var 0)
  | .divide => .binary .wordDiv (.var 1) (.var 0)
  | .modulo => .binary .wordMod (.var 1) (.var 0)
  | .add => .binary .wordAdd (.var 1) (.var 0)
  | .subtract => .binary .wordSub (.var 1) (.var 0)
  | .shiftLeft => .binary .wordShl (.var 1) (.var 0)
  | .shiftRight => .binary .wordShr (.var 1) (.var 0)
  | .uncheckedAdd => .binary .wordAdd (.var 1) (.var 0)
  | .uncheckedSubtract => .binary .wordSub (.var 1) (.var 0)
  | .uncheckedMultiply => .binary .wordMul (.var 1) (.var 0)
  | .uncheckedDivide => .binary .wordDiv (.var 1) (.var 0)
  | .uncheckedModulo => .binary .wordMod (.var 1) (.var 0)
  | .bitAnd => .binary .wordAnd (.var 1) (.var 0)
  | .bitXor => .binary .wordXor (.var 1) (.var 0)
  | .bitOr => .binary .wordOr (.var 1) (.var 0)
  | .greater => .binary .wordGt (.var 1) (.var 0)
  | .equal => .binary .wordEq (.var 1) (.var 0)
  | .less => .binary .wordGt (.var 0) (.var 1)
  | .lessEqual => .unary .boolNot (.binary .wordGt (.var 1) (.var 0))
  | .greaterEqual => .unary .boolNot (.binary .wordGt (.var 0) (.var 1))
  | .notEqual => .unary .boolNot (.binary .wordEq (.var 1) (.var 0))
  | .logicalAnd => .ifE (.var 1) (.var 0) (.bool false)
  | .logicalOr => .ifE (.var 1) (.bool true) (.var 0)

/-- The body of unchecked `/` and `%`, under the right payload, the left payload
and the outer scope: a zero divisor fails with `Panic(0x12)`, and any other
divisor gives the Word operation. -/
def panickingBody (operator : Syntax.BinaryOp) : Core.Expr :=
  .ifE (.binary .wordEq (.var 0) (.word Core.Word.zero))
    (Core.LanguageResult.failure .word
      (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)))
    (Core.LanguageResult.success (strictBinaryBody operator))

/-- `binaryWith` with a body that may fail. -/
def binaryPanicking (operator : Syntax.BinaryOp) (left right : Core.Expr) : Core.Expr :=
  Core.LanguageResult.bind .word left
    (Core.LanguageResult.bind .word (right.weakenAt 0) (panickingBody operator))

def binary (operator : Syntax.BinaryOp) (left right : Core.Expr) : Core.Expr :=
  match operator with
  | .logicalAnd => Core.LocalPrimitiveResults.logicalAnd left right
  | .logicalOr => Core.LocalPrimitiveResults.logicalOr left right
  | .uncheckedDivide | .uncheckedModulo => binaryPanicking operator left right
  | _ => Core.LocalPrimitiveResults.binaryWith (binaryResultType operator) left right
      (strictBinaryBody operator)

theorem strictBinaryBody_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    (operator : Syntax.BinaryOp) :
    Core.HasType (binaryOperandType operator :: binaryOperandType operator :: scope)
      (strictBinaryBody operator) (binaryResultType operator) definitions := by
  cases operator <;> first
    | exact .binary (.var rfl) (.var rfl)
    | exact .unary (.binary (.var rfl) (.var rfl))
    | exact .ifE (.var rfl) (.var rfl) .bool
    | exact .ifE (.var rfl) .bool (.var rfl)

theorem panickingBody_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    {operator : Syntax.BinaryOp} (word : binaryResultType operator = .word)
    (operand : binaryOperandType operator = .word) :
    Core.HasType (.word :: .word :: scope) (panickingBody operator)
      (Core.LanguageResult.resultType .word) definitions := by
  have body := strictBinaryBody_hasType (definitions := definitions) (scope := scope) operator
  rw [word, operand] at body
  exact .ifE (.binary (.var rfl) .word)
    (Core.LanguageResult.failure_hasType .word .word) (Core.LanguageResult.success_hasType body)

theorem binaryPanicking_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    {operator : Syntax.BinaryOp} {left right : Core.Expr}
    (leftTyped : Core.HasType scope left (Core.LanguageResult.resultType (binaryOperandType operator)) definitions)
    (rightTyped : Core.HasType scope right (Core.LanguageResult.resultType (binaryOperandType operator)) definitions)
    (word : binaryResultType operator = .word) (operand : binaryOperandType operator = .word) :
    Core.HasType scope (binaryPanicking operator left right)
      (Core.LanguageResult.resultType (binaryResultType operator)) definitions := by
  rw [operand] at leftTyped rightTyped
  rw [word]
  apply Core.LanguageResult.bind_hasType .word leftTyped
  apply Core.LanguageResult.bind_hasType .word
  · simpa [Core.Context.insertAt] using rightTyped.weakenAt (inserted := .word) 0
  · exact panickingBody_hasType word operand

/-- A nonzero divisor gives the Word operation. -/
theorem binaryPanicking_success {environment : Core.Environment}
    {before middle after : Core.Store} {operator : Syntax.BinaryOp} {left right : Core.Expr}
    {leftValue rightValue : Core.Word} {result : Core.Value}
    (leftEvaluation : Core.Evaluates environment before left (.inRight .word (.word leftValue)) middle)
    (rightEvaluation : Core.Evaluates (.word leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word (.word rightValue)) after)
    (nonzero : rightValue ≠ Core.Word.zero)
    (bodyEvaluation : ∀ store, Core.Evaluates (.word rightValue :: .word leftValue :: environment) store
      (strictBinaryBody operator) result store) :
    Core.Evaluates environment before (binaryPanicking operator left right) (.inRight .word result) after :=
  Core.LanguageResult.bind_success _ leftEvaluation
    (Core.LanguageResult.bind_success _ rightEvaluation
      (.ifFalse (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply, nonzero]))
        (.inRight (bodyEvaluation after))))

/-- A zero divisor fails with `Panic(0x12)`. -/
theorem binaryPanicking_panic {environment : Core.Environment}
    {before middle after : Core.Store} {operator : Syntax.BinaryOp} {left right : Core.Expr}
    {leftValue : Core.Value}
    (leftEvaluation : Core.Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Core.Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word (.word Core.Word.zero)) after) :
    Core.Evaluates environment before (binaryPanicking operator left right)
      (.inLeft .word (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero))) after :=
  Core.LanguageResult.bind_success _ leftEvaluation
    (Core.LanguageResult.bind_success _ rightEvaluation
      (.ifTrue (.binary (.var rfl) .word (by simp [Core.BinaryOp.apply]))
        (.inLeft .word)))

/-- The divisor check under the right and left Word payloads either panics on
a zero divisor or continues with the body. -/
theorem panickingBody_inv {environment : Core.Environment} {before after : Core.Store}
    {operator : Syntax.BinaryOp} {left right : Core.Word} {value : Core.Value}
    (evaluated : Core.Evaluates (.word right :: .word left :: environment) before
      (panickingBody operator) value after) :
    (right = Core.Word.zero ∧
      value = .inLeft .word (.word (SourceCorePanics.reason SourceCorePanics.divisionByZero)) ∧
      after = before) ∨
    (right ≠ Core.Word.zero ∧ Core.Evaluates (.word right :: .word left :: environment) before
      (Core.LanguageResult.success (strictBinaryBody operator)) value after) := by
  unfold panickingBody at evaluated
  cases evaluated with
  | ifTrue condition branch =>
    cases condition with
    | binary leftEvaluation zeroEvaluation applied =>
      cases leftEvaluation with
      | var found =>
        cases zeroEvaluation
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        simp only [Core.BinaryOp.apply, Option.some.injEq, Core.Value.bool.injEq, beq_iff_eq] at applied
        cases branch with
        | inLeft reason => cases reason; exact .inl ⟨applied, rfl, rfl⟩
  | ifFalse condition branch =>
    cases condition with
    | binary leftEvaluation zeroEvaluation applied =>
      cases leftEvaluation with
      | var found =>
        cases zeroEvaluation
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        simp only [Core.BinaryOp.apply, Option.some.injEq, Core.Value.bool.injEq, beq_eq_false_iff_ne] at applied
        exact .inr ⟨applied, branch⟩

theorem binaryPanicking_left_failure {environment : Core.Environment}
    {before after : Core.Store} {operator : Syntax.BinaryOp} {left right : Core.Expr} {reason : Core.Word}
    (evaluation : Core.Evaluates environment before left (.inLeft .word (.word reason)) after) :
    Core.Evaluates environment before (binaryPanicking operator left right)
      (.inLeft .word (.word reason)) after :=
  Core.LanguageResult.bind_failure _ evaluation

theorem binaryPanicking_right_failure {environment : Core.Environment}
    {before middle after : Core.Store} {operator : Syntax.BinaryOp} {left right : Core.Expr}
    {leftValue : Core.Value} {reason : Core.Word}
    (leftEvaluation : Core.Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Core.Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inLeft .word (.word reason)) after) :
    Core.Evaluates environment before (binaryPanicking operator left right)
      (.inLeft .word (.word reason)) after :=
  Core.LanguageResult.bind_success _ leftEvaluation (Core.LanguageResult.bind_failure _ rightEvaluation)

theorem binary_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    {operator : Syntax.BinaryOp} {left right : Core.Expr}
    (leftTyped : Core.HasType scope left (Core.LanguageResult.resultType (binaryOperandType operator)) definitions)
    (rightTyped : Core.HasType scope right (Core.LanguageResult.resultType (binaryOperandType operator)) definitions) :
    Core.HasType scope (binary operator left right)
      (Core.LanguageResult.resultType (binaryResultType operator)) definitions := by
  cases operator <;> first
    | exact Core.LocalPrimitiveResults.logicalAnd_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.logicalOr_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.binaryWith_hasType (by constructor) leftTyped rightTyped
        (strictBinaryBody_hasType _)
    | exact binaryPanicking_hasType leftTyped rightTyped rfl rfl

/-- Conditional/group/tuple children use this same policy recursively, so an
operator can occur at any expression position without losing read reasons. -/
def lowerExpressionWithReasons : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then
        throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      match node.form with
      | .integerLiteral literal resolution =>
          let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
            node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
          pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← SourceCoreBasic.readExpression source id
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .unary operator operand =>
              let operand ← lowerExpressionWithReasons fuel context source scope operand reasonAt
              let coreOperator := unaryOperator operator
              SourceCoreBasic.ensureType site coreOperator.operandType operand.type
              SourceCoreBasic.ensureType site coreOperator.resultType type
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              -- This profile's certificate has no panic, so unchecked `/` and `%` stay unsupported.
              if operator.mayPanic then throw (.unsupportedExpression id node.form) else
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site (binaryOperandType operator) left.type
              SourceCoreBasic.ensureType site (binaryOperandType operator) right.type
              SourceCoreBasic.ensureType site (binaryResultType operator) type
              pure ⟨type, binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithReasons fuel context source scope condition reasonAt
              SourceCoreBasic.ensureType site .bool condition.type
              let thenBranch ← lowerExpressionWithReasons fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithReasons fuel context source scope elseBranch reasonAt
              SourceCoreBasic.ensureType site type thenBranch.type
              SourceCoreBasic.ensureType site type elseBranch.type
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithReasons fuel context source scope inner reasonAt
              SourceCoreBasic.ensureType site type inner.type
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site type (.product left.type right.type)
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ => SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id)

def lowerExpression (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reason : Core.Word) : Except Error LoweredExpr :=
  lowerExpressionWithReasons fuel context source scope id (fun _ => reason)

end Solcore.Frontend.SourceCorePrimitive
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCalls
/-! Monomorphic named calls through ordinary optional Core function cells.
Arguments run in source order before the selected cell is read. Global cells
are supplied by the enclosing program installation, after local references and
any administrative binders. The prepared plan authenticates occurrence edges;
this fragment does not execute source code or lower evidence-bearing methods. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCalls

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Scope := SourceCoreBasic.Scope
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr

structure Signature where
  key : Key
  parameterType : Core.Ty
  resultType : Core.Ty
  deriving Repr, DecidableEq

structure Context where
  plan : Plan
  owner : Key
  /-- Newest-first, in the same order as the enclosing Core environment. -/
  globals : List Signature
  administrativePrefix : Nat
  solvedRequirements : List SolvedRequirement
  internalReason : Core.Word
  deriving Repr

abbrev Error := SourceCoreBasic.Error

/-- A function returns a language result, including on a recursive call. -/
def Signature.functionType (signature : Signature) : Core.Ty :=
  .function signature.parameterType (Core.LanguageResult.resultType signature.resultType)

def Signature.referenceType (signature : Signature) : Core.Ty :=
  Core.OptionalCell.referenceType signature.functionType

/-- Source argument packing: no arguments form Unit; one is unchanged;
multiple arguments form a right-associated product, with left-to-right effects. -/
def packArguments : List LoweredExpr → LoweredExpr
  | [] => ⟨.unit, Core.LanguageResult.success .unit⟩
  | [argument] => argument
  | argument :: rest =>
      let tail := packArguments rest
      ⟨.product argument.type tail.type,
        Core.LocalSequence.pair argument.type tail.type argument.expression tail.expression⟩

/-- Read the global cell only after the argument bundle succeeds. The argument
and function payload binders are private to this expression. -/
def call (signature : Signature) (index : Nat) (arguments : Core.Expr)
    (internalReason : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind signature.resultType arguments
    (Core.LanguageResult.bind signature.resultType
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.apply (.var 0) (.var 1)))

theorem call_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    (internalReason : Core.Word)
    (parameterWF : Core.Ty.WellFormed definitions signature.parameterType)
    (resultWF : Core.Ty.WellFormed definitions signature.resultType)
    (reference : environment[index]? = some signature.referenceType)
    (argumentsTyped : Core.HasType environment arguments
      (Core.LanguageResult.resultType signature.parameterType) definitions) :
    Core.HasType environment (call signature index arguments internalReason)
      (Core.LanguageResult.resultType signature.resultType) definitions := by
  apply Core.LanguageResult.bind_hasType resultWF argumentsTyped
  apply Core.LanguageResult.bind_hasType resultWF
  · apply Core.OptionalCell.read_hasType internalReason
      (.function parameterWF (Core.LanguageResult.resultType_wellFormed resultWF))
    exact .var (by simpa [Signature.referenceType, Signature.functionType] using reference)
  · exact .apply (.var rfl) (.var rfl)

theorem call_argument_failure {environment : Core.Environment} {before after : Core.Store}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    {reason internalReason : Core.Word}
    (evaluation : Core.Evaluates environment before arguments
      (.inLeft signature.parameterType (.word reason)) after) :
    Core.Evaluates environment before (call signature index arguments internalReason)
      (.inLeft signature.resultType (.word reason)) after :=
  Core.LanguageResult.bind_failure signature.resultType evaluation

theorem call_global_failure {environment : Core.Environment} {before middle after : Core.Store}
    {signature : Signature} {index : Nat} {arguments : Core.Expr}
    {argument : Core.Value} {reason internalReason : Core.Word}
    (argumentsEvaluation : Core.Evaluates environment before arguments
      (.inRight .word argument) middle)
    (globalEvaluation : Core.Evaluates (argument :: environment) middle
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.inLeft signature.functionType (.word reason)) after) :
    Core.Evaluates environment before (call signature index arguments internalReason)
      (.inLeft signature.resultType (.word reason)) after :=
  Core.LanguageResult.bind_success signature.resultType argumentsEvaluation
    (Core.LanguageResult.bind_failure signature.resultType globalEvaluation)

theorem call_success {environment captured : Core.Environment}
    {before middle applied after : Core.Store}
    {signature : Signature} {index : Nat} {arguments body : Core.Expr}
    {argument result : Core.Value} {internalReason : Core.Word}
    (argumentsEvaluation : Core.Evaluates environment before arguments
      (.inRight .word argument) middle)
    (globalEvaluation : Core.Evaluates (argument :: environment) middle
      (Core.OptionalCell.read signature.functionType (.var (index + 1)) internalReason)
      (.inRight .word (.closure signature.parameterType
        (Core.LanguageResult.resultType signature.resultType) body captured)) applied)
    (bodyEvaluation : Core.Evaluates (argument :: captured) applied body result after) :
    Core.Evaluates environment before (call signature index arguments internalReason) result after :=
  Core.LanguageResult.bind_success signature.resultType argumentsEvaluation
    (Core.LanguageResult.bind_success signature.resultType globalEvaluation
      (.apply (.var rfl) (.var rfl) bodyEvaluation))

private def globalAt (globals : List Signature) (key : Key) :
    Except Error (Nat × Signature) :=
  match globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
  | [] => .error (.callPreparation (.missingSpecialization key))
  | [(signature, index)] => .ok (index, signature)
  | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))

/-- Validate a direct edge and its projected signature before compiling its
arguments. No assumption dictionary or staged result is implemented here. -/
def directSignature (context : Context) (source : TypedSource)
    (node : ExpressionNode) (callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) : Except Error (Nat × Signature) := do
  if source.owner ≠ context.owner.declaration then
    throw (.ownerMismatch context.owner.declaration source.owner)
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner).mapError SourceCoreBasic.Error.callPreparation
  unless caller.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions context.owner caller.assumptions))
  if callee.occurrence.owner ≠ source.owner then
    throw (.ownerMismatch source.owner callee.occurrence.owner)
  let calleeNode ← (SourceCompilationPlan.exactExpression source callee).mapError SourceCoreBasic.Error.callPreparation
  unless calleeNode.requirements.isEmpty do throw (.requirementsPresent callee)
  unless calleeNode.coercions.isEmpty do throw (.coercionsPresent callee)
  (SourceCompilationPlan.validateDirectDeclarationCallee source node.id callee instantiation).mapError SourceCoreBasic.Error.callPreparation
  let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
  let key ← (SourceCompilationPlan.exactCallKey context.plan context.owner node.id target).mapError SourceCoreBasic.Error.callPreparation
  let specialized ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  unless specialized.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions key specialized.assumptions))
  if specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime) then
    throw (.unsupportedExpression node.id node.form)
  if arguments.length ≠ specialized.function.typedBody.inputs.length then
    throw (.callPreparation (.argumentArityMismatch specialized.function.typedBody.inputs.length arguments.length))
  let (parameter, result) ← match specialized.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.callPreparation (.invalidFunctionType key specialized.function.type))
  let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  let parameterType ← (SourceCoreBasic.projectType site parameter)
  let resultType ← (SourceCoreBasic.projectType site result)
  let (index, signature) ← globalAt context.globals key
  (SourceCoreBasic.ensureType site parameterType signature.parameterType)
  (SourceCoreBasic.ensureType site resultType signature.resultType)
  pure (index, signature)

/-- The same policy recurses into every supported composite expression, so
calls retain primitive short circuit and local-read diagnostic providers. -/
def lowerExpressionWithReasons : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then
        throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      match node.form with
      | .integerLiteral literal resolution =>
          let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
            node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
          pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← (SourceCoreBasic.readExpression source id)
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .call callee arguments (.declaration instantiation) =>
              let (globalIndex, signature) ← directSignature context source node callee arguments instantiation
              (SourceCoreBasic.ensureType site signature.resultType type)
              let arguments ← arguments.mapM fun argument =>
                lowerExpressionWithReasons fuel context source scope argument reasonAt
              let packed := packArguments arguments
              (SourceCoreBasic.ensureType site signature.parameterType packed.type)
              pure ⟨type, call signature (scope.length + context.administrativePrefix + globalIndex)
                packed.expression context.internalReason⟩
          | .unary operator operand =>
              let operand ← lowerExpressionWithReasons fuel context source scope operand reasonAt
              let coreOperator := SourceCorePrimitive.unaryOperator operator
              (SourceCoreBasic.ensureType site coreOperator.operandType operand.type)
              (SourceCoreBasic.ensureType site coreOperator.resultType type)
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) left.type)
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) right.type)
              (SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryResultType operator) type)
              pure ⟨type, SourceCorePrimitive.binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithReasons fuel context source scope condition reasonAt
              (SourceCoreBasic.ensureType site .bool condition.type)
              let thenBranch ← lowerExpressionWithReasons fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithReasons fuel context source scope elseBranch reasonAt
              (SourceCoreBasic.ensureType site type thenBranch.type)
              (SourceCoreBasic.ensureType site type elseBranch.type)
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithReasons fuel context source scope inner reasonAt
              (SourceCoreBasic.ensureType site type inner.type)
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithReasons fuel context source scope left reasonAt
              let right ← lowerExpressionWithReasons fuel context source scope right reasonAt
              (SourceCoreBasic.ensureType site type (.product left.type right.type))
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ => (SourceCoreBasic.lowerExpression (fuel + 1) source scope id (reasonAt id))

end Solcore.Frontend.SourceCoreCalls
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreFunctionTypes
/-! The monomorphic function-value profile. Source functions become tagged
ordinary Core closures returning language results. This extends the structural
Unit/Bool/Word/product projection without changing the legacy scalar bridge.
Native Integer is included. Nominal, mapping and polymorphic representations
remain separate compiler profiles. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFunctionTypes

open SourceInference

abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error

def lowerType (site : SourceCoreElaboration.ErrorSite) : TypeSystem.Ty → Except SourceCoreElaboration.Error Core.Ty
  | .product left right => do
      pure (.product (← lowerType site left) (← lowerType site right))
  | .function parameter result => do
      pure (Core.TaggedFunction.functionType (← lowerType site parameter) (← lowerType site result))
  | type => SourceCoreScalar.lowerType site type

def projectType (site : SourceCoreElaboration.ErrorSite) (type : TypeSystem.Ty) : Except Error Core.Ty :=
  (lowerType site type).mapError SourceCoreBasic.Error.typeProjection

def readExpression (source : TypedSource) (id : ExpressionId) : Except Error (ExpressionNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => .error (.missingExpression id)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  let type ← projectType (.occurrence id.occurrence) node.type
  pure (node, type)

def readStatement (source : TypedSource) (id : StatementId) : Except Error (StatementNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupStatement? id with
    | some node => pure node
    | none => .error (.missingStatement id)
  let type ← projectType (.occurrence id.occurrence) node.type
  pure (node, type)

def lowerBinder (source : TypedSource) (scope : Scope) (binder : TypedBinder) : Except Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  projectType (.binder binder.id) binder.scheme.body

def lowerAssignment (source : TypedSource) (scope : Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) : Except Error (Nat × Core.Ty) := do
  if operator ≠ .equal then throw (.unsupportedAssignmentOperator operator)
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← projectType (.binder binder) assignment.target.type
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

def lowerRead (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reason : Core.Word) : Except Error Core.Expr := do
  let (node, type) ← readExpression source id
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder
    | _ => .error (.unsupportedExpression id node.form)
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  let (index, payloadType) ← match SourceCoreLocalCell.lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  SourceCoreBasic.ensureType (.occurrence id.occurrence) type payloadType
  pure (Core.OptionalCell.read payloadType (.var index) reason)

theorem lowerType_product {site : SourceCoreElaboration.ErrorSite}
    {left right : TypeSystem.Ty} {leftCore rightCore : Core.Ty}
    (leftLowered : lowerType site left = .ok leftCore)
    (rightLowered : lowerType site right = .ok rightCore) :
    lowerType site (.product left right) = .ok (.product leftCore rightCore) := by
  simp [lowerType, leftLowered, rightLowered, bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lowerType_function {site : SourceCoreElaboration.ErrorSite}
    {parameter result : TypeSystem.Ty} {parameterCore resultCore : Core.Ty}
    (parameterLowered : lowerType site parameter = .ok parameterCore)
    (resultLowered : lowerType site result = .ok resultCore) :
    lowerType site (.function parameter result) = .ok (Core.TaggedFunction.functionType parameterCore resultCore) := by
  simp [lowerType, parameterLowered, resultLowered, bind, Except.bind, pure, Pure.pure, Except.pure]

end Solcore.Frontend.SourceCoreFunctionTypes
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreInteger
/-! Native Integer expressions and monomorphic builtin closures are ordinary
Core code. Arithmetic preserves source operand order; reversed comparisons
swap the already evaluated payloads. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreInteger

def binaryResultType : Syntax.BinaryOp → Core.Ty
  | .multiply | .divide | .modulo | .add | .subtract | .bitAnd | .bitXor | .bitOr => .integer
  | _ => .bool

def strictBinaryBody : Syntax.BinaryOp → Core.Expr
  | .multiply => .binary .integerMul (.var 1) (.var 0)
  | .divide => .binary .integerDiv (.var 1) (.var 0)
  | .modulo => .binary .integerMod (.var 1) (.var 0)
  | .add => .binary .integerAdd (.var 1) (.var 0)
  | .subtract => .binary .integerSub (.var 1) (.var 0)
  | .bitAnd => .binary .integerAnd (.var 1) (.var 0)
  | .bitXor => .binary .integerXor (.var 1) (.var 0)
  | .bitOr => .binary .integerOr (.var 1) (.var 0)
  | .less => .binary .integerLt (.var 1) (.var 0)
  | .equal => .binary .integerEq (.var 1) (.var 0)
  | .greater => .binary .integerLt (.var 0) (.var 1)
  | .greaterEqual => .unary .boolNot (.binary .integerLt (.var 1) (.var 0))
  | .lessEqual => .unary .boolNot (.binary .integerLt (.var 0) (.var 1))
  | .notEqual => .unary .boolNot (.binary .integerEq (.var 1) (.var 0))
  | .logicalAnd => .ifE (.var 1) (.var 0) (.bool false)
  | .logicalOr => .ifE (.var 1) (.bool true) (.var 0)
  -- Shifts and unchecked arithmetic take Words only; typing never lowers one
  -- at Integer.
  | .shiftLeft | .shiftRight | .uncheckedAdd | .uncheckedSubtract | .uncheckedMultiply
  | .uncheckedDivide | .uncheckedModulo => .bool false

def binaryOperandType : Syntax.BinaryOp → Core.Ty
  | .logicalAnd | .logicalOr => .bool
  | _ => .integer

def binary (operator : Syntax.BinaryOp) (left right : Core.Expr) : Core.Expr :=
  match operator with
  | .logicalAnd => Core.LocalPrimitiveResults.logicalAnd left right
  | .logicalOr => Core.LocalPrimitiveResults.logicalOr left right
  | _ => Core.LocalPrimitiveResults.binaryWith (binaryResultType operator) left right
      (strictBinaryBody operator)

theorem strictBinaryBody_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    (operator : Syntax.BinaryOp) :
    Core.HasType (binaryOperandType operator :: binaryOperandType operator :: scope)
      (strictBinaryBody operator) (binaryResultType operator) definitions := by
  cases operator <;> first
    | exact .binary (.var rfl) (.var rfl)
    | exact .unary (.binary (.var rfl) (.var rfl))
    | exact .ifE (.var rfl) (.var rfl) .bool
    | exact .ifE (.var rfl) .bool (.var rfl)
    | exact .bool

theorem binary_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    {operator : Syntax.BinaryOp} {left right : Core.Expr}
    (leftTyped : Core.HasType scope left (Core.LanguageResult.resultType (binaryOperandType operator)) definitions)
    (rightTyped : Core.HasType scope right (Core.LanguageResult.resultType (binaryOperandType operator)) definitions) :
    Core.HasType scope (binary operator left right)
      (Core.LanguageResult.resultType (binaryResultType operator)) definitions := by
  cases operator <;> first
    | exact Core.LocalPrimitiveResults.logicalAnd_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.logicalOr_hasType leftTyped rightTyped
    | exact Core.LocalPrimitiveResults.binaryWith_hasType (by constructor) leftTyped rightTyped
        (strictBinaryBody_hasType _)

def builtinParameter : BuiltinFunctionId → Core.Ty
  | .wordToInteger => .word
  | .wordFromInteger => .integer
  | _ => .product .integer .integer

def builtinResult : BuiltinFunctionId → Core.Ty
  | .wordFromInteger => .word
  | .integerEq | .integerLt => .bool
  | _ => .integer

def builtinBody : BuiltinFunctionId → Core.Expr
  | .integerSub => .binary .integerSub (.first (.var 0)) (.second (.var 0))
  | .integerAdd => .binary .integerAdd (.first (.var 0)) (.second (.var 0))
  | .integerMul => .binary .integerMul (.first (.var 0)) (.second (.var 0))
  | .integerEq => .binary .integerEq (.first (.var 0)) (.second (.var 0))
  | .integerLt => .binary .integerLt (.first (.var 0)) (.second (.var 0))
  | .wordFromInteger => .unary .integerToWord (.var 0)
  | .wordToInteger => .unary .wordToInteger (.var 0)

def builtinClosure (function : BuiltinFunctionId) : Core.Expr :=
  .lambda (builtinParameter function) (Core.LanguageResult.resultType (builtinResult function))
    (Core.LanguageResult.success (builtinBody function))

theorem builtinClosure_hasType {definitions : Core.DataEnvironment} {scope : Core.Context}
    (function : BuiltinFunctionId) : Core.HasType scope (builtinClosure function)
      (.function (builtinParameter function) (Core.LanguageResult.resultType (builtinResult function))) definitions := by
  cases function <;>
    apply Core.HasType.lambda (by repeat constructor) (by repeat constructor) <;>
      apply Core.LanguageResult.success_hasType <;> first
        | exact .binary (.first (.var rfl)) (.second (.var rfl))
        | exact .unary (.var rfl)

end Solcore.Frontend.SourceCoreInteger
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreSourceCells
/-! Source-visible allocations share the ordinary expression/statement
traversal. The allocator receives the actual embedding of lexical references,
including argument-bundle and temporary result binders. It returns only an
optional payload reference; any marker bindings stay inside its expression.
The enclosing prepared entry still checks the entire emitted Core body. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreSourceCells
open SourceInference Core
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error

structure Request where
  source : TypedSource
  scope : Scope
  references : Renaming
  binder : TypedBinder
  payloadType : Core.Ty
  /-- An initialized payload expression, already inside the success branch.
  Allocation must evaluate it before creating any source cell. -/
  payload : Option Core.Expr

abbrev Allocator := Request → Except Error Core.Expr

def letUninitialized (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (references : Renaming) (binder : TypedBinder)
    (payloadType : Core.Ty) (body : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (LocalSequence.letUninitialized payloadType body)
  | some allocate =>
      pure (.letE (← allocate ⟨source, scope, references, binder, payloadType, none⟩) body)

def letInitialized (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (references : Renaming) (binder : TypedBinder)
    (outputType payloadType : Core.Ty) (initializer body : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (LocalSequence.letInitialized outputType payloadType initializer body)
  | some allocate =>
      let allocation ← allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references,
        binder, payloadType, some (.var 0)⟩
      pure (LanguageResult.bind outputType initializer (.letE allocation (body.weakenAt 1)))

/-- Capture only lexical references, in source environment order. The argument
bundle and other administrative binders are skipped by `references`. -/
def captureType : Scope → Core.Ty
  | [] => .unit
  | [(_, type)] => OptionalCell.referenceType type
  | (_, type) :: next :: rest =>
      .product (OptionalCell.referenceType type) (captureType (next :: rest))

def captures (references : Renaming) : Scope → Core.Expr
  | [] => .unit
  | [_] => .var (references 0)
  | _ :: next :: rest => .pair (.var (references 0))
      (captures (fun index => references (index + 1)) (next :: rest))

theorem captures_hasType {definitions : DataEnvironment} {context : Core.Context}
    (scope : Scope) (references : Renaming)
    (slots : ∀ index binding, scope[index]? = some binding →
      context[references index]? = some (OptionalCell.referenceType binding.2)) :
    HasType context (captures references scope) (captureType scope) definitions := by
  induction scope generalizing references with
  | nil => exact .unit
  | cons head rest ih =>
      cases rest with
      | nil => exact .var (slots 0 head rfl)
      | cons next tail =>
          apply HasType.pair (.var (slots 0 head rfl))
          apply ih (fun index => references (index + 1))
          intro index binding found
          exact slots (index + 1) binding (by simpa using found)

/-- The profile authenticates the layout and original binder metadata. Marker
payloads contain source references selected at this exact allocation site. -/
def marked (layoutAt : Request → Except Error SourceCoreHeapMarkers.Layout) : Allocator := fun request => do
  let layout ← layoutAt request
  unless layout.captureType = captureType request.scope do
    throw (.typeMismatch (.binder request.binder.id) (captureType request.scope) layout.captureType)
  let captured := captures request.references request.scope
  pure (match request.payload with
    | none => SourceCoreHeapMarkers.allocate layout request.payloadType captured
    | some value => SourceCoreHeapMarkers.allocateInitialized layout request.payloadType captured value)

/-! ## Captures by value

A lambda copies the captured cells when it is created and again at each call.
`SourceSemantics.CaptureBinders.copiedBinder?` selects the copied slots, as it
selects the copied bindings in the source semantics: a slot is copied when its
identifier has a single monomorphic declaration. A hidden match scrutinee has
no declaration, and a generalized local's cell holds an immutable principal,
so both keep their cells. -/

open SourceSemantics.CaptureBinders (copiedBinder?)

/-- The copied slots of a scope, in scope order, with their scope index,
declaration and payload type. -/
def copiedSlots (source : TypedSource) (scope : Scope) : List (Nat × TypedBinder × Core.Ty) :=
  scope.zipIdx.filterMap fun ((id, type), index) =>
    (copiedBinder? source id).map fun binder => (index, binder, type)

/-- Copy the optional cell at `reference` into a fresh cell for `binder`. An
uninitialized cell stays uninitialized. Marked copies allocate in both branches
of the payload test, below the branch's payload binder. -/
def copyCell (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (references : Renaming) (binder : TypedBinder) (payloadType : Core.Ty)
    (reference : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (.newCell (OptionalCell.cellType payloadType) (.loadCell reference))
  | some allocate =>
      let shifted := Renaming.comp (Renaming.insertion 0) references
      let absent ← allocate ⟨source, scope, shifted, binder, payloadType, none⟩
      let present ← allocate ⟨source, scope, shifted, binder, payloadType, some (.var 0)⟩
      pure (.caseE (.loadCell reference) absent present)

/-- After `count` copies of the slots at `positions` (in copy order), the
copy of the `ordinal`-th one is at `count - 1 - ordinal`; every other index
moves past the copies. -/
def copyRenaming (positions : List Nat) : Renaming := fun index =>
  match positions.findIdx? (fun position => decide (position = index)) with
  | some ordinal => positions.length - 1 - ordinal
  | none => index + positions.length

/-- References of one copy. A named input's own allocation counts the
packed-argument slot inside its references, so a copy of an input does too;
every index above the scope then keeps its administrative meaning. -/
def copyReferences (source : TypedSource) (scope : Scope) (binder : TypedBinder)
    (base : Nat → Nat) (ordinal : Nat) : Renaming := fun index =>
  if index < scope.length then base index + ordinal
  else if source.inputs.any (fun input => decide (input.id = binder.id)) then base (index + 1) + ordinal
  else base index + ordinal

/-- Copy the remaining slots `rest` of `scope`, the first of them at scope
index `index`, after `ordinal` earlier copies; then run `body`. `base` gives
each scope slot's index before the first copy. -/
def copyChain (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (base : Nat → Nat) : Scope → Nat → Nat → Core.Expr → Except Error Core.Expr
  | [], _, _, body => pure body
  | (id, type) :: rest, index, ordinal, body =>
      match copiedBinder? source id with
      | none => copyChain allocator source scope base rest (index + 1) ordinal body
      | some binder => do
          let copy ← copyCell allocator source scope (copyReferences source scope binder base ordinal)
            binder type (.var (base index + ordinal))
          let continuation ← copyChain allocator source scope base rest (index + 1) (ordinal + 1) body
          pure (.letE copy continuation)

/-- The renaming that redirects each copied slot of `scope` to its copy. -/
def scopeCopyRenaming (source : TypedSource) (scope : Scope) (base : Nat → Nat) : Renaming :=
  copyRenaming ((copiedSlots source scope).map fun slot => base slot.1)

/-- Copy the slots of `scope` that a closure copies, head first, then run
`body` with each copied slot redirected to its copy. -/
def copyScope (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (base : Nat → Nat) (body : Core.Expr) : Except Error Core.Expr :=
  copyChain allocator source scope base scope 0 0 (body.rename (scopeCopyRenaming source scope base))

/-- `copyChain` without an allocator: each copy is a plain cell. -/
def copyChainPlain (source : TypedSource) (base : Nat → Nat) :
    Scope → Nat → Nat → Core.Expr → Core.Expr
  | [], _, _, body => body
  | (id, type) :: rest, index, ordinal, body =>
      match copiedBinder? source id with
      | none => copyChainPlain source base rest (index + 1) ordinal body
      | some _ => .letE (.newCell (OptionalCell.cellType type) (.loadCell (.var (base index + ordinal))))
          (copyChainPlain source base rest (index + 1) (ordinal + 1) body)

/-- `copyScope` without an allocator. -/
def copyScopePlain (source : TypedSource) (scope : Scope) (base : Nat → Nat)
    (body : Core.Expr) : Core.Expr :=
  copyChainPlain source base scope 0 0 (body.rename (scopeCopyRenaming source scope base))

/-- An empty scope has nothing to copy. -/
theorem copyScopePlain_nil (source : TypedSource) (base : Nat → Nat) (body : Core.Expr) :
    copyScopePlain source [] base body = body := by
  have identity : scopeCopyRenaming source [] base = Renaming.id := by
    funext index
    simp [scopeCopyRenaming, copiedSlots, copyRenaming, Renaming.id]
  simp only [copyScopePlain, copyChainPlain, identity, Expr.rename_id]

private theorem copyChain_none (source : TypedSource) (scope : Scope) (base : Nat → Nat) :
    ∀ (rest : Scope) (index ordinal : Nat) (body : Core.Expr),
      copyChain none source scope base rest index ordinal body =
        .ok (copyChainPlain source base rest index ordinal body)
  | [], _, _, _ => rfl
  | (id, type) :: rest, index, ordinal, body => by
      unfold copyChain copyChainPlain
      split
      · exact copyChain_none source scope base rest (index + 1) ordinal body
      · simp only [copyCell, copyChain_none source scope base rest (index + 1) (ordinal + 1) body,
          bind, Except.bind, pure, Except.pure]

theorem copyScope_none (source : TypedSource) (scope : Scope) (base : Nat → Nat)
    (body : Core.Expr) :
    copyScope none source scope base body = .ok (copyScopePlain source scope base body) :=
  copyChain_none source scope base scope 0 0 _

private theorem copyChainPlain_hasType_inv {definitions : DataEnvironment} {source : TypedSource}
    {base : Nat → Nat} {body : Core.Expr} {type : Core.Ty} :
    ∀ (rest : Scope) (index ordinal : Nat) (context : Core.Context),
      HasType context (copyChainPlain source base rest index ordinal body) type definitions →
      ∃ copies : Core.Context, HasType (copies ++ context) body type definitions
  | [], _, _, context, typed => ⟨[], typed⟩
  | (id, slotType) :: rest, index, ordinal, context, typed => by
      unfold copyChainPlain at typed
      split at typed
      · exact copyChainPlain_hasType_inv rest (index + 1) ordinal context typed
      · cases typed with
        | letE _ continuation =>
            obtain ⟨copies, inner⟩ :=
              copyChainPlain_hasType_inv rest (index + 1) (ordinal + 1) _ continuation
            exact ⟨copies ++ [_], by simpa using inner⟩

/-- Typing of plain copies exposes the renamed body under the copies' types. -/
theorem copyScopePlain_hasType_inv {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {scope : Scope} {base : Nat → Nat} {body : Core.Expr} {type : Core.Ty}
    (typed : HasType context (copyScopePlain source scope base body) type definitions) :
    ∃ copies : Core.Context,
      HasType (copies ++ context) (body.rename (scopeCopyRenaming source scope base)) type definitions :=
  copyChainPlain_hasType_inv scope 0 0 context typed

/-- A generalized local copies its scope once: its instances and the
binder's own marker capture the copies, while the continuation keeps the
original cells. -/
def letInitializedSnapshot (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (binder : TypedBinder) (outputType payloadType : Core.Ty)
    (initializer body : Core.Expr) : Except Error Core.Expr := do
  let allocation ← match allocator with
    | none => pure (OptionalCell.allocateInitialized payloadType (.var 0))
    | some allocate => allocate ⟨source, scope, Renaming.insertion 0, binder, payloadType, some (.var 0)⟩
  let captured ← copyScope allocator source scope (fun index => index)
    (LanguageResult.bind (OptionalCell.referenceType payloadType) initializer
      (LanguageResult.success allocation))
  pure (LanguageResult.bind outputType captured body)

/-- Each parameter sees earlier parameters followed by its original capture
scope. The packed argument binder sits between those two portions. -/
def bindParameters (allocate : Allocator) (source : TypedSource) (scope : Scope)
    (parameters : List (TypedBinder × Core.Ty)) (outputType : Core.Ty)
    (projection : Nat → Nat → Core.Expr → Core.Expr) (body : Core.Expr) : Except Error Core.Expr :=
  parameters.zipIdx.foldrM (fun ((binder, type), index) continuation =>
    let prior := (parameters.take index).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
    letInitialized (some allocate) source prior (Renaming.insertion index) binder outputType type
      (LanguageResult.success (projection index parameters.length (.var index))) continuation) body

end Solcore.Frontend.SourceCoreSourceCells
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreFunctions
/-! Monomorphic function values over optional cells. Named references carry a
deterministic plan-local identity; lambdas retain anonymous identity and
capture by value: creation copies the captured cells, and each call copies
them again before binding its parameters. A supplied statement compiler owns
control flow, so this module adds no source evaluator or duplicate loop logic.
Ordinary let initializers are still evaluated before their binding is allocated. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFunctions

open SourceInference

abbrev Context := SourceCoreCalls.Context
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr
abbrev Signature := SourceCoreCalls.Signature
abbrev Key := SourceCoreCalls.Key

abbrev ExpressionLowerer := Nat → TypedSource → Scope → ExpressionId →
  (ExpressionId → Core.Word) → Except Error LoweredExpr

/-- The callback receives this expression policy for lambda bodies. It must
use the function-value binder, assignment, and statement type projection. -/
abbrev BodyLowerer := ExpressionLowerer → Nat → TypedSource → Scope → List StatementId →
  Core.Ty → (ExpressionId → Core.Word) → Core.Word → Core.Word → Except Error Core.Expr

/-- The profile authenticates this origin against its owned inventory. A
contextual profile captures the complete local substitution separately. -/
inductive CallableOrigin where
  | named (key : Key)
  | lambda (id : ExpressionId)
  | builtin (function : BuiltinFunctionId)
  deriving Repr

/-- A profile may add a typed, pure manifest after parameter binding and
before callable decoration. The enclosing assembled Core checker validates
its result under the same packed-argument/captured-environment convention. -/
abbrev RawLambdaBodyHook := Context → TypedSource → Scope → ExpressionNode →
  Core.Ty → Core.Ty → Core.Expr → Except Error Core.Expr

def unchangedLambdaBody : RawLambdaBodyHook := fun _ _ _ _ _ _ body => pure body

/-- After binding the raw body, a profile may capture an administrative
lexical value around the raw lambda. Callable decoration still owns the tags. -/
abbrev RawLambdaExpressionHook := RawLambdaBodyHook

def unchangedLambdaExpression : RawLambdaExpressionHook := fun _ _ _ _ _ _ expression => pure expression

/-- Shared expression/evidence traversal uses one callable representation.
Decoration receives a language result containing the raw tagged function;
the call hook owns the guard protocol before arguments and application.
Prepared source metadata remains authoritative when staged markers are allowed. -/
structure CallablePolicy where
  functionType : Core.Ty → Core.Ty → Core.Ty := Core.TaggedFunction.functionType
  decorateCallable : Context → TypedSource → ExpressionNode → CallableOrigin →
      Core.Ty → Core.Ty → Core.Expr → Except Error Core.Expr :=
    fun _ _ _ _ _ _ expression => pure expression
  callCallable : Context → TypedSource → ExpressionNode → Core.Ty → Core.Expr → Core.Expr →
      Except Error Core.Expr :=
    fun _ _ _ result callee arguments => pure (Core.TaggedFunction.call result callee arguments)
  allowStaged : Bool := false

/-- A representation profile supplies authenticated metadata projections and
additional data leaves. The recursive traversal and call order remain shared.
The leaf callback receives the same recursive expression compiler, so nominal
payloads can contain calls and closures without a second evaluator. -/
structure Policy where
  rawLambdaBody : RawLambdaBodyHook := unchangedLambdaBody
  rawLambdaExpression : RawLambdaExpressionHook := unchangedLambdaExpression
  callables : CallablePolicy := {}
  sourceCells : Option SourceCoreSourceCells.Allocator := none
  projectType : SourceCoreElaboration.ErrorSite → TypeSystem.Ty → Except Error Core.Ty :=
    SourceCoreFunctionTypes.projectType
  readExpression : TypedSource → ExpressionId → Except Error (ExpressionNode × Core.Ty) :=
    SourceCoreFunctionTypes.readExpression
  lowerBinder : TypedSource → Scope → TypedBinder → Except Error Core.Ty :=
    SourceCoreFunctionTypes.lowerBinder
  lowerRead : TypedSource → Scope → ExpressionId → Core.Word → Except Error Core.Expr :=
    SourceCoreFunctionTypes.lowerRead
  /-- Profiles may authenticate evidence and lower retained coercion paths
  before ordinary traversal. The supplied child compiler shares this policy. -/
  lowerSpecial? : Option (Context → ExpressionLowerer → Nat → TypedSource → Scope →
    ExpressionId → (ExpressionId → Core.Word) → Except Error (Option LoweredExpr)) := none
  /-- Whether a lambda occurrence copies its captures when it is created. An
  instance of a generalized local shares the copies of its declaration. -/
  snapshotLambda : ExpressionId → Bool := fun _ => true
  leafLowerer : ExpressionLowerer → Nat → TypedSource → Scope → ExpressionId →
      (ExpressionId → Core.Word) → Except Error LoweredExpr :=
    fun _ fuel source scope id reasonAt => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)

private def globalAt (globals : List Signature) (key : Key) : Except Error (Nat × Signature) :=
  match globals.zipIdx.filter (fun entry => decide (entry.1.key = key)) with
  | [] => .error (.callPreparation (.missingSpecialization key))
  | [(signature, index)] => .ok (index, signature)
  | candidates => .error (.callPreparation (.duplicateSpecialization key candidates.length))

/-- Actual plan/global selection, exposed for compiler certificates. -/
def selectedSignature (policy : Policy) (context : Context) (source : TypedSource) (node : ExpressionNode)
    (instantiation : DeclarationInstantiation) (isReference : Bool) : Except Error (Nat × Signature) := do
  if source.owner ≠ context.owner.declaration then throw (.ownerMismatch context.owner.declaration source.owner)
  let caller ← (SourceCompilationPlan.exactSpecialization context.plan context.owner).mapError SourceCoreBasic.Error.callPreparation
  unless caller.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions context.owner caller.assumptions))
  let target ← (SourceCompilationPlan.exactInstantiationKey context.plan instantiation).mapError SourceCoreBasic.Error.callPreparation
  let key ← (if isReference then SourceCompilationPlan.exactReferenceKey context.plan context.owner node.id target
    else SourceCompilationPlan.exactCallKey context.plan context.owner node.id target).mapError SourceCoreBasic.Error.callPreparation
  let specialized ← (SourceCompilationPlan.exactSpecialization context.plan key).mapError SourceCoreBasic.Error.callPreparation
  unless specialized.assumptions.isEmpty do throw (.callPreparation (.unresolvedAssumptions key specialized.assumptions))
  if !policy.callables.allowStaged &&
      (specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime)) then
    throw (.unsupportedExpression node.id node.form)
  let (parameter, result) ← match specialized.function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.callPreparation (.invalidFunctionType key specialized.function.type))
  let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
  let parameterType ← policy.projectType site parameter
  let resultType ← policy.projectType site result
  let (index, signature) ← globalAt context.globals key
  SourceCoreBasic.ensureType site parameterType signature.parameterType
  SourceCoreBasic.ensureType site resultType signature.resultType
  pure (index, signature)

def namedReference (signature : Signature) (index : Nat) (identity internalReason : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind (Core.TaggedFunction.functionType signature.parameterType signature.resultType)
    (Core.OptionalCell.read signature.functionType (.var index) internalReason)
    (Core.LanguageResult.success (Core.TaggedFunction.identified identity (.var 0)))

theorem namedReference_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {signature : Signature} {index : Nat} (identity internalReason : Core.Word)
    (parameterWF : Core.Ty.WellFormed definitions signature.parameterType)
    (resultWF : Core.Ty.WellFormed definitions signature.resultType)
    (reference : environment[index]? = some signature.referenceType) :
    Core.HasType environment (namedReference signature index identity internalReason)
      (Core.LanguageResult.resultType
        (Core.TaggedFunction.functionType signature.parameterType signature.resultType)) definitions := by
  apply Core.LanguageResult.bind_hasType (Core.TaggedFunction.functionType_wellFormed parameterWF resultWF)
  · apply Core.OptionalCell.read_hasType internalReason
      (.function parameterWF (Core.LanguageResult.resultType_wellFormed resultWF))
    exact .var reference
  · exact Core.LanguageResult.success_hasType (Core.TaggedFunction.identified_hasType identity (.var rfl))

/-- Parameter projections follow Unit/single/right-product source packing. -/
def argumentProjection (index : Nat) : Nat → Core.Expr → Core.Expr
  | 0, _ => .unit
  | 1, bundle => bundle
  | count + 2, bundle =>
      if index = 0 then .first bundle else argumentProjection (index - 1) (count + 1) (.second bundle)

def bindParameters (parameters : List (TypedBinder × Core.Ty)) (resultType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  parameters.zipIdx.foldr (fun ((_, type), index) continuation =>
    Core.LocalSequence.letInitialized resultType type
      (Core.LanguageResult.success (argumentProjection index parameters.length (.var index))) continuation) body

/-- Ordered parameter metadata lowering, exposed for compiler certificates. -/
def lambdaParameters (policy : Policy) (source : TypedSource) : Scope → List TypedBinder →
    Except Error (List (TypedBinder × Core.Ty) × Scope)
  | scope, [] => pure ([], scope)
  | scope, parameter :: parameters => do
      let type ← policy.lowerBinder source scope parameter
      let (remaining, scope) ← lambdaParameters policy source ((parameter.id, type) :: scope) parameters
      pure ((parameter, type) :: remaining, scope)

/-- Actual builtin metadata lowering, exposed for compiler certificates. -/
def builtinReference (callables : CallablePolicy) (context : Context) (source : TypedSource) (node : ExpressionNode)
    (name : String) (function : BuiltinFunctionId) : Except Error LoweredExpr := do
  if name ≠ function.spelling || node.type ≠ function.type then
    throw (.unsupportedExpression node.id node.form)
  let index ← match BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) with
    | some item => pure item.2
    | none => throw (.unsupportedExpression node.id node.form)
  let identity ← match Core.Word.ofNat? (context.globals.length + index + 1) with
    | some identity => pure identity
    | none => throw (.unsupportedExpression node.id node.form)
  let parameter := SourceCoreInteger.builtinParameter function
  let result := SourceCoreInteger.builtinResult function
  let expression ← callables.decorateCallable context source node (.builtin function) parameter result
    (Core.LanguageResult.success (Core.TaggedFunction.identified identity
      (SourceCoreInteger.builtinClosure function)))
  pure ⟨callables.functionType parameter result, expression⟩

/-- All recursive expression budgets are bounded by the current remaining
budget, including callbacks from the separately supplied statement traversal. -/
def lowerExpressionWithPolicy (policy : Policy) (lowerBody : BodyLowerer) : Nat → Context → TypedSource → Scope → ExpressionId →
    (ExpressionId → Core.Word) → Except Error LoweredExpr
  | 0, _, _, _, id, _ => .error (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1, context, source, scope, id, reasonAt => do
      if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
      let node ← match source.lookupExpression? id with
        | some node => pure node
        | none => .error (.missingExpression id)
      let special ← match policy.lowerSpecial? with
        | none => pure none
        | some lower =>
            lower context
              (fun budget childSource childScope childId childReasonAt =>
                lowerExpressionWithPolicy policy lowerBody (min budget fuel) context childSource childScope childId childReasonAt)
              (fuel + 1) source scope id reasonAt
      if let some lowered := special then return lowered
      match node.form with
      | .integerLiteral literal resolution =>
          if node.type = TypeSystem.Ty.integer then
            let validated ← (SourceCoreElaboration.validateNativeIntegerLiteral context.solvedRequirements
              node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
            pure ⟨.integer, Core.LanguageResult.success (.integer validated.value)⟩
          else
            let validated ← (SourceCoreElaboration.validateWordIntegerLiteral context.solvedRequirements
              node literal resolution).mapError SourceCoreBasic.Error.literalEvidence
            pure ⟨.word, Core.LanguageResult.success (.word validated.value)⟩
      | _ =>
          let (node, type) ← policy.readExpression source id
          let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
          match node.form with
          | .reference _ (.local _) =>
              let read ← policy.lowerRead source scope id (reasonAt id)
              pure ⟨type, read⟩
          | .reference name (.builtinFunction function) =>
              let lowered ← builtinReference policy.callables context source node name function
              SourceCoreBasic.ensureType site type lowered.type
              pure lowered
          | .call callee arguments (.builtinFunction function) =>
              (SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function)
                |>.mapError SourceCoreBasic.Error.literalEvidence
              let (calleeNode, _) ← policy.readExpression source callee
              let callee ← builtinReference policy.callables context source calleeNode function.spelling function
              let lowered ← arguments.mapM fun argument =>
                lowerExpressionWithPolicy policy lowerBody fuel context source scope argument reasonAt
              let packed := SourceCoreCalls.packArguments lowered
              SourceCoreBasic.ensureType site (SourceCoreInteger.builtinParameter function) packed.type
              SourceCoreBasic.ensureType site (SourceCoreInteger.builtinResult function) type
              let expression ← policy.callables.callCallable context source node type callee.expression packed.expression
              pure ⟨type, expression⟩
          | .reference _ (.declaration instantiation) =>
              let (index, signature) ← selectedSignature policy context source node instantiation true
              SourceCoreBasic.ensureType site type (policy.callables.functionType signature.parameterType signature.resultType)
              let identity ← match Core.Word.ofNat? (index + 1) with
                | some identity => pure identity
                | none => .error (.unsupportedExpression id node.form)
              let expression ← policy.callables.decorateCallable context source node (.named signature.key)
                signature.parameterType signature.resultType
                (namedReference signature (scope.length + context.administrativePrefix + index)
                  identity context.internalReason)
              pure ⟨type, expression⟩
          | .call callee arguments (.declaration instantiation) =>
              if callee.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner callee.occurrence.owner)
              discard <| policy.readExpression source callee
              (SourceCompilationPlan.validateDirectDeclarationCallee source id callee instantiation).mapError SourceCoreBasic.Error.callPreparation
              let (index, signature) ← selectedSignature policy context source node instantiation false
              let specialized ← (SourceCompilationPlan.exactSpecialization context.plan signature.key).mapError SourceCoreBasic.Error.callPreparation
              if arguments.length ≠ specialized.function.typedBody.inputs.length then
                throw (.callPreparation (.argumentArityMismatch specialized.function.typedBody.inputs.length arguments.length))
              SourceCoreBasic.ensureType site signature.resultType type
              let lowered ← arguments.mapM fun argument =>
                lowerExpressionWithPolicy policy lowerBody fuel context source scope argument reasonAt
              let packed := SourceCoreCalls.packArguments lowered
              SourceCoreBasic.ensureType site signature.parameterType packed.type
              pure ⟨type, SourceCoreCalls.call signature (scope.length + context.administrativePrefix + index)
                packed.expression context.internalReason⟩
          | .call callee arguments (.indirect metadata) =>
              unless metadata.argumentCoercions.isEmpty do throw (.unsupportedExpression id node.form)
              (SourceCompilationPlan.validateIndirectCallMetadata source node callee arguments metadata).mapError SourceCoreBasic.Error.callPreparation
              let (calleeNode, _) ← policy.readExpression source callee
              let (parameter, result) ← match calleeNode.type with
                | .function parameter result => pure (parameter, result)
                | _ => .error (.callPreparation (.indirectCalleeNotFunction id calleeNode.type))
              let parameterType ← policy.projectType site parameter
              let resultType ← policy.projectType site result
              SourceCoreBasic.ensureType site resultType type
              let callee ← lowerExpressionWithPolicy policy lowerBody fuel context source scope callee reasonAt
              let lowered ← arguments.mapM fun argument =>
                lowerExpressionWithPolicy policy lowerBody fuel context source scope argument reasonAt
              let packed := SourceCoreCalls.packArguments lowered
              SourceCoreBasic.ensureType site parameterType packed.type
              SourceCoreBasic.ensureType site (policy.callables.functionType parameterType resultType) callee.type
              let expression ← policy.callables.callCallable context source node resultType callee.expression packed.expression
              pure ⟨type, expression⟩
          | .lambda parameters returnType statements =>
              let (parameterType, resultType) ← match node.type with
                | .function parameter result => pure (parameter, result)
                | _ => .error (.unsupportedExpression id node.form)
              let bundle := TypeSystem.Ty.productMany (parameters.map (·.scheme.body))
              if bundle ≠ parameterType then throw (.callPreparation (.typeMismatch parameterType (some bundle)))
              if returnType ≠ resultType then throw (.callPreparation (.resultTypeMismatch resultType (some returnType)))
              let parameterCore ← policy.projectType site parameterType
              let resultCore ← policy.projectType site resultType
              let (parameters, bodyScope) ← lambdaParameters policy source scope parameters
              let body ← lowerBody
                (fun budget childSource childScope childId childReasonAt =>
                  lowerExpressionWithPolicy policy lowerBody (min budget fuel) context childSource childScope childId childReasonAt)
                fuel source bodyScope statements resultCore reasonAt context.internalReason context.internalReason
              let rawBody ← match policy.sourceCells with
                | none => pure (bindParameters parameters resultCore (body.weakenAt parameters.length))
                | some allocate =>
                    SourceCoreSourceCells.bindParameters allocate source scope parameters resultCore
                      argumentProjection (body.weakenAt parameters.length)
              let rawBody ← SourceCoreSourceCells.copyScope policy.sourceCells source scope (· + 1) rawBody
              let rawBody ← policy.rawLambdaBody context source scope node parameterCore resultCore rawBody
              SourceCoreBasic.ensureType site type (policy.callables.functionType parameterCore resultCore)
              let rawLambda ← policy.rawLambdaExpression context source scope node parameterCore resultCore
                (.lambda parameterCore (Core.LanguageResult.resultType resultCore) rawBody)
              let expression ← policy.callables.decorateCallable context source node (.lambda id) parameterCore resultCore
                (Core.LanguageResult.success (Core.TaggedFunction.anonymous rawLambda))
              if policy.snapshotLambda id then
                pure ⟨type, ← SourceCoreSourceCells.copyScope policy.sourceCells source scope (fun index => index) expression⟩
              else pure ⟨type, expression⟩
          | .unary operator operand =>
              let operand ← lowerExpressionWithPolicy policy lowerBody fuel context source scope operand reasonAt
              let coreOperator := if operator = .bitNot && operand.type = .integer then
                Core.UnaryOp.integerNot else SourceCorePrimitive.unaryOperator operator
              SourceCoreBasic.ensureType site coreOperator.operandType operand.type
              SourceCoreBasic.ensureType site coreOperator.resultType type
              pure ⟨type, Core.LocalPrimitiveResults.unary coreOperator operand.expression⟩
          | .binary left operator right =>
              let left ← lowerExpressionWithPolicy policy lowerBody fuel context source scope left reasonAt
              let right ← lowerExpressionWithPolicy policy lowerBody fuel context source scope right reasonAt
              if left.type = .integer then
                SourceCoreBasic.ensureType site (SourceCoreInteger.binaryOperandType operator) left.type
                SourceCoreBasic.ensureType site (SourceCoreInteger.binaryOperandType operator) right.type
                SourceCoreBasic.ensureType site (SourceCoreInteger.binaryResultType operator) type
                pure ⟨type, SourceCoreInteger.binary operator left.expression right.expression⟩
              else
                SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) left.type
                SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryOperandType operator) right.type
                SourceCoreBasic.ensureType site (SourceCorePrimitive.binaryResultType operator) type
                pure ⟨type, SourceCorePrimitive.binary operator left.expression right.expression⟩
          | .conditional condition thenBranch elseBranch =>
              let condition ← lowerExpressionWithPolicy policy lowerBody fuel context source scope condition reasonAt
              SourceCoreBasic.ensureType site .bool condition.type
              let thenBranch ← lowerExpressionWithPolicy policy lowerBody fuel context source scope thenBranch reasonAt
              let elseBranch ← lowerExpressionWithPolicy policy lowerBody fuel context source scope elseBranch reasonAt
              SourceCoreBasic.ensureType site type thenBranch.type
              SourceCoreBasic.ensureType site type elseBranch.type
              pure ⟨type, Core.LocalControl.choose type condition.expression thenBranch.expression elseBranch.expression⟩
          | .group inner =>
              let inner ← lowerExpressionWithPolicy policy lowerBody fuel context source scope inner reasonAt
              SourceCoreBasic.ensureType site type inner.type
              pure inner
          | .tuple [left, right] =>
              let left ← lowerExpressionWithPolicy policy lowerBody fuel context source scope left reasonAt
              let right ← lowerExpressionWithPolicy policy lowerBody fuel context source scope right reasonAt
              SourceCoreBasic.ensureType site type (.product left.type right.type)
              pure ⟨type, Core.LocalSequence.pair left.type right.type left.expression right.expression⟩
          | _ =>
              policy.leafLowerer
                (fun budget childSource childScope childId childReasonAt =>
                  lowerExpressionWithPolicy policy lowerBody (min budget fuel) context childSource childScope childId childReasonAt)
                (fuel + 1) source scope id reasonAt
termination_by fuel => fuel

/-- Existing monomorphic scalar/function profile. -/
def lowerExpressionWithReasons (lowerBody : BodyLowerer) (fuel : Nat) (context : Context)
    (source : TypedSource) (scope : Scope) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) :
    Except Error LoweredExpr :=
  lowerExpressionWithPolicy {} lowerBody fuel context source scope id reasonAt

end Solcore.Frontend.SourceCoreFunctions
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreLoops
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
abbrev FlowLowerer := Nat → TypedSource → Scope → List StatementId → Core.Ty →
  (ExpressionId → Core.Word) → Core.Word → Except Error Core.Expr

/-- Entry profiles supply type and binder projection independently of control. -/
structure Policy where
  lowerExpression : ExpressionLowerer
  sourceCells : Option SourceCoreSourceCells.Allocator := none
  readStatement : TypedSource → StatementId → Except Error (StatementNode × Core.Ty) :=
    SourceCoreBasic.readStatement
  lowerBinder : TypedSource → Scope → TypedBinder → Except Error Core.Ty :=
    SourceCoreBasic.lowerBinder
  lowerAssignment : TypedSource → Scope → AssignmentResolution → Syntax.ValueAssignOp →
    Except Error (Nat × Core.Ty) := SourceCoreBasic.lowerAssignment
  assignValue : Option (ExpressionLowerer → Nat → TypedSource → Scope → SourceCoreElaboration.ErrorSite →
    AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Core.Ty → Core.Expr →
    (ExpressionId → Core.Word) → Except Error Core.Expr) := none
  assignEqual : Option (ExpressionLowerer → Nat → TypedSource → Scope → SourceCoreElaboration.ErrorSite →
    AssignmentResolution → ExpressionId → Core.Ty → Core.Expr →
    (ExpressionId → Core.Word) → Except Error Core.Expr) := none
  assignBitNot : Option (TypedSource → Scope → SourceCoreElaboration.ErrorSite →
    AssignmentResolution → Core.Ty → Core.Expr → Except Error Core.Expr) := none
  assignBitNotWithExpression : Option (ExpressionLowerer → Nat → TypedSource → Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Core.Ty → Core.Expr →
    (ExpressionId → Core.Word) → Except Error Core.Expr) := none
  lowerMatch : Option (ExpressionLowerer → FlowLowerer → Nat → TypedSource → Scope → StatementId →
    MatchResolution → Core.Ty → (ExpressionId → Core.Word) → Core.Word → Except Error Core.Expr) := none

/-- Actual assignment callback selection, exposed for compiler certificates. -/
def assignValue (policy : Policy) (fuel : Nat) (source : TypedSource) (scope : Scope)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (outputType : Core.Ty)
    (next : Core.Expr) (reasonAt : ExpressionId → Core.Word) : Except Error Core.Expr := do
  match operator, policy.assignValue with
  | .equal, _ =>
      match policy.assignEqual with
      | some callback => callback policy.lowerExpression fuel source scope site assignment rhs outputType next reasonAt
      | none =>
        let (index, payloadType) ← policy.lowerAssignment source scope assignment operator
        let rhs ← policy.lowerExpression fuel source scope rhs reasonAt
        SourceCoreBasic.ensureType (.binder assignment.target.root) payloadType rhs.type
        pure (Core.LocalSequence.assign outputType (.var index) rhs.expression next)
  | _, none =>
      let (index, payloadType) ← policy.lowerAssignment source scope assignment operator
      let rhs ← policy.lowerExpression fuel source scope rhs reasonAt
      SourceCoreBasic.ensureType (.binder assignment.target.root) payloadType rhs.type
      pure (Core.LocalSequence.assign outputType (.var index) rhs.expression next)
  | _, some callback =>
      callback policy.lowerExpression fuel source scope site assignment operator rhs outputType next reasonAt

/-- Header items have no statement identity. They use the same authenticated
binder/expression/assignment checks and thread newly allocated lexical cells.
Only the supplied continuation determines whether that scope persists. -/
def lowerForItems (policy : Policy) (parentSite : SourceCoreElaboration.ErrorSite) : Nat → TypedSource → Scope →
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
          | none =>
              SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Core.Renaming.id
                binder payloadType body
          | some initializer =>
              let initializer ← policy.lowerExpression fuel source scope initializer reasonAt
              SourceCoreBasic.ensureType (.binder binder.id) payloadType initializer.type
              if binder.scheme.quantified.isEmpty then
                SourceCoreSourceCells.letInitialized policy.sourceCells source scope Core.Renaming.id binder
                  controlType payloadType initializer.expression body
              else
                SourceCoreSourceCells.letInitializedSnapshot policy.sourceCells source scope binder
                  controlType payloadType initializer.expression body
      | .expression expression =>
          let expression ← policy.lowerExpression fuel source scope expression reasonAt
          let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
          pure (Core.LocalSequence.discard controlType expression.expression body)
      | .assignValue assignment operator rhs =>
          let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
          assignValue policy fuel source scope parentSite assignment operator rhs controlType body reasonAt
      | .assignBitNot assignment =>
          match policy.assignBitNotWithExpression with
          | some callback =>
              let body ← lowerForItems policy parentSite fuel source scope rest resultType reasonAt next
              callback policy.lowerExpression fuel source scope parentSite assignment controlType body reasonAt
          | none => match policy.assignBitNot with
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
              SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Core.Renaming.id binder
                payloadType body
          | some initializer =>
              let initializer ← policy.lowerExpression fuel source scope initializer reasonAt
              SourceCoreBasic.ensureType (.binder binder.id) payloadType initializer.type
              let body ← lowerFlowStatementsWithPolicy policy fuel source ((binder.id, payloadType) :: scope)
                rest resultType reasonAt tailReturns selfReason
              if binder.scheme.quantified.isEmpty then
                SourceCoreSourceCells.letInitialized policy.sourceCells source scope Core.Renaming.id binder
                  controlType payloadType initializer.expression body
              else
                SourceCoreSourceCells.letInitializedSnapshot policy.sourceCells source scope binder
                  controlType payloadType initializer.expression body
      | .assignValue assignment operator value =>
          SourceCoreBasic.ensureType site .unit type
          let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
          assignValue policy fuel source scope site assignment operator value controlType body reasonAt
      | .assignBitNot assignment =>
          SourceCoreBasic.ensureType site .unit type
          match policy.assignBitNotWithExpression with
          | some callback =>
              let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
              callback policy.lowerExpression fuel source scope site assignment controlType body reasonAt
          | none => match policy.assignBitNot with
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
      | .matchWith resolution =>
          match policy.lowerMatch with
          | none => .error (.unsupportedStatement id node.form)
          | some callback =>
              let matched ← callback policy.lowerExpression
                (fun _ childSource childScope statements resultType childReasonAt childSelfReason =>
                  lowerFlowStatementsWithPolicy policy fuel childSource childScope statements
                    resultType childReasonAt false childSelfReason)
                fuel source scope id resolution resultType reasonAt selfReason
              let body ← lowerFlowStatementsWithPolicy policy fuel source scope rest resultType reasonAt tailReturns selfReason
              pure (Core.LocalLoop.sequence resultType matched body)
      | .breakStmt =>
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalLoop.breaking resultType)
      | .continueStmt =>
          SourceCoreBasic.ensureType site .unit type
          pure (Core.LocalLoop.continuing resultType)

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
end
