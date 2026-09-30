import Solcore.Frontend.SourceCoreScalar
import Solcore.Core.TaggedFunction

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
