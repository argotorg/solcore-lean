import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentPreservation

/-! Ordinary assignment certificates share one expression certificate for keys
and RHS. Source metadata and generated native layouts are retained separately.
This interface is static; expression meaning is supplied by concrete clients. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Shape (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (place : PlaceResolution) (prepared : Prepared) :
    List SourceCoreBasic.LoweredExpr → TypeSystem.Ty → Prop where
  | bare (empty : place.projections = []) (layout : CompatibleBareAssignment.Layout values prepared) :
      Shape values source context certificate scope administrative definitions place prepared [] prepared.route.rootSourceType
  | projected {codes leaf sourceTypes site}
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source
        certificate scope site place prepared codes sourceTypes leaf administrative)
      (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
      Shape values source context certificate scope administrative definitions place prepared codes leaf

structure Head (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  lowered : SourceCoreBasic.LoweredExpr
  node : ExpressionNode
  invalid : Word
  shape : Shape values source context certificate scope administrative definitions assignment.target prepared codes leaf
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  found : source.lookupExpression? rhs = some node
  right : certificate scope rhs lowered
  rightView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type
  rightType : lowered.type = prepared.route.leafType
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

def emit (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) head.lowered.expression next output
    (binaryOperator (head.prepared.route.leafType = .integer) operator) false head.invalid

def writtenContext (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (actual : Core.Context) : Core.Context :=
  CompatibleRenamedPlaceSuccess.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

/-- The diagnostic table separately authenticates each emitted failure token. -/
structure Errors (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : faults (.invalidAssignmentOperands operator) head.invalid
end Head

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
