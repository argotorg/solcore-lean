import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.TypedLexicalControlMeaning

/-! Static ordinary assignment heads and lexical continuations. Bare and
projected destinations retain their distinct source rules. Each head contains
concrete typed expression trees and compiler layout receipts, never execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Shape (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (place : PlaceResolution) (prepared : Prepared) :
    List SourceCoreBasic.LoweredExpr → TypeSystem.Ty → Prop where
  | bare (empty : place.projections = []) (layout : CompatibleBareAssignment.Layout values prepared) :
      Shape readFuel values source context solved reasonAt scope administrative definitions place prepared [] prepared.route.rootSourceType
  | projected {codes leaf sourceTypes site}
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source
        (CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt) scope site place prepared codes sourceTypes leaf administrative)
      (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
      Shape readFuel values source context solved reasonAt scope administrative definitions place prepared codes leaf

structure Head (readFuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) (administrative : Core.Context)
    (definitions : DataEnvironment) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  lowered : SourceCoreBasic.LoweredExpr
  node : ExpressionNode
  invalid : Word
  shape : Shape readFuel values source context solved reasonAt scope administrative definitions assignment.target prepared codes leaf
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  found : source.lookupExpression? rhs = some node
  right : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope rhs lowered
  rightView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type
  rightType : lowered.type = prepared.route.leafType
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer

namespace Head
variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

def emit (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) head.lowered.expression next output
    (binaryOperator (head.prepared.route.leafType = .integer) operator) false head.invalid

def writtenContext (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (actual : Core.Context) : Core.Context :=
  CompatibleRenamedPlaceSuccess.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

/-- The diagnostic table separately authenticates each emitted failure token. -/
structure Errors (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : faults (.invalidAssignmentOperands operator) head.invalid
end Head

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (context : SourceSemantics.Context) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | tail {mode statements expected type code}
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode statements expected type code) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode statements expected type code
  | assign {mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs)
      (remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode rest expected type body) :
      Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type))

namespace Tree
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : Scope}
  {administrative : Core.Context} {definitions : DataEnvironment}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {mode : Bool} → {statements : List StatementId} → {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
    Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
      mode statements expected type code → Prop where
  | tail {mode statements expected type code}
      (body : TypedLexicalControl.Tree layouts owner active frame globals onError readFuel values source solved reasonAt
        context scope mode statements expected type code) : Errors registry faults (.tail body)
  | assign {mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .assignValue assignment operator rhs}
      {head : Head readFuel values source context solved reasonAt scope administrative definitions assignment operator rhs}
      {remaining : Tree layouts owner active frame globals onError readFuel values source solved reasonAt context scope administrative definitions
        mode rest expected type body}
      (current : head.Errors registry faults) (tail : Errors registry faults remaining) :
      Errors registry faults (.assign found form head remaining)
end Tree
end Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatements
