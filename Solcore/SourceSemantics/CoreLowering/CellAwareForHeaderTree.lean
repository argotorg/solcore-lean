import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission

/-! A finite header retains its actual compiler continuation and the exact
scope at that continuation. It contains only static typing and lowering data. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (type : Ty)
    (finalContext : SourceSemantics.Context) (finalScope : SourceCoreLocalCell.Scope)
    (terminal : Expr) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → List ForItemForm → Expr → Prop where
  | nil : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
      finalContext finalScope [] terminal
  | absent {context nextContext scope binder rest body payload}
      (declaration : SourceCoreDataPlaces.rootBinder (source named) binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        nextContext ((binder.id, payload) :: scope) rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  | initialized {context nextContext scope binder initializer node rest lowered body}
      (declaration : SourceCoreDataPlaces.rootBinder (source named) binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : (source named).lookupExpression? initializer = some node)
      (sourceType : node.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer node.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.letDecl binder (some initializer) :: rest)
        (sequence type lowered.expression annotation.expression body)
  | discard {context scope expression node rest lowered body}
      (found : (source named).lookupExpression? expression = some node)
      (typed : ExpressionHasType (source named) context expression node.type)
      (value : certificates context scope expression lowered)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.expression expression :: rest)
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) context
        (certificates context) scope administrative prepared.layouts.definitions assignment operator rhs)
      (bare : assignment.target.projections = [])
      (typed : SourceAssignmentHasType (source named) context assignment operator rhs)
      (operands : AssignmentOperandDiagnostics.OperandsLaw
        (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) operator head.invalid)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.assignValue assignment operator rhs :: rest)
        (head.emit body (LocalLoop.controlType type))

  | assignProjected {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) context
        (certificates context) scope administrative prepared.layouts.definitions assignment operator rhs)
      (projected : assignment.target.projections ≠ [])
      (typed : SourceAssignmentHasType (source named) context assignment operator rhs)
      (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite
        (fun site root => diagnostics.placeReason named.signature.key site root none)
        (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
        registry (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) head)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.assignValue assignment operator rhs :: rest)
        (head.emit body (LocalLoop.controlType type))

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
