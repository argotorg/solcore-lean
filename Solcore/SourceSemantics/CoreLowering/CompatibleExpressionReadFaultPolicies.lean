import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.Dynamic.Fault

/-! An ordinary read fault policy consumes the actual Source binding
and current uninitialized cell. No diagnostic table or fault relation is
inferred from a native representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference

/-- The exact Source occurrence, lexical binding and current cell at the
ordinary uninitialized branch of an accepted read. -/
structure UninitializedWitness {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (location : Dynamic.Location) (cell : Dynamic.Cell) : Prop where
  contains : ContainsExpression source id certificate.node
  localReference : certificate.node.form = .reference certificate.name (.local certificate.binder)
  declaration : Resolved.LocalScope.Lookup context.locals certificate.binder certificate.declared.scheme
  occurrenceView : SourceCoreRawMetadata.runtimeType certificate.node.type =
    SourceCoreRawMetadata.runtimeType certificate.declared.scheme.body
  lookup : Dynamic.Environment.LooksUp environment certificate.binder location
  read : Dynamic.Heap.Reads heap location cell
  cellType : cell.type = certificate.declared.scheme.body
  ordinary : cell.generalized = none
  empty : cell.value = none
  notMapping : ¬ ∃ key value, cell.type = .mapping key value

/-- Inclusion is requested only for the location selected by this actual read.
The real environment, heap and lexical context remain explicit indices. -/
def UninitializedPolicy {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (faults : Dynamic.SemanticFault → Word → Prop) : Prop :=
  ∀ location cell, UninitializedWitness certificate context environment heap location cell →
    faults (.uninitializedLocation location) reason

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
