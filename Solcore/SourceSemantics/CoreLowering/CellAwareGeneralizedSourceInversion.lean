import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.SelectedStatementPreservationSupport

/-! A genuine generalized Source declaration exposes its retained descriptor
and allocation directly. Its graded tail starts at the extended lexical
context without executing the principal initializer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases nodeEq
  exact same

private theorem extension_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binder : TypedBinder}
    (left : BinderExtends owner context binder first)
    (right : BinderExtends owner context binder second) : first = second := by
  cases left
  cases right
  rfl

theorem generalized {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize function location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.GeneralizedClosureCaptures context invocation.source environment binder initializer function ∧
      Dynamic.Heap.AllocatesGeneralized before function location bound ∧
      Size.StatementsIn program registry mode tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same captures _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact ⟨_, _, _, _, rfl, captures, allocated, remaining⟩
  | letInitialized actual same _ mono _ _ _ | letFault actual same mono _ =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact False.elim (polymorphic mono)
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible

/-- The actual checked statement supplies principal closure typing at the
current heap. It is obtained before any native instance body is called. -/
theorem captured_wellTyped {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {control : ControlContext}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {function : Dynamic.GeneralizedClosure} {facts : StatementFacts}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (typed : StatementHasType source control context id finalContext facts)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (polymorphic : binder.scheme.quantified ≠ [])
    (captures : Dynamic.GeneralizedClosureCaptures context source environment binder initializer function) :
    Dynamic.GeneralizedClosureWellTyped context heap function := by
  have shape := SelectedPreservation.statement_form runtime.graph.nodeOccurrencesUnique typed
    (lookupStatement?_sound found) form
  cases shape with
  | letInitialized _ mono _ => exact False.elim (polymorphic mono)
  | letInitializedGeneralized poly requirements generalizes value extension =>
    exact captures.wellTyped runtime locals poly requirements generalizes value extension

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
