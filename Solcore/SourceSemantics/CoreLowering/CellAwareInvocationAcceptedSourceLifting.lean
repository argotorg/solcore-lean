import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

/-! Original Source executions of closed-subset expressions are staged
executions. A subset expression contains no call, so every original value rule
at a subset site is the staged rule of the same form, and a generalized local
read keeps its descriptor and empty coercion path. Fault outcomes are not
lifted here; `CellAwareInvocationAcceptedStatementLifting` lifts statement
lists. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {program : Program} {registry : Staging.Recursive.Registry}
  {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}

private theorem node_unique (unique : NodeOccurrencesUnique scope.source) {id : ExpressionId}
    {left right : ExpressionNode} (first : ContainsExpression scope.source id left)
    (second : ContainsExpression scope.source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem requirements_of {id : ExpressionId} (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    site.node.requirements = [] := by
  have requirements := site.requirements
  split at requirements
  · rename_i literal resolution integer
    exact absurd (same.symm.trans integer) (notInteger literal resolution)
  · exact requirements

private theorem occurrence {id : ExpressionId} (site : Site prepared named scope.source id)
    {form : ExpressionForm} (same : site.node.form = form)
    (notInteger : ∀ literal resolution, form ≠ .integerLiteral literal resolution) :
    Staging.Recursive.Occurrence scope id form :=
  ⟨site.node, lookupExpression?_sound site.found, same, requirements_of site same notInteger, site.coercions⟩

private theorem atomic_form {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    Staging.Recursive.AtomicForm form := by
  cases atomic <;> constructor

private theorem atomic_not_local {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form)
    (name : String) (binder : Resolved.LocalId) : form ≠ .reference name (.local binder) := by
  cases atomic <;> intro same <;> cases same

/-- A value execution of a subset expression is a staged execution with the
same value and heap. -/
theorem expression_value (unique : NodeOccurrencesUnique scope.source) {id : ExpressionId}
    (subset : Subset prepared named scope.source id) :
    ∀ {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value},
      Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before id value after →
      Staging.Recursive.Expression program registry scope context environment before id (.value value) after := by
  induction subset with
  | literal site atomic =>
    intro environment before after value evaluation
    exact Staging.Recursive.Lifting.atomic unique (lookupExpression?_sound site.found) (atomic_form atomic)
      site.coercions (fun name binder _ _ same => absurd same (atomic_not_local atomic name binder))
      (.value evaluation)
  | read site form =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    cases evaluation with
    | intro found raw coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      rw [site.coercions] at raw
      exact .atomicValue contains (by rw [form]; exact .reference _ _) site.coercions raw
    | generalizedLocal found formEq layout lookup read descriptor contextFields instantiation coercions =>
      cases node_unique unique found contains
      rw [site.coercions] at coercions
      cases coercions
      exact .generalizedLocal contains formEq layout lookup read descriptor contextFields instantiation
        (by rw [site.coercions]; exact .coercionsNil)
  | unary site form _ child =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | unary layout operand applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .unary (occurrence site form (fun _ _ same => by cases same)) (child operand) applied
      | method _ selected _ => cases selected
  | binary site form _ _ left right =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | binaryShortCircuit _ first circuit _ =>
      exact .binaryShortCircuit (occurrence site form (fun _ _ same => by cases same)) (left first) circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := CompatibleExpressionPrimitives.no_owned layout
      subst empty
      cases applies with
      | primitive applied =>
        exact .binary (occurrence site form (fun _ _ same => by cases same)) (left first) continues
          (right second) applied
      | method _ selected _ => cases selected
  | conditional site form _ _ _ test yes no =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | conditionalTrue _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same)) (test first) (yes second)
    | conditionalFalse _ first second =>
      exact .conditional (occurrence site form (fun _ _ same => by cases same)) (test first) (no second)
  | group site form _ child =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | group _ inner => exact .group (occurrence site form (fun _ _ same => by cases same)) (child inner)
  | pair site form _ _ left right =>
    intro environment before after value evaluation
    have contains := lookupExpression?_sound site.found
    have raw := CompatibleExpressionPrimitives.evaluation_raw unique contains
      (fun name binder same => by rw [form] at same; cases same) site.coercions evaluation
    rw [form, requirements_of site form (fun _ _ same => by cases same), site.coercions] at raw
    cases raw with
    | tuple _ elements pack =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second tail =>
          cases tail
          cases pack with
          | cons tail =>
            cases tail
            exact .pair (occurrence site form (fun _ _ same => by cases same)) (left first) (right second)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting
