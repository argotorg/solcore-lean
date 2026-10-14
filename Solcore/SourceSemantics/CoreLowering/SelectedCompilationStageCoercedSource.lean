import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
open Frontend SourceInference
open SelectedCompilationStageCoercionLiftBounds

inductive Branches (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (node : ExpressionNode)
    (size : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {rawSize pathSize value middle outcome after}
      (raw : RawOutcome program rawSize context evidence source environment before node.form
        node.requirements node.coercions (.value value) middle)
      (path : PathOutcome program pathSize context evidence middle node.coercions value outcome after)
      (rawLess : rawSize < size) (pathLess : pathSize < size) :
      Branches program context evidence source environment before node size outcome after
  | fault {rawSize reason after}
      (raw : RawOutcome program rawSize context evidence source environment before node.form
        node.requirements node.coercions (.fault reason) after)
      (rawLess : rawSize < size) :
      Branches program context evidence source environment before node size (.fault reason) after

theorem branches {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    Branches program context evidence source environment before node size outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .value (.value raw) (.value path) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocal contains localForm _ _ _ _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [form] at localForm
      cases localForm
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .fault (.fault raw) (SourceExecutionSize.child_lt_stepSize (by simp))
    | coercion contains raw path =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .value (.value raw) (.fault path) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _
    | generalizedLocalCoercion contains localForm _ _ _ _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [form] at localForm
      cases localForm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
