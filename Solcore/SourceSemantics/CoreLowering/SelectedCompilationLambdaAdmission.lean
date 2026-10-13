import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
open Frontend SourceInference

theorem value_typed {program : Program} {context : SourceSemantics.Context}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {evidence : Dynamic.EvidenceEnvironment} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (empty : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    Dynamic.ValueHasType context heap (.closure {
      parameters := parameters, resultType := result, body := body,
      source := source, captured := environment, context := context, evidence := evidence }) node.type := by
  generalize expectedEq : node.type = expected at typed ⊢
  have contains := lookupExpression?_sound found
  have annotation := typed.lambda_annotation_of_uncoerced runtime.graph.nodeOccurrencesUnique contains form empty
  cases typed with
  | @intro _ _ actual raw plan actualContains formTyped rawEq rawWF typeWF requirements =>
    have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique actualContains).symm.trans found)
    subst actual
    have rawAnnotation : node.rawType = .function (TypeSystem.Ty.productMany (parameters.map (·.scheme.body))) result := by
      simpa [ExpressionNode.rawType, empty] using annotation
    rw [form] at formTyped
    cases formTyped with
    | lambda names extended bodyTyped completes =>
      rw [annotation]
      refine Dynamic.ValueHasType.closure rfl ?_ covers locals
      exact {
        owner := runtime.owner
        closed := runtime.closed
        variables_closed := runtime.variables_closed
        residual_variables_open := runtime.residual_variables_open
        graph := runtime.graph
        requirement_ledger := runtime.requirements
        occurrence := ⟨id, node, contains, form, rawAnnotation, by
          rw [form]
          simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq extended] using
            ExpressionFormHasRawType.lambda names extended bodyTyped completes⟩ }

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLambdaAdmission
