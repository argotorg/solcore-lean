import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! The initialized declaration receipt is built from the exact child call in
its actual edge. No alternate existential initializer state is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
namespace ActualInitializerReceipt

theorem annotation {context : SourceInference.Context}
    {source : Option Syntax.TypeExpr} {expected : Option Ty}
    (accepted : AnnotationExpected context source expected) :
    LocalLetRequirementTiming.Annotation context source expected := by
  cases accepted with
  | absent => exact .none
  | present accepted => exact .some accepted

def statement
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : StatementResult}
    {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (accepted : inferStatementFuel (fuel + 1) context source expectedReturn initial = .ok result)
    (form : source.value = .letDecl name sourceType (some initializer))
    (annotated : AnnotationExpected context sourceType expected)
    (child : inferExprFuel fuel context initializer expected initial.allocateStatementId.2 = .ok (value, ready)) :
    LocalLetRequirementTiming.Receipt fuel context source initial result :=
  { name, initializer, annotation := sourceType, expected,
    annotationAccepted := annotation annotated, form, value, ready, child,
    completed := by
      cases annotated with
      | absent =>
          unfold inferStatementFuel at accepted
          simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm
      | present resolved =>
          unfold inferStatementFuel at accepted
          simp only [form, resolved, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm }

def header
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {result : ForItemForm}
    {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expected : Option Ty} {value : InferredExpression} {ready : State}
    (accepted : inferForItemFuel (fuel + 1) context source initial = .ok (result, final))
    (form : source.value = .letDecl name sourceType (some initializer))
    (annotated : AnnotationExpected context sourceType expected)
    (child : inferExprFuel fuel context initializer expected initial = .ok (value, ready)) :
    LocalHeaderRequirementTiming.Receipt fuel context source initial (result, final) :=
  { name, initializer, annotation := sourceType, expected,
    annotationAccepted := annotation annotated, form, value, ready, child,
    completed := by
      cases annotated with
      | absent =>
          unfold inferForItemFuel at accepted
          simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm
      | present resolved =>
          unfold inferForItemFuel at accepted
          simp only [form, resolved, child, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
          exact (Except.ok.inj accepted).symm }

end ActualInitializerReceipt
end Solcore.SourceSemantics.SourceInferenceExecution
