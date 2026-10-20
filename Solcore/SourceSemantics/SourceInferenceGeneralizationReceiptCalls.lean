import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming
import Solcore.SourceSemantics.SourceInferenceActualCallGraph

/-! Initialized statements and headers expose the exact child call from their
actual execution receipt. Annotation evidence follows the original resolver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem

theorem annotationExpected_of_receipt
    {context : SourceInference.Context} {annotation : Option Syntax.TypeExpr} {expected : Option Ty}
    (receipt : LocalLetRequirementTiming.Annotation context annotation expected) :
    AnnotationExpected context annotation expected := by
  cases receipt with
  | none => exact .absent
  | some accepted => exact .present accepted

theorem statement_initializer_child
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted) :
    ChildStep (.statement (fuel + 1) context source expectedReturn initial result)
      (.expression fuel context receipt.initializer receipt.expected initial.allocateStatementId.2
        receipt.value receipt.ready) :=
  .statement_initializer accepted receipt.form rfl
    (annotationExpected_of_receipt receipt.annotationAccepted) receipt.child

theorem header_initializer_child
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial final : State} {inferred : ForItemForm}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial (inferred, final))
    (accepted : (CallIndex.forItem (fuel + 1) context source initial inferred final).Accepted) :
    ChildStep (.forItem (fuel + 1) context source initial inferred final)
      (.expression fuel context receipt.initializer receipt.expected initial receipt.value receipt.ready) :=
  .forItem_initializer accepted receipt.form
    (annotationExpected_of_receipt receipt.annotationAccepted) receipt.child

end Solcore.SourceSemantics.SourceInferenceExecution
