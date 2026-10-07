import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! The original parameter receipt supplies genuine Source body typing.
Compiler syntax remains a separate static receipt for the same context, roots
and result type. Their conjunction supplies the actual imperative input facts;
it contains no execution or recursive body meaning premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
open Frontend SourceInference

variable {program : Program} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}

/-- Keep the original Source control judgment at the actual parameter context. -/
theorem statements
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function context environment heap) :
    ProtectedStateImperativeTypedSourceSites.Statements function.source context function.body := by
  obtain ⟨finalContext, facts, typed, _completes⟩ := receipt.bodyTyped
  exact ⟨{ returnType := function.resultType }, finalContext, facts, typed⟩

/-- Authenticate body input facts from the Source receipt and original syntax.
No native type or erased compiler body recovers the Source judgment. -/
theorem facts {expressionSyntax : ExpressionId → Prop}
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt program function context environment heap)
    (syntaxTree : GenericImperativeMatch.Syntax function.source expressionSyntax context
      (.statements true function.body) function.resultType) :
    ProtectedStateImperativeTypedSourceSites.Facts function.source expressionSyntax
      context true function.body function.resultType :=
  ⟨syntaxTree, statements receipt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyTypedFacts
