import Solcore.SourceSemantics.SourceInferenceActualTerminalBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))  :
    BindersRetained (CallIndex.expression fuel context source none initial value middle).final.nodes (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferExprsFuel fuel context sources middle with
  | error error => simp [inferExprsFuel, head, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferExprsFuel_origins_progress tailAccepted).retained.trans
      (expressions_tail accepted head tailAccepted)


theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)  :
    BindersRetained (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).final.nodes (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes middle with
  | error error => simp [inferConstructorArgumentsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferConstructorArgumentsFuel_origins_progress tailAccepted).retained.trans
      (constructorArguments_tail accepted child tailAccepted)


theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)  :
    BindersRetained (CallIndex.forItem fuel context source initial value final).final.nodes (CallIndex.forItems fuel context (source :: sources) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferForItemsFuel fuel context sources final with
  | error error => simp [inferForItemsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferForItemsFuel_origins_progress tailAccepted).retained.trans
      (forItems_tail accepted child tailAccepted)


theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)  :
    BindersRetained (CallIndex.statements fuel context sources expectedReturn head.state tail).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest =>
    simp only [inferStatementsFuel, headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _


theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)  :
    BindersRetained (CallIndex.statement fuel context source expectedReturn initial head).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil =>
    simp only [inferStatementsFuel, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, child, tailAccepted, bind, Except.bind] at accepted
    | ok tail =>
      have nonempty : next :: rest ≠ [] := List.cons_ne_nil _ _
      exact (inferStatementsFuel_origins_progress tailAccepted).retained.trans
        (statements_tail accepted nonempty child tailAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
