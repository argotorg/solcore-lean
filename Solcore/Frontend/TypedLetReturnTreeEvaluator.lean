import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Resolved.FreshIdentity

/-! Direct raw recursive-body evaluation. Optional annotations do not affect
type-free execution. Fresh IDs use the name table alone, and strict
initializers supply the actual values placed in the extended tail scope.
Discarded expressions execute strictly without extending source scopes. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Exact existing Core-transition cost, without checking or executing Core.
Raw selected success does not imply whole-source acceptance. -/
def evaluateTypedLetReturnTreeWithCost? (owner : Resolved.DeclarationId)
    (table : LocalNameTable) (environment : Resolved.Environment)
    (body : Syntax.Block) : Option (Core.Value × Nat) :=
  match body with
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => some (.unit, 1)
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      evaluateLocalExpressionWithCost? table environment source
  | ⟨blockSpan, ⟨_, .letDecl name _ (some initializer)⟩ :: rest⟩ => do
      let (boundValue, initializerCost) ← evaluateLocalExpressionWithCost? table environment initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let (value, tailCost) ← evaluateTypedLetReturnTreeWithCost? owner
        ((name.value, id) :: table) ((id, boundValue) :: environment) ⟨blockSpan, rest⟩
      return (value, initializerCost + tailCost + 2)
  | ⟨blockSpan, ⟨_, .expression expression true⟩ :: rest⟩ => do
      let (_, expressionCost) ← evaluateLocalExpressionWithCost? table environment expression
      let (value, tailCost) ← evaluateTypedLetReturnTreeWithCost? owner table environment ⟨blockSpan, rest⟩
      return (value, expressionCost + tailCost + 2)
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (.bool choice, conditionCost) ← evaluateLocalExpressionWithCost? table environment condition
        | none
      let (value, branchCost) ← if choice then
        evaluateTypedLetReturnTreeWithCost? owner table environment thenBody
      else evaluateTypedLetReturnTreeWithCost? owner table environment elseBody
      return (value, conditionCost + branchCost + 2)
  | _ => none
termination_by sizeOf body

end Solcore.Frontend
