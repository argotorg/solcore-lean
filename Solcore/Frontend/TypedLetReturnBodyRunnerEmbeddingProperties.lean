import Solcore.Frontend.TypedLetReturnBodyRunner
import Solcore.Frontend.TypedLetReturnBodyEmbeddingProperties
import Solcore.Frontend.TerminalReturnTreeRunner

/-! Old terminal shapes preserve failure and complete machine results at
every fuel. Arbitrary prefixes cannot be identified with the old tree runner. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTypedLetReturnBody?_single
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runReturnBody?, checkReturnBody?,
    elaborateTypedLetReturnBody?_single, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnBody?_conditional
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store =
      inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runTerminalReturnTree?, checkTerminalReturnTree?,
    elaborateTypedLetReturnBody?_conditional, toTypeInputs_names, toTypeInputs_context]

theorem runTypedLetReturnBody?_conditional_singletons
    (inputs : LocalInputs) (types : TypeNameTable) (owner : Resolved.DeclarationId) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTypedLetReturnBody? types owner fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runConditionalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?, runConditionalReturnBody?, checkConditionalReturnBody?,
    elaborateTypedLetReturnBody?_conditional_singletons, toTypeInputs_names, toTypeInputs_context]

end Solcore.Frontend.LocalInputs
