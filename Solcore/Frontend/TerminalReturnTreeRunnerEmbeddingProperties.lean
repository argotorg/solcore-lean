import Solcore.Frontend.TerminalReturnTreeRunner
import Solcore.Frontend.TerminalReturnTreeEmbeddingProperties

/-! Old-shape runner equality retains failure and every actual Core result.
Singleton arms are explicit; this does not identify old and recursive runners
on arbitrary deep bodies rejected by the old profile. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runTerminalReturnTree?_single (inputs : LocalInputs) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runReturnBody?, checkReturnBody?,
    elaborateTerminalReturnTree?_single]

theorem runTerminalReturnTree?_single_terminal (inputs : LocalInputs) (fuel : Nat)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store =
      inputs.runTerminalReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runTerminalReturnBody?, checkTerminalReturnBody?,
    elaborateTerminalReturnTree?_single_terminal]

theorem runTerminalReturnTree?_conditional_singletons (inputs : LocalInputs) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runConditionalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runConditionalReturnBody?, checkConditionalReturnBody?,
    elaborateTerminalReturnTree?_conditional_singletons]

theorem runTerminalReturnTree?_conditional_singletons_terminal (inputs : LocalInputs) (fuel : Nat)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    inputs.runTerminalReturnTree? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store =
      inputs.runTerminalReturnBody? fuel
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ store := by
  simp only [runTerminalReturnTree?, checkTerminalReturnTree?, runTerminalReturnBody?, checkTerminalReturnBody?,
    elaborateTerminalReturnTree?_conditional_singletons_terminal]

end Solcore.Frontend.LocalInputs
