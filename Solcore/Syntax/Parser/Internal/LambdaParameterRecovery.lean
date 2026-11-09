import Solcore.Syntax.Parser.Types
import Solcore.Syntax.Parser.Internal.ParameterRecoveryTotality
import Solcore.Syntax.Parser.Internal.DelimitedTotality

/-!
Two totality facts about `recoverLambdaParameter`.

`Parser/Internal/ParameterTotality` proves the same two theorems publicly. Lean accepts
that across imports, but not in a file that imports the other copy. So these stay in a small
file of their own, which that module must not import.
-/

/-!
Parser side of the parameter traces: raw and core parameters, tails,
recovery and dispatch.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties

/-! Lambda recovery retags only the recovered error AST. Exact function
recovery supplies its whole state, events, complete Failure, and unconditional
ordinary outcome. No caller report is committed or re-emitted by this wrapper. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem recoverLambdaParameter_ordinary : Parser.Ordinary recoverLambdaParameter := by
  intro input
  rcases recoverParameter_ordinary input with ⟨parameter, next, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨_, next, by simp only [recoverLambdaParameter, result]; rfl⟩
  · exact .inr ⟨failure, rejected, by simp only [recoverLambdaParameter, result]⟩

theorem recoverLambdaParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    recoverLambdaParameter input ≠ .invariant error := recoverLambdaParameter_ordinary.ne_invariant input error

end Solcore.Syntax.Parser.LambdaParameterInternals

end
