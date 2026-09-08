import Solcore.Frontend.TypedLetReturnBodyProperties
import Solcore.Frontend.TerminalReturnTreeEmbeddingProperties

/-! Existing terminal trees embed with the identical Core and type. Optional
equality is restricted to terminal shapes, since valid let prefixes add success. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeHasType.typedLetReturnBody
    {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyHasType types owner inputs body type := .terminal typing

theorem TerminalReturnTreeElaborates.typedLetReturnBody
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnBodyElaborates types owner inputs body core type := .terminal elaboration

theorem TerminalReturnTreeElaborates.typedLetReturnBody_complete
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    elaborateTypedLetReturnBody? types owner inputs body = some (core, type) :=
  (elaboration.typedLetReturnBody types owner).complete

theorem elaborateTypedLetReturnBody?_single
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateReturnBody? inputs.names inputs.context
        ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  simp only [elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?_single]

/-- The recursive tree checker, not this prefix adapter, checks both original
arms. In particular a let inside either arm is not newly accepted. -/
theorem elaborateTypedLetReturnBody?_conditional
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block)
    (blockSpan ifSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ =
      elaborateTerminalReturnTree? inputs.names inputs.context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ := by
  simp only [elaborateTypedLetReturnBody?]

theorem elaborateTypedLetReturnBody?_conditional_singletons
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (condition : Syntax.Expr) (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTypedLetReturnBody? types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? inputs.names inputs.context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  rw [elaborateTypedLetReturnBody?_conditional]
  exact elaborateTerminalReturnTree?_conditional_singletons inputs.names inputs.context condition
    thenReturned elseReturned blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan

end Solcore.Frontend
