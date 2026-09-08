import Solcore.Frontend.TerminalReturnTreeProperties
import Solcore.Frontend.TerminalReturnBodyProperties

/-! Old successful body judgments embed exactly. Full optional-result equality
is confined to old singleton and one-level shapes, not arbitrary return trees. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := .single typing

theorem ReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := .single elaboration

theorem ReturnBodyElaborates.returnTree_complete {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem ConditionalReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : ConditionalReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := by
  cases typing with
  | intro condition thenArm elseArm => exact .conditional condition thenArm.returnTree elseArm.returnTree

theorem ConditionalReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := by
  cases elaboration with
  | intro resolution lowered typing thenArm elseArm =>
      exact .conditional resolution lowered typing thenArm.returnTree elseArm.returnTree

theorem ConditionalReturnBodyElaborates.returnTree_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ConditionalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem TerminalReturnBodyHasType.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {type : Core.Ty} (typing : TerminalReturnBodyHasType table context body type) :
    TerminalReturnTreeHasType table context body type := by
  cases typing with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyElaborates.returnTree {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    TerminalReturnTreeElaborates table context body core type := by
  cases elaboration with
  | single child => exact child.returnTree
  | conditional child => exact child.returnTree

theorem TerminalReturnBodyElaborates.returnTree_complete
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnBodyElaborates table context body core type) :
    elaborateTerminalReturnTree? table context body = some (core, type) :=
  elaboration.returnTree.complete

theorem elaborateTerminalReturnTree?_single_terminal (table : LocalNameTable) (context : Resolved.Context)
    (returned : Option Syntax.Expr) (blockSpan returnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ =
      elaborateTerminalReturnBody? table context ⟨blockSpan, [⟨returnSpan, .returnStmt returned⟩]⟩ := by
  rw [elaborateTerminalReturnTree?_single, elaborateTerminalReturnBody?_single]

/-- Both arm shapes are explicitly singleton returns. Unsupported expressions
remain rejected equally; recursive arm blocks are deliberately not quantified. -/
theorem elaborateTerminalReturnTree?_conditional_singletons
    (table : LocalNameTable) (context : Resolved.Context) (condition : Syntax.Expr)
    (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateConditionalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  simp only [elaborateTerminalReturnTree?, elaborateConditionalReturnBody?]

theorem elaborateTerminalReturnTree?_conditional_singletons_terminal
    (table : LocalNameTable) (context : Resolved.Context) (condition : Syntax.Expr)
    (thenReturned elseReturned : Option Syntax.Expr)
    (blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan : Syntax.SourceSpan) :
    elaborateTerminalReturnTree? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ =
      elaborateTerminalReturnBody? table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition
          ⟨thenBlockSpan, [⟨thenReturnSpan, .returnStmt thenReturned⟩]⟩
          (some ⟨elseBlockSpan, [⟨elseReturnSpan, .returnStmt elseReturned⟩]⟩)⟩]⟩ := by
  rw [elaborateTerminalReturnBody?_conditional]
  exact elaborateTerminalReturnTree?_conditional_singletons table context condition thenReturned elseReturned
    blockSpan ifSpan thenBlockSpan thenReturnSpan elseBlockSpan elseReturnSpan

end Solcore.Frontend
