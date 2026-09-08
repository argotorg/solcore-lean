import Solcore.Frontend.ReturnBodyElaboration

/-! A separate recursive body adapter: singleton returns at the leaves and
singleton explicit if/else nodes. Every written branch is checked. Existing
nonrecursive body and runtime-function entry profiles remain unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Structural recursion on the original block has no depth or fuel limit.
Keep the exact condition and both ordered arms; add no Core operation. -/
def elaborateTerminalReturnTree? (table : LocalNameTable) (context : Resolved.Context)
    (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => elaborateReturnBody? table context body
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? table context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateTerminalReturnTree? table context thenBody
        let (elseCore, elseType) ← elaborateTerminalReturnTree? table context elseBody
        if thenType = elseType then
          return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none
termination_by sizeOf body

inductive TerminalReturnTreeHasType (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Ty → Prop where
  | single {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType table context body type) :
      TerminalReturnTreeHasType table context body type
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType table context condition .bool)
      (thenTyping : TerminalReturnTreeHasType table context thenBody type)
      (elseTyping : TerminalReturnTreeHasType table context elseBody type) :
      TerminalReturnTreeHasType table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Independent exact elaboration retains condition resolution, positional
lowering and typing, and the original recursive arm derivations separately. -/
inductive TerminalReturnTreeElaborates (table : LocalNameTable) (context : Resolved.Context) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates table context body core type) :
      TerminalReturnTreeElaborates table context body core type
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (conditionResolution : ResolvesLocalExpression table condition conditionResolved)
      (conditionLowered : Resolved.Lowers (Resolved.LocalScope.ids context) conditionResolved conditionCore)
      (conditionTyping : Resolved.HasType context conditionResolved .bool)
      (thenElaboration : TerminalReturnTreeElaborates table context thenBody thenCore type)
      (elseElaboration : TerminalReturnTreeElaborates table context elseBody elseCore type) :
      TerminalReturnTreeElaborates table context
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

end Solcore.Frontend
