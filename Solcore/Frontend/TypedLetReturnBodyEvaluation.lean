import Solcore.Frontend.TerminalReturnTreeEvaluation
import Solcore.Resolved.FreshIdentity

/-! Independent operational paths for annotated, initialized let prefixes.
Raw evaluation does not imply whole acceptance or a source shadowing policy.
Fresh IDs are relative to the explicit names, not arbitrary runtime inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive TypedLetReturnBodyEvaluates (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Prop where
  | terminal {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
      (child : TerminalReturnTreeEvaluates table environment initialStore body value finalStore) :
      TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      (initializerEvaluation : LocalExpressionEvaluates table environment initialStore initializer boundValue middleStore)
      (tailEvaluation : TypedLetReturnBodyEvaluates owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore) :
      TypedLetReturnBodyEvaluates owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore

/-- Both child paths are mandatory even when the new binding is unused.
The original Core let contributes exactly enterLet and bindLet. -/
inductive TypedLetReturnBodyEvaluatesWithCost (owner : Resolved.DeclarationId) :
    LocalNameTable → Resolved.Environment → Core.Store → Syntax.Block → Core.Value → Core.Store → Nat → Prop where
  | terminal {table : LocalNameTable} {environment : Resolved.Environment}
      {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
      (child : TerminalReturnTreeEvaluatesWithCost table environment initialStore body value finalStore cost) :
      TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost
  | binding {table : LocalNameTable} {environment : Resolved.Environment}
      {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {initialStore middleStore finalStore : Core.Store} {boundValue value : Core.Value}
      {initializerCost tailCost : Nat}
      (initializerEvaluation : LocalExpressionEvaluatesWithCost table environment
        initialStore initializer boundValue middleStore initializerCost)
      (tailEvaluation : TypedLetReturnBodyEvaluatesWithCost owner
        ((name.value, Resolved.freshLocalId owner (table.map Prod.snd)) :: table)
        ((Resolved.freshLocalId owner (table.map Prod.snd), boundValue) :: environment)
        middleStore ⟨blockSpan, rest⟩ value finalStore tailCost) :
      TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        value finalStore (initializerCost + tailCost + 2)

end Solcore.Frontend
