import Solcore.Resolved.LocalFragmentProperties
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TypedLetReturnTree

/-! Exact frontend provenance retains every child of the local Core fragment.
These structural consequences use lowering evidence, not evaluation or a
replacement expression of the same type. No runtime entry imports are needed. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem elaborateLocalExpression?_localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalExpression? table context source = some (core, type)) :
    Core.Expr.LocalFragment core := by
  obtain ⟨_, _, lowered, _⟩ := elaborateLocalExpression?_sound accepted
  exact lowered.localFragment

theorem ReturnBodyElaborates.localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ReturnBodyElaborates table context body core type) :
    Core.Expr.LocalFragment core := by
  cases elaboration with
  | bare => exact .unit
  | expression _ lowered _ => exact lowered.localFragment

theorem TerminalReturnTreeElaborates.localFragment
    {table : LocalNameTable} {context : Resolved.Context}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates table context body core type) :
    Core.Expr.LocalFragment core := by
  induction elaboration with
  | single child => exact child.localFragment
  | conditional _ lowered _ _ _ thenIH elseIH =>
      exact .ifE lowered.localFragment thenIH elseIH

theorem TypedLetReturnTreeElaborates.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnTreeElaborates types owner inputs body core type) :
    Core.Expr.LocalFragment core := by
  induction elaboration with
  | single child => exact child.localFragment
  | binding _ _ _ lowered _ _ ih | inferred _ _ lowered _ _ ih =>
      exact .letE lowered.localFragment ih
  | conditional _ lowered _ _ _ thenIH elseIH =>
      exact .ifE lowered.localFragment thenIH elseIH

end Solcore.Frontend
