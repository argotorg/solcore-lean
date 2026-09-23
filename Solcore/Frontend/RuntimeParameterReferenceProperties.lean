import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.ReturnBody

/-! A source-position witness selects the exact supplied argument. Independent
first-match and index judgments, not type equality or row membership alone,
justify the reference. Identifier and expression ranges remain arbitrary. -/

set_option autoImplicit false

namespace Solcore.Frontend.RuntimeParametersBind

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {parameters : List Syntax.FunctionParameter} {arguments : List TypedRuntimeArgument}
  {inputs : LocalInputs} {index : Nat} {parameterSpan : Syntax.SourceSpan}
  {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}

theorem reference_resolves_at
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument) (span nameSpan : Syntax.SourceSpan) :
    ResolvesLocalExpression inputs.names ⟨span, .identifier ⟨nameSpan, name.value⟩⟩
      (.var ⟨owner, index⟩) := by
  obtain ⟨_, _, _, named, _, _, _⟩ := bound.position parameterAt argumentAt
  exact .identifier named

theorem reference_elaborates_at
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument) (span nameSpan : Syntax.SourceSpan) :
    elaborateLocalExpression? inputs.names inputs.context
      ⟨span, .identifier ⟨nameSpan, name.value⟩⟩ =
        some (.var (arguments.length - 1 - index), argument.type) := by
  obtain ⟨_, _, _, named, found, _, indexed⟩ := bound.position parameterAt argumentAt
  exact elaborateLocalExpression?_complete (.identifier named) (.var indexed) (.var found)

theorem reference_cost_at
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument) (span nameSpan : Syntax.SourceSpan)
    (store : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names inputs.environment store
      ⟨span, .identifier ⟨nameSpan, name.value⟩⟩ argument.value store 1 := by
  obtain ⟨_, _, _, named, _, found, _⟩ := bound.position parameterAt argumentAt
  exact .identifier named found

/-- Singleton return retains the exact positional Core variable and argument
type. Neither wrapper contributes another source lookup or Core operation. -/
theorem reference_return_elaborates_at
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (blockSpan returnSpan span nameSpan : Syntax.SourceSpan) :
    ReturnBodyElaborates inputs.names inputs.context
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩
      (.var (arguments.length - 1 - index)) argument.type := by
  obtain ⟨_, _, _, named, found, _, indexed⟩ := bound.position parameterAt argumentAt
  exact .expression (.identifier named) (.var indexed) (.var found)

end Solcore.Frontend.RuntimeParametersBind
