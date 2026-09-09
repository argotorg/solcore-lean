import Solcore.Frontend.RuntimeParameterDeclarationsPositionProperties
import Solcore.Frontend.ReturnBodyElaboration

/-! Static parameter positions resolve and lower references exactly, even when
their annotation types have no inhabitants. All occurrence spans remain arbitrary. -/

set_option autoImplicit false

namespace Solcore.Frontend.RuntimeParametersDeclare

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {parameters : List Syntax.FunctionParameter} {inputs : LocalTypeInputs}
  {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
  {annotation : Syntax.TypeExpr} {type : Core.Ty}

theorem reference_resolves_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (span nameSpan : Syntax.SourceSpan) :
    ResolvesLocalExpression inputs.names ⟨span, .identifier ⟨nameSpan, name.value⟩⟩
      (.var ⟨owner, index⟩) := by
  obtain ⟨_, _, _, _, named, _, _⟩ := declared.position parameterAt
  exact .identifier named

theorem reference_elaborates_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type) (span nameSpan : Syntax.SourceSpan) :
    elaborateLocalExpression? inputs.names inputs.context
      ⟨span, .identifier ⟨nameSpan, name.value⟩⟩ =
        some (.var (parameters.length - 1 - index), type) := by
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position parameterAt
  cases actualMeaning.type_unique meaning.structural
  exact elaborateLocalExpression?_complete (.identifier named) (.var indexed) (.var found)

/-- Singleton return embeds the same positional resolution, lowering and type
evidence. The existing terminal union can wrap this judgment with `.single`. -/
theorem reference_return_elaborates_at
    (declared : RuntimeParametersDeclare types owner parameters inputs)
    (parameterAt : parameters[index]? = some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (blockSpan returnSpan span nameSpan : Syntax.SourceSpan) :
    ReturnBodyElaborates inputs.names inputs.context
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩
      (.var (parameters.length - 1 - index)) type := by
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position parameterAt
  cases actualMeaning.type_unique meaning.structural
  exact .expression (.identifier named) (.var indexed) (.var found)

end Solcore.Frontend.RuntimeParametersDeclare
