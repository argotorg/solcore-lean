import Solcore.Frontend.RuntimeParameters

/-! Construct structural evidence for the literal actual value, without checking
allocation or adding signature/unselected-type well-formedness requirements. -/
set_option autoImplicit false
namespace Solcore.Frontend

mutual
  private def buildValue? (value : Core.Value) : Option (PLift (Core.ValueHasType value value.type)) :=
    match value with
    | .unit => some ⟨.unit⟩
    | .bool _ => some ⟨.bool⟩
    | .word _ => some ⟨.word⟩
    | .hostFunction _ | .constructed _ _ => none
    | .pair left right => do
        let leftTyped ← buildValue? left
        let rightTyped ← buildValue? right
        return ⟨.pair leftTyped.down rightTyped.down⟩
    | .inLeft _ payload => do
        let typed ← buildValue? payload
        return ⟨.inLeft typed.down⟩
    | .inRight _ payload => do
        let typed ← buildValue? payload
        return ⟨.inRight typed.down⟩
    | .closure parameterType resultType body captured => do
        let typed ← buildEnvironment? captured
        if inferred : Core.infer? (parameterType :: captured.map Core.Value.type) body = some resultType then
          return ⟨.closure typed.down (Core.infer_sound inferred)⟩
        else none
    | .cellRef _ _ => some ⟨.cellRef⟩
  termination_by sizeOf value

  private def buildEnvironment? (captured : Core.Environment) :
      Option (PLift (Core.EnvironmentHasTypes captured (captured.map Core.Value.type))) :=
    match captured with
    | [] => some ⟨.nil⟩
    | value :: rest => do
        let head ← buildValue? value
        let tail ← buildEnvironment? rest
        return ⟨.cons head.down tail.down⟩
  termination_by sizeOf captured
end

/-- Build an existing typed-argument record without replacing its actual value.
This checks structural typing, not allocation or a supplied runtime world. -/
def buildRuntimeArgument? (value : Core.Value) : Option TypedRuntimeArgument :=
  (buildValue? value).map (fun typed => ⟨value.type,value,typed.down⟩)

end Solcore.Frontend
