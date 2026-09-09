import Solcore.Frontend.TypedLetReturnTreeProperties
import Solcore.Frontend.TypedLetReturnBodyProperties

/-! Every old tree and outer-prefix success retains its exact Core and type.
New branch-local bindings mean old checker failures are not generally preserved. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TerminalReturnTreeHasType.typedLetReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
    (typing : TerminalReturnTreeHasType inputs.names inputs.context body type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction typing with
  | single child => exact .single child
  | conditional condition _ _ thenIH elseIH => exact .conditional condition thenIH elseIH

theorem TerminalReturnTreeElaborates.typedLetReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TerminalReturnTreeElaborates inputs.names inputs.context body core type)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | single child => exact .single child
  | conditional resolution lowered typing _ _ thenIH elseIH =>
      exact .conditional resolution (by simpa only [LocalTypeInputs.context_ids] using lowered)
        typing thenIH elseIH

theorem TypedLetReturnBodyHasType.returnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type) :
    TypedLetReturnTreeHasType types owner inputs body type := by
  induction typing with
  | terminal child => exact child.typedLetReturnTree types owner
  | binding meaning unused initializerTyping _ ih => exact .binding meaning.structural unused initializerTyping ih

theorem TypedLetReturnBodyElaborates.returnTree
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : TypedLetReturnBodyElaborates types owner inputs body core type) :
    TypedLetReturnTreeElaborates types owner inputs body core type := by
  induction elaboration with
  | terminal child => exact child.typedLetReturnTree types owner
  | binding meaning unused resolution lowered typing _ ih =>
      exact .binding meaning.structural unused resolution lowered typing ih

theorem elaborateTypedLetReturnTree?_some_of_terminalReturnTree
    {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (accepted : elaborateTerminalReturnTree? inputs.names inputs.context body = some (core, type)) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  ((elaborateTerminalReturnTree?_elaborates accepted).typedLetReturnTree types owner).complete

theorem elaborateTypedLetReturnTree?_some_of_typedLetReturnBody
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type)) :
    elaborateTypedLetReturnTree? types owner inputs body = some (core, type) :=
  (elaborateTypedLetReturnBody?_elaborates accepted).returnTree.complete

end Solcore.Frontend
