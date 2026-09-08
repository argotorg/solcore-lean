import Solcore.Frontend.TerminalReturnTreeProperties
import Solcore.Frontend.TypeNameProperties
import Solcore.Frontend.LocalTypeInputsProperties

/-! A separate value-free adapter for annotated, initialized, non-shadowing
local declarations followed by an existing terminal return tree. Rejection
is specific to this adapter; no general source binding policy is introduced. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Consume the original prefix in order. Each initializer uses the old scope;
the tail is already lowered under its new binder, so it needs no weakening. -/
def elaborateTypedLetReturnBody? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretTypeName? types annotation
        let (initializerCore, initializerType) ←
          elaborateLocalExpression? inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateTypedLetReturnBody? types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | _ => elaborateTerminalReturnTree? inputs.names inputs.context body
termination_by body.value.length

inductive TypedLetReturnBodyHasType (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | terminal {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
      (child : TerminalReturnTreeHasType inputs.names inputs.context body type) :
      TypedLetReturnBodyHasType types owner inputs body type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : TypeNameDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : TypedLetReturnBodyHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnBodyHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType

/-- Independent exact source provenance, with annotation meaning and all three
initializer obligations separate from the elaborated remaining statements. -/
inductive TypedLetReturnBodyElaborates (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | terminal {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : TerminalReturnTreeElaborates inputs.names inputs.context body core type) :
      TypedLetReturnBodyElaborates types owner inputs body core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      {initializerResolved : Resolved.Expr} {initializerCore tailCore : Core.Expr}
      (meaning : TypeNameDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved declaredType)
      (tailElaboration : TypedLetReturnBodyElaborates types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnBodyElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

end Solcore.Frontend
