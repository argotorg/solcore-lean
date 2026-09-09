import Solcore.Frontend.ReturnBodyElaboration
import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.LocalTypeInputsProperties

/-! A separate value-free adapter for recursive typed prefixes and terminal
if/else branches. Siblings start in the same original scope; their local fresh
IDs need not be globally distinct. Structural annotations or independently inferred
initializer types reuse existing Core and entry records. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Every written initializer and arm is checked in its own original scope.
The exact Core tail is already under its binder; no additional weakening is used. -/
def elaborateTypedLetReturnTree? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (inputs : LocalTypeInputs) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match body with
  | ⟨_, [⟨_, .returnStmt _⟩]⟩ => elaborateReturnBody? inputs.names inputs.context body
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let declaredType ← interpretStructuralType? types annotation
        let (initializerCore, initializerType) ← elaborateLocalExpression? inputs.names inputs.context initializer
        if initializerType = declaredType then do
          let (tailCore, returnType) ← elaborateTypedLetReturnTree? types owner
            (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
          return (.letE initializerCore tailCore, returnType)
        else none
      else none
  | ⟨blockSpan, ⟨_, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      if name.value ∉ inputs.names.map Prod.fst then do
        let (initializerCore, initializerType) ← elaborateLocalExpression? inputs.names inputs.context initializer
        let (tailCore, returnType) ← elaborateTypedLetReturnTree? types owner
          (inputs.bindFresh owner name.value initializerType) ⟨blockSpan, rest⟩
        return (.letE initializerCore tailCore, returnType)
      else none
  | ⟨_, [⟨_, .ifThen condition thenBody (some elseBody)⟩]⟩ => do
      let (conditionCore, conditionType) ← elaborateLocalExpression? inputs.names inputs.context condition
      if conditionType = .bool then do
        let (thenCore, thenType) ← elaborateTypedLetReturnTree? types owner inputs thenBody
        let (elseCore, elseType) ← elaborateTypedLetReturnTree? types owner inputs elseBody
        if thenType = elseType then return (.ifE conditionCore thenCore elseCore, thenType)
        else none
      else none
  | _ => none
termination_by sizeOf body

inductive TypedLetReturnTreeHasType (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | single {inputs : LocalTypeInputs} {body : Syntax.Block} {type : Core.Ty}
      (child : ReturnBodyHasType inputs.names inputs.context body type) :
      TypedLetReturnTreeHasType types owner inputs body type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer declaredType)
      (tailTyping : TypedLetReturnTreeHasType types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (initializerTyping : LocalExpressionHasType inputs.names inputs.context initializer inferredType)
      (tailTyping : TypedLetReturnTreeHasType types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ returnType) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩ returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {type : Core.Ty}
      (conditionTyping : LocalExpressionHasType inputs.names inputs.context condition .bool)
      (thenTyping : TypedLetReturnTreeHasType types owner inputs thenBody type)
      (elseTyping : TypedLetReturnTreeHasType types owner inputs elseBody type) :
      TypedLetReturnTreeHasType types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ type

/-- Original syntax and independently resolved, lowered and typed children
determine exact nested lets and both ordered branches, not merely the result type. -/
inductive TypedLetReturnTreeElaborates (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | single {inputs : LocalTypeInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (child : ReturnBodyElaborates inputs.names inputs.context body core type) :
      TypedLetReturnTreeElaborates types owner inputs body core type
  | binding {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement} {declaredType returnType : Core.Ty}
      {initializerResolved : Resolved.Expr} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved declaredType)
      (tailElaboration : TypedLetReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | inferred {inputs : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan}
      {name : Syntax.Identifier} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {inferredType returnType : Core.Ty} {initializerResolved : Resolved.Expr}
      {initializerCore tailCore : Core.Expr}
      (unused : name.value ∉ inputs.names.map Prod.fst)
      (resolution : ResolvesLocalExpression inputs.names initializer initializerResolved)
      (lowered : Resolved.Lowers inputs.ids initializerResolved initializerCore)
      (typing : Resolved.HasType inputs.context initializerResolved inferredType)
      (tailElaboration : TypedLetReturnTreeElaborates types owner
        (inputs.bindFresh owner name.value inferredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType
  | conditional {inputs : LocalTypeInputs} {blockSpan ifSpan : Syntax.SourceSpan}
      {condition : Syntax.Expr} {thenBody elseBody : Syntax.Block} {conditionResolved : Resolved.Expr}
      {conditionCore thenCore elseCore : Core.Expr} {type : Core.Ty}
      (resolution : ResolvesLocalExpression inputs.names condition conditionResolved)
      (lowered : Resolved.Lowers inputs.ids conditionResolved conditionCore)
      (typing : Resolved.HasType inputs.context conditionResolved .bool)
      (thenElaboration : TypedLetReturnTreeElaborates types owner inputs thenBody thenCore type)
      (elseElaboration : TypedLetReturnTreeElaborates types owner inputs elseBody elseCore type) :
      TypedLetReturnTreeElaborates types owner inputs
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
        (.ifE conditionCore thenCore elseCore) type

end Solcore.Frontend
