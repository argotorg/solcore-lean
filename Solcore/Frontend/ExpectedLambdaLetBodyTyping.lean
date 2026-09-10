import Solcore.Frontend.ExpectedLambdaLetBody
import Solcore.Frontend.ExpectedComputationLambdaTyping

/-!
Independent source typing for a leading explicitly typed lambda initializer.
The original initializer is typed before the new let name enters the tail scope.
No Core expression or checker execution defines this source judgment.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Type the original annotation, lambda initializer and untouched tail independently of Core output. -/
inductive ExpectedLambdaLetBodyHasType
    (ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Block → Core.Ty → Prop where
  | binding {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerTyping : ExpectedComputationLambdaHasType ChildHasType types owner initial initializer declaredType)
      (tailTyping : ComputationReturnTreeHasType ChildHasType types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      ExpectedLambdaLetBodyHasType ChildHasType types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Source typing corresponds to elaboration existence using only child typing correspondence. -/
theorem expectedLambdaLetBodyHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {type : Core.Ty} :
    ExpectedLambdaLetBodyHasType ChildHasType types owner initial source type ↔
      ∃ core, ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type := by
  constructor
  · intro typing
    cases typing with
    | binding meaning initializer tail =>
        obtain ⟨initializerCore, initializerElab⟩ := (expectedComputationLambdaHasType_iff_elaborates childTyping).mp initializer
        obtain ⟨tailCore, tailElab⟩ := (computationReturnTreeHasType_iff_elaborates childTyping).mp tail
        exact ⟨_, .binding meaning initializerElab tailElab⟩
  · rintro ⟨core, elaboration⟩
    cases elaboration with
    | binding meaning initializer tail =>
        exact .binding meaning ((expectedComputationLambdaHasType_iff_elaborates childTyping).mpr ⟨_, initializer⟩)
          ((computationReturnTreeHasType_iff_elaborates childTyping).mpr ⟨_, tail⟩)

/-- Exact child checking additionally identifies successful results of the opt-in body checker. -/
theorem expectedLambdaLetBodyHasType_iff_checked
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {type : Core.Ty} :
    ExpectedLambdaLetBodyHasType ChildHasType types owner initial source type ↔
      ∃ core, elaborateExpectedLambdaLetBody? checkChild types owner initial source = some (core, type) := by
  rw [expectedLambdaLetBodyHasType_iff_elaborates childTyping]
  constructor
  · rintro ⟨core, elaboration⟩
    exact ⟨core, (elaborateExpectedLambdaLetBody?_iff childCorrect).mpr elaboration⟩
  · rintro ⟨core, accepted⟩
    exact ⟨core, (elaborateExpectedLambdaLetBody?_iff childCorrect).mp accepted⟩

end Solcore.Frontend
