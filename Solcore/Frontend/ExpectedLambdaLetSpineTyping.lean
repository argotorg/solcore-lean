import Solcore.Frontend.ExpectedLambdaLetSpine
import Solcore.Frontend.ExpectedComputationLambdaTyping

/-!
Independent source typing uses the same pure terminal/head boundary as the spine.
Each original initializer is typed before its new let row enters the recursive tail.
Neither Core output nor successful checking defines this judgment.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original annotation, expected initializer and recursive tail typing with disjoint source boundaries. -/
inductive ExpectedLambdaLetSpineHasType
    (ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Ty → Prop where
  | terminal {initial : LocalTypeInputs} {source : Syntax.Block} {type : Core.Ty}
      (boundary : isExpectedLambdaLetHead source = false)
      (body : ComputationReturnTreeHasType ChildHasType types owner initial source type) :
      ExpectedLambdaLetSpineHasType ChildHasType types owner initial source type
  | binding {initial : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty}
      (head : isExpectedLambdaLetHead
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = true)
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerTyping : ExpectedComputationLambdaHasType ChildHasType types owner initial initializer declaredType)
      (tailTyping : ExpectedLambdaLetSpineHasType ChildHasType types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ returnType) :
      ExpectedLambdaLetSpineHasType ChildHasType types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ returnType

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Source typing corresponds to elaboration existence using only child typing correspondence. -/
theorem expectedLambdaLetSpineHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {type : Core.Ty} :
    ExpectedLambdaLetSpineHasType ChildHasType types owner initial source type ↔
      ∃ core, ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  constructor
  · intro typing
    induction typing with
    | terminal boundary body =>
        obtain ⟨core, elaboration⟩ := (computationReturnTreeHasType_iff_elaborates childTyping).mp body
        exact ⟨_, .terminal boundary elaboration⟩
    | binding head meaning initializer tail ih =>
        obtain ⟨initializerCore, initializerElab⟩ := (expectedComputationLambdaHasType_iff_elaborates childTyping).mp initializer
        obtain ⟨tailCore, tailElab⟩ := ih
        exact ⟨_, .binding head meaning initializerElab tailElab⟩
  · rintro ⟨core, elaboration⟩
    induction elaboration with
    | terminal boundary body =>
        exact .terminal boundary ((computationReturnTreeHasType_iff_elaborates childTyping).mpr ⟨_, body⟩)
    | binding head meaning initializer tail ih =>
        exact .binding head meaning ((expectedComputationLambdaHasType_iff_elaborates childTyping).mpr ⟨_, initializer⟩) ih

/-- Exact child checking additionally identifies successful results of the maximal-prefix checker. -/
theorem expectedLambdaLetSpineHasType_iff_checked
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {type : Core.Ty} :
    ExpectedLambdaLetSpineHasType ChildHasType types owner initial source type ↔
      ∃ core, elaborateExpectedLambdaLetSpine? checkChild types owner initial source = some (core, type) := by
  rw [expectedLambdaLetSpineHasType_iff_elaborates childTyping]
  constructor
  · rintro ⟨core, elaboration⟩
    exact ⟨core, (elaborateExpectedLambdaLetSpine?_iff childCorrect).mpr elaboration⟩
  · rintro ⟨core, accepted⟩
    exact ⟨core, (elaborateExpectedLambdaLetSpine?_iff childCorrect).mp accepted⟩

end Solcore.Frontend
