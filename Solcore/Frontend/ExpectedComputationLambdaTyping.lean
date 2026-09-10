import Solcore.Frontend.ExpectedComputationLambda

/-!
Source-only typing for the standalone expected unary computation lambda profile.
The original header and body are retained independently of checking or Core output.
The expected type is an input, not a principal or source-unique inferred type.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original expected-header and body typing, with both component well-formedness guards. -/
inductive ExpectedComputationLambdaHasType
    (ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Expr → Core.Ty → Prop where
  | lambda {source : Syntax.Expr} {expected : Core.Ty} {header : DeclaredUnaryLambdaHeader}
      (headerDeclaration : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected header)
      (parameterWellFormed : Core.Ty.WellFormed [] header.parameterType)
      (returnWellFormed : Core.Ty.WellFormed [] header.returnType)
      (bodyTyping : ComputationReturnTreeHasType ChildHasType types owner
        header.inputs header.body header.returnType) :
      ExpectedComputationLambdaHasType ChildHasType types owner initial source expected

variable {ChildHasType : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Ty → Prop}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Source typing corresponds to elaboration existence using only child typing correspondence. -/
theorem expectedComputationLambdaHasType_iff_elaborates
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} :
    ExpectedComputationLambdaHasType ChildHasType types owner initial source expected ↔
      ∃ core, ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro typing
    cases typing with
    | lambda header parameterWellFormed returnWellFormed bodyTyping =>
        obtain ⟨bodyCore, bodyElaboration⟩ := (computationReturnTreeHasType_iff_elaborates childTyping).mp bodyTyping
        exact ⟨_, .lambda header parameterWellFormed returnWellFormed bodyElaboration⟩
  · rintro ⟨core, elaboration⟩
    cases elaboration with
    | lambda header parameterWellFormed returnWellFormed bodyElaboration =>
        exact .lambda header parameterWellFormed returnWellFormed
          ((computationReturnTreeHasType_iff_elaborates childTyping).mpr ⟨_, bodyElaboration⟩)

/-- Exact child checking additionally connects source typing to the unchanged lambda checker. -/
theorem expectedComputationLambdaHasType_iff_checked
    (childTyping : ∀ {table context source type},
      ChildHasType table context source type ↔ ∃ core, ChildElab table context source core type)
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} :
    ExpectedComputationLambdaHasType ChildHasType types owner initial source expected ↔
      ∃ core, elaborateExpectedComputationLambda? checkChild types owner initial source expected = some core := by
  rw [expectedComputationLambdaHasType_iff_elaborates childTyping]
  constructor
  · rintro ⟨core, elaboration⟩
    exact ⟨core, (elaborateExpectedComputationLambda?_iff childCorrect).mpr elaboration⟩
  · rintro ⟨core, accepted⟩
    exact ⟨core, (elaborateExpectedComputationLambda?_iff childCorrect).mp accepted⟩

end Solcore.Frontend
