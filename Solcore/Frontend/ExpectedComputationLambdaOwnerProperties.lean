import Solcore.Frontend.ExpectedComputationLambda
import Solcore.Frontend.ComputationReturnTreeOwnerProperties

/- Expected-type lambda checking changes no Core result under injective owner
relabeling.  Only the type-only local inputs and body child contexts move. -/
set_option autoImplicit false
namespace Solcore.Frontend

variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}

private theorem expectedComputationLambdaElaborates_mapOwner_iff
    (covariance : ∀ {table context source core type},
      ChildElab (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {expected : Core.Ty} :
    ExpectedComputationLambdaElaborates ChildElab types (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source core expected ↔
      ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro elaboration
    cases elaboration with
    | lambda header parameterWellFormed returnWellFormed bodyElaboration =>
        cases header with
        | lambda parameterDeclaration returnMeaning =>
            cases parameterDeclaration with
            | inferred =>
                rename_i bodyCore sourceSpan keyword parametersSpan returnAnnotation body
                  parameterType returnType span name
                have renamedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.bindFresh owner name.value parameterType).mapIds
                      (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
                    body bodyCore returnType := by
                  rw [LocalTypeInputs.bindFresh_mapOwner initial owner mapping injective
                    name.value parameterType]
                  exact bodyElaboration
                have originalBody :=
                  (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp
                    renamedBody
                have parameterWellFormed' : Core.Ty.WellFormed [] parameterType :=
                  parameterWellFormed
                have returnWellFormed' : Core.Ty.WellFormed [] returnType := returnWellFormed
                exact ExpectedComputationLambdaElaborates.lambda
                  (header := ⟨initial.bindFresh owner name.value parameterType,
                    body, parameterType, returnType⟩)
                  (ExpectedUnaryLambdaHeaderDeclares.lambda
                    (inputs := initial.bindFresh owner name.value parameterType)
                    ExpectedLambdaParameterDeclares.inferred returnMeaning)
                  parameterWellFormed' returnWellFormed' originalBody
            | typed meaning =>
                rename_i bodyCore sourceSpan keyword parametersSpan returnAnnotation body
                  parameterType returnType span name annotation
                have renamedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.bindFresh owner name.value parameterType).mapIds
                      (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
                    body bodyCore returnType := by
                  rw [LocalTypeInputs.bindFresh_mapOwner initial owner mapping injective
                    name.value parameterType]
                  exact bodyElaboration
                have originalBody :=
                  (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mp
                    renamedBody
                have parameterWellFormed' : Core.Ty.WellFormed [] parameterType :=
                  parameterWellFormed
                have returnWellFormed' : Core.Ty.WellFormed [] returnType := returnWellFormed
                exact ExpectedComputationLambdaElaborates.lambda
                  (header := ⟨initial.bindFresh owner name.value parameterType,
                    body, parameterType, returnType⟩)
                  (ExpectedUnaryLambdaHeaderDeclares.lambda
                    (inputs := initial.bindFresh owner name.value parameterType)
                    (ExpectedLambdaParameterDeclares.typed meaning) returnMeaning)
                  parameterWellFormed' returnWellFormed' originalBody
  · intro elaboration
    cases elaboration with
    | lambda header parameterWellFormed returnWellFormed bodyElaboration =>
        cases header with
        | lambda parameterDeclaration returnMeaning =>
            cases parameterDeclaration with
            | inferred =>
                rename_i bodyCore sourceSpan keyword parametersSpan returnAnnotation body
                  parameterType returnType span name
                have mappedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.bindFresh owner name.value parameterType).mapIds
                      (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
                    body bodyCore returnType :=
                  (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr
                    bodyElaboration
                have renamedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType) body bodyCore returnType := by
                  rw [← LocalTypeInputs.bindFresh_mapOwner initial owner mapping injective
                    name.value parameterType]
                  exact mappedBody
                have parameterWellFormed' : Core.Ty.WellFormed [] parameterType :=
                  parameterWellFormed
                have returnWellFormed' : Core.Ty.WellFormed [] returnType := returnWellFormed
                exact ExpectedComputationLambdaElaborates.lambda
                  (header := ⟨(initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType,
                    body, parameterType, returnType⟩)
                  (ExpectedUnaryLambdaHeaderDeclares.lambda
                    (inputs := (initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType)
                    ExpectedLambdaParameterDeclares.inferred returnMeaning)
                  parameterWellFormed' returnWellFormed' renamedBody
            | typed meaning =>
                rename_i bodyCore sourceSpan keyword parametersSpan returnAnnotation body
                  parameterType returnType span name annotation
                have mappedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.bindFresh owner name.value parameterType).mapIds
                      (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
                    body bodyCore returnType :=
                  (computationReturnTreeElaborates_mapOwner_iff mapping injective covariance).mpr
                    bodyElaboration
                have renamedBody : ComputationReturnTreeElaborates ChildElab types (mapping owner)
                    ((initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType) body bodyCore returnType := by
                  rw [← LocalTypeInputs.bindFresh_mapOwner initial owner mapping injective
                    name.value parameterType]
                  exact mappedBody
                have parameterWellFormed' : Core.Ty.WellFormed [] parameterType :=
                  parameterWellFormed
                have returnWellFormed' : Core.Ty.WellFormed [] returnType := returnWellFormed
                exact ExpectedComputationLambdaElaborates.lambda
                  (header := ⟨(initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType,
                    body, parameterType, returnType⟩)
                  (ExpectedUnaryLambdaHeaderDeclares.lambda
                    (inputs := (initial.mapIds (ownerLocalIdMap mapping)
                      (ownerLocalIdMap_injective mapping injective)).bindFresh
                        (mapping owner) name.value parameterType)
                    (ExpectedLambdaParameterDeclares.typed meaning) returnMeaning)
                  parameterWellFormed' returnWellFormed' renamedBody

/-- The complete expected-lambda checker, including rejection, returns the same
literal Core expression after an injective owner-only relabeling. -/
theorem elaborateExpectedComputationLambda?_mapOwner
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (covariance : ∀ table context source,
      checkChild (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source =
        checkChild table context source)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Expr) (expected : Core.Ty) :
    elaborateExpectedComputationLambda? checkChild types (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source expected =
      elaborateExpectedComputationLambda? checkChild types owner initial source expected := by
  let Graph := fun table context source core type =>
    checkChild table context source = some (core, type)
  have graphCovariance : ∀ {table context source core type},
      Graph (LocalNameTable.mapIds (ownerLocalIdMap mapping) table)
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) context) source core type ↔
        Graph table context source core type := by
    intro table context source core type
    dsimp only [Graph]
    rw [covariance]
  have accepted_iff {core} :
      elaborateExpectedComputationLambda? checkChild types (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
          source expected = some core ↔
        elaborateExpectedComputationLambda? checkChild types owner initial source expected = some core :=
    (elaborateExpectedComputationLambda?_iff (ChildElab := Graph) Iff.rfl).trans
      ((expectedComputationLambdaElaborates_mapOwner_iff mapping injective graphCovariance).trans
        (elaborateExpectedComputationLambda?_iff (ChildElab := Graph) Iff.rfl).symm)
  cases original : elaborateExpectedComputationLambda? checkChild types owner initial source expected with
  | none =>
      cases renamed : elaborateExpectedComputationLambda? checkChild types (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
          source expected with
      | none => rfl
      | some core =>
          have impossible := accepted_iff.mp renamed
          rw [original] at impossible
          cases impossible
  | some core => exact accepted_iff.mpr original

end Solcore.Frontend
