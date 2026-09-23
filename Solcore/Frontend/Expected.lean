import Solcore.Frontend.StructuralType
import Solcore.Frontend.LocalTypeInputs
import Solcore.Syntax.Term
import Solcore.Frontend.Computation
import Solcore.Frontend.ClosedSource
import Solcore.Frontend.RecursiveLocalComputation

/-! Expected-type lambda and local binding adapters. -/

/-!
## Consolidated module: `Solcore.Frontend.ExpectedUnaryLambdaHeader`
-/

/-!
Expected-type unary lambda headers prepare only an inner type-only scope.
The original body remains unchecked; no Core expression, closure, runtime value,
or source-lambda execution judgment is produced.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- The original runtime parameter agrees with the expected domain and shadows
outer spellings by prepending one fresh row without changing the outer rows. -/
inductive ExpectedLambdaParameterDeclares (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.LambdaParameter → Core.Ty → LocalTypeInputs → Prop where
  | inferred {span : Syntax.SourceSpan} {name : Syntax.Identifier} {type : Core.Ty} :
      ExpectedLambdaParameterDeclares types owner initial ⟨span, .inferred name⟩ type
        (initial.bindFresh owner name.value type)
  | typed {span : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation type) :
      ExpectedLambdaParameterDeclares types owner initial ⟨span, .typed none name annotation⟩ type
        (initial.bindFresh owner name.value type)

/-- Omitted lambda annotations retain the supplied codomain, not a Unit default. -/
inductive ExpectedLambdaReturnDenotes (types : TypeNameTable) :
    Option Syntax.TypeExpr → Core.Ty → Prop where
  | omitted {type : Core.Ty} : ExpectedLambdaReturnDenotes types none type
  | annotated {annotation : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation type) :
      ExpectedLambdaReturnDenotes types (some annotation) type

/-- Header preparation retains the exact original body and expected component
types. These type-only inputs are not a constructed runtime capture environment. -/
structure DeclaredUnaryLambdaHeader where
  inputs : LocalTypeInputs
  body : Syntax.Block
  parameterType : Core.Ty
  returnType : Core.Ty

/-- Independent agreement of one original lambda header with an explicit unary
function type; the body has no typing or evaluation premise. -/
inductive ExpectedUnaryLambdaHeaderDeclares (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Expr → Core.Ty → DeclaredUnaryLambdaHeader → Prop where
  | lambda {sourceSpan keyword parametersSpan : Syntax.SourceSpan}
      {parameter : Syntax.LambdaParameter} {returnAnnotation : Option Syntax.TypeExpr}
      {body : Syntax.Block} {parameterType returnType : Core.Ty} {inputs : LocalTypeInputs}
      (parameterDeclaration : ExpectedLambdaParameterDeclares types owner initial parameter parameterType inputs)
      (returnMeaning : ExpectedLambdaReturnDenotes types returnAnnotation returnType) :
      ExpectedUnaryLambdaHeaderDeclares types owner initial
        ⟨sourceSpan, .lambda keyword ⟨parametersSpan, [parameter]⟩ returnAnnotation body⟩
        (.function parameterType returnType) ⟨inputs, body, parameterType, returnType⟩

private def declareExpectedLambdaParameter? (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (parameter : Syntax.LambdaParameter) (expected : Core.Ty) : Option LocalTypeInputs :=
  match parameter.value with
  | .inferred name => some (initial.bindFresh owner name.value expected)
  | .typed none name annotation =>
      if interpretStructuralType? types annotation = some expected then
        some (initial.bindFresh owner name.value expected) else none
  | _ => none

private def expectedLambdaReturnAccepted (types : TypeNameTable)
    (annotation : Option Syntax.TypeExpr) (expected : Core.Ty) : Bool :=
  match annotation with
  | none => true
  | some source => decide (interpretStructuralType? types source = some expected)

/-- Opt-in header checking does not infer an expected type, inspect the body, or
consume parser diagnostics. Unsupported shapes and annotation disagreements fail. -/
def declareExpectedUnaryLambdaHeader? (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Expr) (expected : Core.Ty) : Option DeclaredUnaryLambdaHeader :=
  match source.value, expected with
  | .lambda _ ⟨_, [parameter]⟩ returnAnnotation body, .function parameterType returnType => do
      let inputs ← declareExpectedLambdaParameter? types owner initial parameter parameterType
      if expectedLambdaReturnAccepted types returnAnnotation returnType then
        some ⟨inputs, body, parameterType, returnType⟩ else none
  | _, _ => none

private theorem parameter_complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial output : LocalTypeInputs} {parameter : Syntax.LambdaParameter} {type : Core.Ty}
    (declared : ExpectedLambdaParameterDeclares types owner initial parameter type output) :
    declareExpectedLambdaParameter? types owner initial parameter type = some output := by
  cases declared with
  | inferred => rfl
  | typed meaning => simp only [declareExpectedLambdaParameter?, meaning.complete, ite_true]

private theorem parameter_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial output : LocalTypeInputs} {parameter : Syntax.LambdaParameter} {type : Core.Ty}
    (accepted : declareExpectedLambdaParameter? types owner initial parameter type = some output) :
    ExpectedLambdaParameterDeclares types owner initial parameter type output := by
  rcases parameter with ⟨span, payload⟩
  cases payload with
  | error => simp only [declareExpectedLambdaParameter?, reduceCtorEq] at accepted
  | inferred name =>
      simp only [declareExpectedLambdaParameter?, Option.some.injEq] at accepted
      subst output
      exact .inferred
  | typed marker name annotation =>
      cases marker with
      | some marker => simp only [declareExpectedLambdaParameter?, reduceCtorEq] at accepted
      | none =>
          simp only [declareExpectedLambdaParameter?] at accepted
          split at accepted
          · rename_i meaning
            cases Option.some.inj accepted
            exact .typed (interpretStructuralType?_sound meaning)
          · cases accepted

private theorem return_iff {types : TypeNameTable}
    {annotation : Option Syntax.TypeExpr} {type : Core.Ty} :
    expectedLambdaReturnAccepted types annotation type = true ↔
      ExpectedLambdaReturnDenotes types annotation type := by
  cases annotation with
  | none => exact ⟨fun _ => .omitted, fun _ => rfl⟩
  | some source =>
      simp only [expectedLambdaReturnAccepted, decide_eq_true_eq]
      constructor
      · exact fun meaning => .annotated (interpretStructuralType?_sound meaning)
      · intro meaning
        cases meaning with
        | annotated annotation => exact annotation.complete

private theorem header_complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial : LocalTypeInputs} {source : Syntax.Expr} {expected : Core.Ty}
    {output : DeclaredUnaryLambdaHeader}
    (declared : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected output) :
    declareExpectedUnaryLambdaHeader? types owner initial source expected = some output := by
  cases declared with
  | lambda parameterDeclaration returnMeaning =>
      simp only [declareExpectedUnaryLambdaHeader?, parameter_complete parameterDeclaration,
        bind, Option.bind_some, return_iff.mpr returnMeaning, ite_true]

private theorem header_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial : LocalTypeInputs} {source : Syntax.Expr} {expected : Core.Ty}
    {output : DeclaredUnaryLambdaHeader}
    (accepted : declareExpectedUnaryLambdaHeader? types owner initial source expected = some output) :
    ExpectedUnaryLambdaHeaderDeclares types owner initial source expected output := by
  rcases source with ⟨sourceSpan, source⟩
  cases source <;> cases expected <;>
    simp only [declareExpectedUnaryLambdaHeader?, reduceCtorEq] at accepted
  rename_i keyword parameters returnAnnotation body parameterType returnType
  rcases parameters with ⟨parametersSpan, parameters⟩
  cases parameters with
  | nil => simp only [reduceCtorEq] at accepted
  | cons parameter rest =>
      cases rest with
      | cons next rest => simp only [reduceCtorEq] at accepted
      | nil =>
          cases parameterChecked : declareExpectedLambdaParameter? types owner initial parameter parameterType with
          | none => simp only [parameterChecked, bind,
              Option.bind_none, reduceCtorEq] at accepted
          | some inputs =>
              simp only [parameterChecked, bind, Option.bind_some] at accepted
              split at accepted
              · rename_i returns
                cases Option.some.inj accepted
                exact .lambda (parameter_sound parameterChecked) (return_iff.mp returns)
              · cases accepted

/-- The executable result is exactly the independent original-header judgment. -/
theorem declareExpectedUnaryLambdaHeader?_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {output : DeclaredUnaryLambdaHeader} :
    declareExpectedUnaryLambdaHeader? types owner initial source expected = some output ↔
      ExpectedUnaryLambdaHeaderDeclares types owner initial source expected output :=
  ⟨header_sound, header_complete⟩

/-- Rejection means absence in this header profile, not a language-wide error. -/
theorem declareExpectedUnaryLambdaHeader?_eq_none_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} :
    declareExpectedUnaryLambdaHeader? types owner initial source expected = none ↔
      ¬ ∃ output, ExpectedUnaryLambdaHeaderDeclares types owner initial source expected output := by
  constructor
  · intro rejected ⟨output, declared⟩
    have accepted := header_complete declared
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : declareExpectedUnaryLambdaHeader? types owner initial source expected with
    | none => rfl
    | some output => exact False.elim (absent ⟨output, header_sound accepted⟩)

/-- The same original header and expected type determine one exact result. -/
theorem ExpectedUnaryLambdaHeaderDeclares.result_unique {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {left right : DeclaredUnaryLambdaHeader}
    (first : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected left)
    (second : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected right) : left = right :=
  Option.some.inj ((header_complete first).symm.trans (header_complete second))

/-- Successful preparation retains original syntax, body and annotation meaning,
and prepends exactly the fresh parameter row to the unchanged outer inputs. -/
theorem ExpectedUnaryLambdaHeaderDeclares.provenance_and_layout {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {output : DeclaredUnaryLambdaHeader}
    (declared : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected output) :
    ∃ sourceSpan keyword parametersSpan parameter returnAnnotation name,
      source = ⟨sourceSpan, .lambda keyword ⟨parametersSpan, [parameter]⟩ returnAnnotation output.body⟩ ∧
      expected = .function output.parameterType output.returnType ∧
      (parameter.value = .inferred name ∨ ∃ annotation,
        parameter.value = .typed none name annotation ∧
        StructuralTypeDenotes types annotation output.parameterType) ∧
      ExpectedLambdaReturnDenotes types returnAnnotation output.returnType ∧
      output.inputs = initial.bindFresh owner name.value output.parameterType ∧
      output.inputs.bindings =
        { name := name.value, id := Resolved.freshLocalId owner initial.ids,
          type := output.parameterType } :: initial.bindings := by
  cases declared with
  | lambda parameterDeclaration returnMeaning =>
      cases parameterDeclaration with
      | inferred => exact ⟨_, _, _, _, _, _, rfl, rfl, Or.inl rfl, returnMeaning, rfl, rfl⟩
      | typed meaning =>
          exact ⟨_, _, _, _, _, _, rfl, rfl, Or.inr ⟨_, rfl, meaning⟩, returnMeaning, rfl, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedComputationLambda`
-/

/-!
Standalone expected-type lambda elaboration retains the original header and body.
It does not extend existing source entry points, construct runtime captures, or
claim canonical backend execution or source-to-Core operational correspondence.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- The original header, representable component types and original body evidence
jointly determine a literal Core lambda, independently of any executable checker. -/
inductive ExpectedComputationLambdaElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | lambda {source : Syntax.Expr} {expected : Core.Ty}
      {header : DeclaredUnaryLambdaHeader} {bodyCore : Core.Expr}
      (headerDeclaration : ExpectedUnaryLambdaHeaderDeclares types owner initial source expected header)
      (parameterWellFormed : Core.Ty.WellFormed [] header.parameterType)
      (returnWellFormed : Core.Ty.WellFormed [] header.returnType)
      (bodyElaboration : ComputationReturnTreeElaborates ChildElab types owner
        header.inputs header.body bodyCore header.returnType) :
      ExpectedComputationLambdaElaborates ChildElab types owner initial source
        (.lambda header.parameterType header.returnType bodyCore) expected

/-- Check the original expected header and component types, then require the
unchanged shared body checker to return exactly the expected codomain. -/
def elaborateExpectedComputationLambda?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Expr) (expected : Core.Ty) : Option Core.Expr := do
  let header ← declareExpectedUnaryLambdaHeader? types owner initial source expected
  if header.parameterType.isWellFormed [] && header.returnType.isWellFormed [] then
    let (bodyCore, bodyType) ← elaborateComputationReturnTree? checkChild types owner header.inputs header.body
    if bodyType = header.returnType then
      some (.lambda header.parameterType header.returnType bodyCore)
    else none
  else none

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Exact checking uses only the fixed child's own checker correspondence. -/
theorem elaborateExpectedComputationLambda?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} {core : Core.Expr} :
    elaborateExpectedComputationLambda? checkChild types owner initial source expected = some core ↔
      ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro accepted
    cases headerChecked : declareExpectedUnaryLambdaHeader? types owner initial source expected with
    | none => simp only [elaborateExpectedComputationLambda?, headerChecked, bind, Option.bind_none, reduceCtorEq] at accepted
    | some header =>
        simp only [elaborateExpectedComputationLambda?, headerChecked, bind, Option.bind_some] at accepted
        split at accepted
        · rename_i wellFormed
          simp only [Bool.and_eq_true] at wellFormed
          obtain ⟨parameterWellFormed, returnWellFormed⟩ := wellFormed
          cases bodyChecked : elaborateComputationReturnTree? checkChild types owner header.inputs header.body with
          | none => simp only [bodyChecked, Option.bind_none, reduceCtorEq] at accepted
          | some result =>
              rcases result with ⟨bodyCore, bodyType⟩
              simp only [bodyChecked, Option.bind_some] at accepted
              split at accepted
              · rename_i same
                subst bodyType
                cases Option.some.inj accepted
                exact .lambda (declareExpectedUnaryLambdaHeader?_iff.mp headerChecked)
                  (Core.Ty.isWellFormed_sound parameterWellFormed)
                  (Core.Ty.isWellFormed_sound returnWellFormed)
                  ((elaborateComputationReturnTree?_iff childCorrect).mp bodyChecked)
              · cases accepted
        · cases accepted
  · intro elaboration
    cases elaboration with
    | lambda header parameterWellFormed returnWellFormed body =>
        simp only [elaborateExpectedComputationLambda?, declareExpectedUnaryLambdaHeader?_iff.mpr header,
          bind, Option.bind_some, Core.Ty.isWellFormed_complete parameterWellFormed,
          Core.Ty.isWellFormed_complete returnWellFormed, Bool.true_and, ite_true,
          (elaborateComputationReturnTree?_iff childCorrect).mpr body]

/-- Rejection is exact absence in this opt-in fixed Core profile. -/
theorem elaborateExpectedComputationLambda?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {expected : Core.Ty} :
    elaborateExpectedComputationLambda? checkChild types owner initial source expected = none ↔
      ¬ ∃ core, ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected := by
  constructor
  · intro rejected ⟨core, elaboration⟩
    have accepted := (elaborateExpectedComputationLambda?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedComputationLambda? checkChild types owner initial source expected with
    | none => rfl
    | some core => exact False.elim (absent ⟨core, (elaborateExpectedComputationLambda?_iff childCorrect).mp accepted⟩)

/-- Core typing uses only child Core typing, not child checker correctness.
No blanket well-formedness assumption is imposed on the outer local context. -/
theorem ExpectedComputationLambdaElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {expected : Core.Ty}
    (elaboration : ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected) :
    Core.HasType initial.context.values core expected := by
  cases elaboration with
  | lambda header parameterWellFormed returnWellFormed body =>
      obtain ⟨_, _, _, _, _, _, _, expectedShape, _, _, inputsEq, _⟩ := header.provenance_and_layout
      rw [expectedShape]
      apply Core.HasType.lambda parameterWellFormed returnWellFormed
      have bodyType := body.core_hasType childCoreType
      rw [inputsEq] at bodyType
      simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
        List.map_cons, Prod.snd] using bodyType

/-- Preserve original header/body evidence and exact lambda shape. The retained
header evidence supplies all original spans and the fresh-row scope layout. -/
theorem ExpectedComputationLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {expected : Core.Ty}
    (elaboration : ExpectedComputationLambdaElaborates ChildElab types owner initial source core expected) :
    ∃ header bodyCore,
      ExpectedUnaryLambdaHeaderDeclares types owner initial source expected header ∧
      Core.Ty.WellFormed [] header.parameterType ∧ Core.Ty.WellFormed [] header.returnType ∧
      ComputationReturnTreeElaborates ChildElab types owner header.inputs header.body bodyCore header.returnType ∧
      core = .lambda header.parameterType header.returnType bodyCore := by
  cases elaboration with
  | lambda header parameterWellFormed returnWellFormed body =>
      exact ⟨_, _, header, parameterWellFormed, returnWellFormed, body, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedComputationLambdaOwnerProperties`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.ExpectedComputationLambdaTyping`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.ExpectedDataLambdaInvocationProperties`
-/

/- Exact checked saved-body evidence, with caller prefixes kept separate. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem shape_unique {source : Syntax.Expr} {leftName rightName : Syntax.Identifier}
    {leftBody rightBody : Syntax.Block}
    (left : SourceUnaryLambdaShape source leftName leftBody)
    (right : SourceUnaryLambdaShape source rightName rightBody) :
    leftName = rightName ∧ leftBody = rightBody :=
  Prod.mk.inj (Option.some.inj
    ((sourceUnaryLambdaShape?_iff.mpr left).symm.trans (sourceUnaryLambdaShape?_iff.mpr right)))

private theorem checked_body {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore)) :
    elaborateComputationReturnTree? elaborateLocalExpression? types owner
      (inputs.bindFresh owner name.value parameterType) body = some (bodyCore, returnType) := by
  have elaboration := (elaborateExpectedComputationLambda?_iff
    (ChildElab := fun table context expression core type =>
      elaborateLocalExpression? table context expression = some (core, type))
    (fun {_ _ _ _ _} => Iff.rfl)).mp checked
  obtain ⟨header, compiled, declared, _, _, bodyElaboration, coreShape⟩ := elaboration.provenance
  obtain ⟨parameterSame, returnSame, bodySame⟩ := Core.Expr.lambda.inj coreShape
  cases declared with
  | lambda parameterDeclaration returnMeaning =>
      cases parameterDeclaration with
      | inferred =>
          cases shape
          cases parameterSame; cases returnSame; cases bodySame
          exact (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bodyElaboration
      | typed meaning =>
          cases shape
          cases parameterSame; cases returnSame; cases bodySame
          exact (elaborateComputationReturnTree?_iff (fun {_ _ _ _ _} => Iff.rfl)).mpr bodyElaboration

private theorem body_image {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body) (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Core.Value} {store : Core.Store} {actual : RuntimeValue} {final : List RuntimeValue} :
    ClosedSourceBodyEvaluates owner
      ((name.value, Resolved.freshLocalId owner (inputs.names.map Prod.snd)) :: inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd), RuntimeValue.ofCore argument) ::
        environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (store.map RuntimeValue.ofCore) body actual final ↔
    ∃ value finalStore, actual = RuntimeValue.ofCore value ∧
      final = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (argument :: Resolved.LocalScope.values environment) store bodyCore value finalStore := by
  have extendedIds : Resolved.LocalScope.ids
      ((Resolved.freshLocalId owner inputs.ids, argument) :: environment) =
      Resolved.LocalScope.ids (inputs.bindFresh owner name.value parameterType).context := by
    simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
      using congrArg (fun ids => Resolved.freshLocalId owner inputs.ids :: ids) sameIds
  have image := fragment.core_evaluates_iff (checked_body shape checked) extendedIds
    (actualValue := actual) (actualFinal := final) (initialStore := store)
  simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids, List.map_cons,
    Resolved.LocalScope.values, Prod.fst, Prod.snd] using image

/-- Actual caller prefixes invoke the checked original saved data body exactly. -/
theorem closedSourceExpectedDataLambda_invocation_core_iff
    {types : TypeNameTable} {savedOwner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {savedEnvironment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types savedOwner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameSavedIds : Resolved.LocalScope.ids savedEnvironment =
      Resolved.LocalScope.ids inputs.context)
    {callerOwner : Resolved.DeclarationId} {callerNames : LocalNameTable}
    {callerCaptured : List (Resolved.LocalId × RuntimeValue)}
    {initialStore calleeStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {argumentValue : Core.Value} {bodyStore : Core.Store}
    (calleeEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured initialStore callee
      (.sourceClosure source savedOwner inputs.names
        (savedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) calleeStore)
    (argumentEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured calleeStore argument (RuntimeValue.ofCore argumentValue)
      (bodyStore.map RuntimeValue.ofCore))
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (argumentValue :: Resolved.LocalScope.values savedEnvironment)
        bodyStore bodyCore value finalStore := by
  have image := body_image shape fragment checked sameSavedIds
    (argument := argumentValue) (store := bodyStore) (actual := actualValue) (final := actualFinal)
  constructor
  · intro evaluated
    cases evaluated with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
        obtain ⟨sameCallee, sameCalleeStore⟩ := actualCallee.deterministic calleeEvaluation
        cases sameCallee; cases sameCalleeStore
        obtain ⟨sameArgument, sameArgumentStore⟩ := actualArgument.deterministic argumentEvaluation
        cases sameArgument; cases sameArgumentStore
        obtain ⟨sameName, sameBody⟩ := shape_unique actualShape shape
        cases sameName; cases sameBody
        exact image.mp actualBody
  · intro evaluated
    exact .call shape calleeEvaluation argumentEvaluation (image.mpr evaluated)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedDataLambdaApplicationProperties`
-/

/- Direct original creation and an unprojected argument compose the whole Core application. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- A direct checked data lambda and original gated argument have the exact Core application image. -/
theorem closedSourceExpectedDataLambda_application_core_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Syntax.Expr} {resolvedArgument : Resolved.Expr} {argumentCore : Core.Expr}
    (argumentFragment : ClosedSourceDataExpression argument)
    (argumentResolution : ResolvesLocalExpression inputs.names argument resolvedArgument)
    (argumentLowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      resolvedArgument argumentCore)
    {initialStore : Core.Store} {callSpan argumentsSpan : Syntax.SourceSpan}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore)
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore
        (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore := by
  have creation : ClosedSourceExpressionEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source
      (.sourceClosure source owner inputs.names
        (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))))
      (initialStore.map RuntimeValue.ofCore) := .creation shape
  constructor
  · intro evaluated
    cases evaluated with
    | creation impossible => cases impossible
    | call actualShape actualCallee actualArgument actualBody =>
        obtain ⟨sameCallee, sameStore⟩ := actualCallee.deterministic creation
        cases sameCallee; cases sameStore
        obtain ⟨argumentValue, argumentStore, sameArgument, sameArgumentStore, argumentCoreEvaluation⟩ :=
          (argumentFragment.core_evaluates_iff argumentResolution argumentLowering).mp actualArgument
        cases sameArgument; cases sameArgumentStore
        have callEvaluation := ClosedSourceExpressionEvaluates.call
          (span := callSpan) (argumentsSpan := argumentsSpan) actualShape actualCallee actualArgument actualBody
        obtain ⟨value, finalStore, sameValue, sameFinal, bodyCoreEvaluation⟩ :=
          (closedSourceExpectedDataLambda_invocation_core_iff shape fragment checked sameIds
            creation actualArgument).mp callEvaluation
        exact ⟨value, finalStore, sameValue, sameFinal, .apply .lambda argumentCoreEvaluation bodyCoreEvaluation⟩
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    cases evaluated with
    | apply functionEvaluation argumentEvaluation bodyEvaluation =>
        cases functionEvaluation
        have argumentOriginal := (argumentFragment.core_evaluates_iff argumentResolution argumentLowering
          (owner := owner)).mpr ⟨_, _, rfl, rfl, argumentEvaluation⟩
        exact (closedSourceExpectedDataLambda_invocation_core_iff shape fragment checked sameIds
          creation argumentOriginal).mpr ⟨value, finalStore, rfl, rfl, bodyEvaluation⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedDataLambdaInvocationOwnerProperties`
-/

/- Lift the checked saved-body image through injective owner relabeling.  The
mapped callee is still a source closure; it is never identified with Core. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The mapped saved checker and identifier layout succeed; actual mapped caller
prefixes and every mapped call endpoint reflect to the original checked body
image.  Injectivity, but not surjectivity, is required. -/
theorem closedSourceExpectedDataLambda_invocation_mapOwners_core_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {types : TypeNameTable} {savedOwner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {savedEnvironment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types savedOwner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameSavedIds : Resolved.LocalScope.ids savedEnvironment =
      Resolved.LocalScope.ids inputs.context)
    {callerOwner : Resolved.DeclarationId} {callerNames : LocalNameTable}
    {callerCaptured : List (Resolved.LocalId × RuntimeValue)}
    {initialStore calleeStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {argumentValue : Core.Value} {bodyStore : Core.Store}
    (calleeEvaluation : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (initialStore.map (RuntimeValue.mapOwners mapping)) callee
      (.sourceClosure source (mapping savedOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment).map
          (fun row => (row.1, RuntimeValue.ofCore row.2))))
      (calleeStore.map (RuntimeValue.mapOwners mapping)))
    (argumentEvaluation : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) argument
      (RuntimeValue.ofCore argumentValue) (bodyStore.map RuntimeValue.ofCore))
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types (mapping savedOwner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source (.function parameterType returnType) =
          some (.lambda parameterType returnType bodyCore) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment) =
        Resolved.LocalScope.ids
          (inputs.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).context ∧
      (ClosedSourceExpressionEvaluates (mapping callerOwner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
        (mapRuntimeCapturedOwners mapping callerCaptured)
        (initialStore.map (RuntimeValue.mapOwners mapping))
        ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
      ∃ value finalStore,
        actualValue = RuntimeValue.ofCore value ∧
        actualFinal = finalStore.map RuntimeValue.ofCore ∧
        Core.Evaluates (argumentValue :: Resolved.LocalScope.values savedEnvironment)
          bodyStore bodyCore value finalStore) := by
  have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types (mapping savedOwner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore) := by
    rw [elaborateExpectedComputationLambda?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective))]
    exact checked
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) savedEnvironment) =
      Resolved.LocalScope.ids
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).context := by
    simpa only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameSavedIds
  have mappedCallee : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (initialStore.map (RuntimeValue.mapOwners mapping)) callee
      ((.sourceClosure source savedOwner inputs.names
        (savedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2))) : RuntimeValue).mapOwners mapping)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) := by
    simpa only [RuntimeValue.mapOwners_sourceClosure, mapRuntimeCapturedOwners_ofCore] using calleeEvaluation
  have originalCallee :=
    (ClosedSourceExpressionEvaluates.mapOwners_iff mapping injective).mp mappedCallee
  have mappedArgument : ClosedSourceExpressionEvaluates (mapping callerOwner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) callerNames)
      (mapRuntimeCapturedOwners mapping callerCaptured)
      (calleeStore.map (RuntimeValue.mapOwners mapping)) argument
      ((RuntimeValue.ofCore argumentValue).mapOwners mapping)
      ((bodyStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) := by
    simpa only [RuntimeValue.mapOwners_ofCore, mapRuntimeStoreOwners_ofCore] using argumentEvaluation
  have originalArgument :=
    (ClosedSourceExpressionEvaluates.mapOwners_iff mapping injective).mp mappedArgument
  refine ⟨mappedChecked, mappedSameIds, ?_⟩
  constructor
  · intro actual
    obtain ⟨before, beforeStore, original, values, stores⟩ :=
      (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp actual
    obtain ⟨value, finalStore, beforeEq, beforeStoreEq, evaluated⟩ :=
      (closedSourceExpectedDataLambda_invocation_core_iff
        (callSpan := callSpan) (argumentsSpan := argumentsSpan)
        shape fragment checked sameSavedIds originalCallee originalArgument).mp original
    refine ⟨value, finalStore, ?_, ?_, evaluated⟩
    · simpa only [beforeEq, RuntimeValue.mapOwners_ofCore] using values
    · simpa only [beforeStoreEq, mapRuntimeStoreOwners_ofCore] using stores
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    have original := (closedSourceExpectedDataLambda_invocation_core_iff
      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
      shape fragment checked sameSavedIds originalCallee originalArgument).mpr
        ⟨value, finalStore, rfl, rfl, evaluated⟩
    simpa only [RuntimeValue.mapOwners_ofCore, mapRuntimeStoreOwners_ofCore] using
      original.mapOwners mapping injective

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedDataLambdaApplicationOwnerProperties`
-/

/- Direct application keeps the original checked lambda and argument lowering.
The owner map changes identities only, while the Core application stays literal. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- The mapped checker, identifier layout and argument stages all succeed, and
the mapped direct source application has exactly the old Core application image.
No argument runtime typing or closure conversion is asserted. -/
theorem closedSourceExpectedDataLambda_application_mapOwners_core_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Syntax.Expr} {resolvedArgument : Resolved.Expr} {argumentCore : Core.Expr}
    (argumentFragment : ClosedSourceDataExpression argument)
    (argumentResolution : ResolvesLocalExpression inputs.names argument resolvedArgument)
    (argumentLowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      resolvedArgument argumentCore)
    {initialStore : Core.Store} {callSpan argumentsSpan : Syntax.SourceSpan}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    elaborateExpectedComputationLambda? elaborateLocalExpression? types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
        source (.function parameterType returnType) =
          some (.lambda parameterType returnType bodyCore) ∧
      Resolved.LocalScope.ids
          (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
        Resolved.LocalScope.ids
          (inputs.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).context ∧
      ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        argument (resolvedArgument.renameIds (ownerLocalIdMap mapping)) ∧
      Resolved.Lowers
          (Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
          (resolvedArgument.renameIds (ownerLocalIdMap mapping)) argumentCore ∧
        (ClosedSourceExpressionEvaluates (mapping owner)
          (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
          ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
            (fun row => (row.1, RuntimeValue.ofCore row.2)))
          (initialStore.map RuntimeValue.ofCore)
          ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
        ∃ value finalStore,
          actualValue = RuntimeValue.ofCore value ∧
          actualFinal = finalStore.map RuntimeValue.ofCore ∧
          Core.Evaluates (Resolved.LocalScope.values environment) initialStore
            (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore) := by
  have argumentStages := argumentFragment.mapOwners_core_evaluates_iff mapping injective
    (owner := owner) (names := inputs.names) (environment := environment)
    (initialStore := initialStore) (actualValue := actualValue) (actualFinal := actualFinal)
    argumentResolution argumentLowering
  have mappedChecked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))
      source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore) := by
    rw [elaborateExpectedComputationLambda?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective))]
    exact checked
  have mappedSameIds : Resolved.LocalScope.ids
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).context := by
    simpa only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  refine ⟨mappedChecked, mappedSameIds, argumentStages.1, argumentStages.2.1, ?_⟩
  constructor
  · intro actual
    have mapped : ClosedSourceExpressionEvaluates (mapping owner)
        (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
        (mapRuntimeCapturedOwners mapping
          (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2))))
        ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping))
        ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal := by
      simpa only [mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore] using actual
    obtain ⟨before, beforeStore, original, values, stores⟩ :=
      (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp mapped
    obtain ⟨value, finalStore, beforeEq, beforeStoreEq, evaluated⟩ :=
      (closedSourceExpectedDataLambda_application_core_iff
        (callSpan := callSpan) (argumentsSpan := argumentsSpan)
        shape fragment checked sameIds argumentFragment argumentResolution argumentLowering).mp original
    refine ⟨value, finalStore, ?_, ?_, evaluated⟩
    · simpa only [beforeEq, RuntimeValue.mapOwners_ofCore] using values
    · simpa only [beforeStoreEq, mapRuntimeStoreOwners_ofCore] using stores
  · rintro ⟨value, finalStore, rfl, rfl, evaluated⟩
    have original := (closedSourceExpectedDataLambda_application_core_iff
      (callSpan := callSpan) (argumentsSpan := argumentsSpan)
      shape fragment checked sameIds argumentFragment argumentResolution argumentLowering).mpr
        ⟨value, finalStore, rfl, rfl, evaluated⟩
    simpa only [mapRuntimeCapturedOwners_ofCore, mapRuntimeStoreOwners_ofCore,
      RuntimeValue.mapOwners_ofCore] using original.mapOwners mapping injective

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedLambdaArgumentApplication`
-/

/-!
An opt-in adapter for a unary call whose argument is an expected-type
computation lambda. It deliberately does not change the recursive inference
checker or any parser/diagnostic entry point.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A locally inferred unary callee supplies the exact expected type for a
literal computation-lambda argument. -/
inductive ExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      ExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
        (.apply functionCore argumentCore) resultType

/-- Infer the callee, then check the sole argument as a computation lambda at
the callee's parameter type. -/
def elaborateExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ => do
      let (functionCore, functionType) ←
        elaborateRecursiveLocalComputation? inputs.names inputs.context callee
      match functionType with
      | .function parameterType resultType => do
          let argumentCore ← elaborateExpectedComputationLambda?
            elaborateRecursiveLocalComputation? types owner inputs argument parameterType
          some (.apply functionCore argumentCore, resultType)
      | _ => none
  | _ => none

/-- Exact executable/declarative correspondence for the opt-in adapter. -/
theorem elaborateExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaArgumentApplication? types owner inputs source = some (core, type) ↔
      ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateExpectedLambdaArgumentApplication?] at accepted
          | cons argument tail =>
            cases tail with
            | cons second rest => simp [elaborateExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases calleeChecked : elaborateRecursiveLocalComputation?
                  inputs.names inputs.context callee with
              | none =>
                  simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked] at accepted
              | some calleeResult =>
                rcases calleeResult with ⟨functionCore, functionType⟩
                have calleeElaboration := elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                cases functionType <;>
                  try { simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked] at accepted }
                case function parameterType resultType =>
                  cases argumentChecked : elaborateExpectedComputationLambda?
                      elaborateRecursiveLocalComputation? types owner inputs argument parameterType with
                  | none =>
                      simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked,
                        argumentChecked] at accepted
                  | some argumentCore =>
                    have argumentElaboration :=
                      (elaborateExpectedComputationLambda?_iff
                        (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                    simp [elaborateExpectedLambdaArgumentApplication?, calleeChecked,
                      argumentChecked] at accepted
                    rcases accepted with ⟨rfl, rfl⟩
                    exact .application calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application calleeElaboration argumentElaboration =>
      simp [elaborateExpectedLambdaArgumentApplication?,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Rejection is precisely absence of adapter evidence. -/
theorem elaborateExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateExpectedLambdaArgumentApplication? types owner inputs source = none ↔
      ¬ ∃ core type,
        ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaArgumentApplication? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- The adapter preserves the inferred result type in Core. -/
theorem ExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Concise inversion retains both original children and the exact Core apply. -/
theorem ExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan callee argument functionCore argumentCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, rfl, calleeElaboration, argumentElaboration, rfl⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedLambdaLetBody`
-/

/-!
One original leading typed let passes its annotation to a lambda initializer.
The initializer uses the original outer scope; only the untouched shared tail
receives the new binding. Existing source entry points and raw evaluation are unchanged.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Original annotation, expected initializer and post-binding tail evidence determine a literal Core let. -/
inductive ExpectedLambdaLetBodyElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs) :
    Syntax.Block → Core.Expr → Core.Ty → Prop where
  | binding {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerElaboration : ExpectedComputationLambdaElaborates ChildElab types owner
        initial initializer initializerCore declaredType)
      (tailElaboration : ComputationReturnTreeElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ExpectedLambdaLetBodyElaborates ChildElab types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

/-- Check only an explicitly typed lambda-let head, then reuse the unchanged shared tail checker. -/
def elaborateExpectedLambdaLetBody?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ => do
      let declaredType ← interpretStructuralType? types annotation
      let initializerCore ← elaborateExpectedComputationLambda? checkChild types owner initial initializer declaredType
      let (tailCore, returnType) ← elaborateComputationReturnTree? checkChild types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
      return (.letE initializerCore tailCore, returnType)
  | _ => none

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

/-- Exact checking requires only the fixed child's checker/elaboration correspondence. -/
theorem elaborateExpectedLambdaLetBody?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaLetBody? checkChild types owner initial source = some (core, type) ↔
      ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type := by
  constructor
  · intro accepted
    unfold elaborateExpectedLambdaLetBody? at accepted
    split at accepted
    · rename_i blockSpan letSpan name annotation initializer rest
      simp only [bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨declaredType, meaning, initializerCore, initializerAccepted, tailResult, tailAccepted, resultEq⟩ := accepted
      rcases tailResult with ⟨tailCore, returnType⟩
      cases Option.some.inj resultEq
      exact .binding (interpretStructuralType?_iff.mp meaning)
        ((elaborateExpectedComputationLambda?_iff childCorrect).mp initializerAccepted)
        ((elaborateComputationReturnTree?_iff childCorrect).mp tailAccepted)
    · cases accepted
  · intro elaboration
    cases elaboration with
    | binding meaning initializer tail =>
        simp only [elaborateExpectedLambdaLetBody?, (interpretStructuralType?_iff).mpr meaning,
          bind, Option.bind_some, pure, (elaborateExpectedComputationLambda?_iff childCorrect).mpr initializer,
          (elaborateComputationReturnTree?_iff childCorrect).mpr tail]

/-- Rejection is absence in this opt-in profile, not a language-wide invalidity judgment. -/
theorem elaborateExpectedLambdaLetBody?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} :
    elaborateExpectedLambdaLetBody? checkChild types owner initial source = none ↔
      ¬ ∃ core type, ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := (elaborateExpectedLambdaLetBody?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaLetBody? checkChild types owner initial source with
    | none => rfl
    | some result => exact False.elim (absent ⟨_, _, (elaborateExpectedLambdaLetBody?_iff childCorrect).mp accepted⟩)

/-- Core typing uses only child Core typing, independently of checking or runtime assumptions. -/
theorem ExpectedLambdaLetBodyElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type) :
    Core.HasType initial.context.values core type := by
  cases elaboration with
  | binding meaning initializer tail =>
      exact .letE (initializer.core_hasType childCoreType)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values,
          List.map_cons, Prod.snd] using tail.core_hasType childCoreType)

/-- Preserve the exact original head/tail, pre-binder initializer scope and fresh tail-row layout. -/
theorem ExpectedLambdaLetBodyElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetBodyElaborates ChildElab types owner initial source core type) :
    ∃ blockSpan letSpan name annotation initializer rest declaredType initializerCore tailCore,
      source = ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ ∧
      StructuralTypeDenotes types annotation declaredType ∧
      ExpectedComputationLambdaElaborates ChildElab types owner initial initializer initializerCore declaredType ∧
      ComputationReturnTreeElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore type ∧
      core = .letE initializerCore tailCore ∧
      (initial.bindFresh owner name.value declaredType).bindings =
        { name := name.value, id := Resolved.freshLocalId owner initial.ids, type := declaredType } :: initial.bindings := by
  cases elaboration with
  | binding meaning initializer tail =>
      exact ⟨_, _, _, _, _, _, _, _, _, rfl, meaning, initializer, tail, rfl,
        LocalTypeInputs.bindFresh_bindings _ _ _ _⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedLambdaLetBodyTyping`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.ExpectedLambdaLetSpine`
-/

/-!
A pure original-source boundary selects consecutive explicitly typed lambda lets.
Recognized heads use the current pre-binder scope and never fall back on failure.
At the first non-head, the entire remaining body uses the unchanged shared checker.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Inspect only the original typed-let/direct-lambda shape, not any type or header validity. -/
def isExpectedLambdaLetHead : Syntax.Block → Bool
  | ⟨_, ⟨_, .letDecl _ (some _) (some ⟨_, .lambda _ _ _ _⟩)⟩ :: _⟩ => true
  | _ => false

/-- Disjoint original terminal/head derivations preserve each initializer and fresh tail scope. -/
inductive ExpectedLambdaLetSpineElaborates
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId) :
    LocalTypeInputs → Syntax.Block → Core.Expr → Core.Ty → Prop where
  | terminal {initial : LocalTypeInputs} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
      (boundary : isExpectedLambdaLetHead source = false)
      (body : ComputationReturnTreeElaborates ChildElab types owner initial source core type) :
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type
  | binding {initial : LocalTypeInputs} {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
      {declaredType returnType : Core.Ty} {initializerCore tailCore : Core.Expr}
      (head : isExpectedLambdaLetHead
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ = true)
      (meaning : StructuralTypeDenotes types annotation declaredType)
      (initializerElaboration : ExpectedComputationLambdaElaborates ChildElab types owner
        initial initializer initializerCore declaredType)
      (tailElaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore returnType) :
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial
        ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩
        (.letE initializerCore tailCore) returnType

/-- Check the maximal direct-lambda prefix; true-boundary failure never delegates to the old body. -/
def elaborateExpectedLambdaLetSpine?
    (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (source : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  if isExpectedLambdaLetHead source = false then
    elaborateComputationReturnTree? checkChild types owner initial source
  else match source with
  | ⟨blockSpan, ⟨_, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ => do
      let declaredType ← interpretStructuralType? types annotation
      let initializerCore ← elaborateExpectedComputationLambda? checkChild types owner initial initializer declaredType
      let (tailCore, returnType) ← elaborateExpectedLambdaLetSpine? checkChild types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩
      return (.letE initializerCore tailCore, returnType)
  | _ => none
termination_by sizeOf source
decreasing_by simp_wf; omega

variable {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}

private theorem checker_sound
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateExpectedLambdaLetSpine? checkChild types owner initial source = some (core, type)) :
    ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  unfold elaborateExpectedLambdaLetSpine? at accepted
  split at accepted
  · rename_i boundary
    exact .terminal boundary ((elaborateComputationReturnTree?_iff childCorrect).mp accepted)
  · rename_i notTerminal
    have head : isExpectedLambdaLetHead source = true := by
      cases equality : isExpectedLambdaLetHead source <;> simp_all
    split at accepted
    · rename_i blockSpan letSpan name annotation initializer rest
      simp only [bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨declaredType, meaning, initializerCore, initializerAccepted, tailResult, tailAccepted, resultEq⟩ := accepted
      rcases tailResult with ⟨tailCore, returnType⟩
      cases Option.some.inj resultEq
      exact .binding head (interpretStructuralType?_iff.mp meaning)
        ((elaborateExpectedComputationLambda?_iff childCorrect).mp initializerAccepted)
        (checker_sound childCorrect tailAccepted)
    · cases accepted
termination_by sizeOf source
decreasing_by subst source; simp_wf; omega

/-- Exact correspondence needs only the fixed child's checker/elaboration law. -/
theorem elaborateExpectedLambdaLetSpine?_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    elaborateExpectedLambdaLetSpine? checkChild types owner initial source = some (core, type) ↔
      ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  constructor
  · exact checker_sound childCorrect
  · intro elaboration
    induction elaboration with
    | terminal boundary body =>
        unfold elaborateExpectedLambdaLetSpine?
        simpa only [boundary, ite_true] using (elaborateComputationReturnTree?_iff childCorrect).mpr body
    | binding head meaning initializer tail ih =>
        unfold elaborateExpectedLambdaLetSpine?
        simp only [head, reduceCtorEq, ite_false, (interpretStructuralType?_iff).mpr meaning,
          bind, Option.bind_some, pure, (elaborateExpectedComputationLambda?_iff childCorrect).mpr initializer, ih]

/-- Rejection is exact absence in this opt-in profile, including unsupported true-boundary heads. -/
theorem elaborateExpectedLambdaLetSpine?_eq_none_iff
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} :
    elaborateExpectedLambdaLetSpine? checkChild types owner initial source = none ↔
      ¬ ∃ core type, ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := (elaborateExpectedLambdaLetSpine?_iff childCorrect).mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateExpectedLambdaLetSpine? checkChild types owner initial source with
    | none => rfl
    | some result => exact False.elim (absent ⟨_, _, (elaborateExpectedLambdaLetSpine?_iff childCorrect).mp accepted⟩)

/-- Core typing requires only child Core typing, not checking or runtime assumptions. -/
theorem ExpectedLambdaLetSpineElaborates.core_hasType
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type) :
    Core.HasType initial.context.values core type := by
  induction elaboration with
  | terminal boundary body => exact body.core_hasType childCoreType
  | binding head meaning initializer tail ih =>
      exact .letE (initializer.core_hasType childCoreType)
        (by simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.values, List.map_cons, Prod.snd] using ih)

/-- One-layer inversion retains either the old terminal or the exact original head and fresh tail row. -/
theorem ExpectedLambdaLetSpineElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {initial : LocalTypeInputs}
    {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ExpectedLambdaLetSpineElaborates ChildElab types owner initial source core type) :
    (isExpectedLambdaLetHead source = false ∧
      ComputationReturnTreeElaborates ChildElab types owner initial source core type) ∨
    ∃ blockSpan letSpan name annotation initializer rest declaredType initializerCore tailCore,
      isExpectedLambdaLetHead source = true ∧
      source = ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ ∧
      StructuralTypeDenotes types annotation declaredType ∧
      ExpectedComputationLambdaElaborates ChildElab types owner initial initializer initializerCore declaredType ∧
      ExpectedLambdaLetSpineElaborates ChildElab types owner
        (initial.bindFresh owner name.value declaredType) ⟨blockSpan, rest⟩ tailCore type ∧
      core = .letE initializerCore tailCore ∧
      (initial.bindFresh owner name.value declaredType).bindings =
        { name := name.value, id := Resolved.freshLocalId owner initial.ids, type := declaredType } :: initial.bindings := by
  cases elaboration with
  | terminal boundary body => exact .inl ⟨boundary, body⟩
  | binding head meaning initializer tail =>
      exact .inr ⟨_, _, _, _, _, _, _, _, _, head, rfl, meaning, initializer, tail, rfl,
        LocalTypeInputs.bindFresh_bindings _ _ _ _⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.ExpectedLambdaLetSpineTyping`
-/

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
