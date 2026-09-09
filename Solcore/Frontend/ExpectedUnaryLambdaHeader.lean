import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Syntax.Term

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
