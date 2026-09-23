import Solcore.Frontend.StructuralType
import Solcore.Syntax.Declaration
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeParameterReferenceProperties

/-! Runtime-function headers, compilation, preparation, execution, and proof support. -/

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionHeader`
-/

/-! Explicit single-return contracts for unmodified, nongeneric runtime entries.
The one written annotation has structural meaning; parameters and lets are unchanged.
Empty/multiple return clauses are outside this profile, not invalid syntax. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RuntimeReturnTypeDenotes (types : TypeNameTable) : Option Syntax.ReturnClause → Core.Ty → Prop where
  | absent : RuntimeReturnTypeDenotes types none .unit
  | single {clauseSpan typesSpan : Syntax.SourceSpan} {annotation : Syntax.TypeExpr} {type : Core.Ty}
      (meaning : StructuralTypeDenotes types annotation type) :
      RuntimeReturnTypeDenotes types
        (some { span := clauseSpan, types := ⟨typesSpan, [annotation]⟩ }) type

def interpretRuntimeReturnType? (types : TypeNameTable) : Option Syntax.ReturnClause → Option Core.Ty
  | none => some .unit
  | some clause => match clause.types.elements with
    | [annotation] => interpretStructuralType? types annotation
    | _ => none

/-- Header shape restrictions are independent of any executable check. -/
structure RuntimeFunctionHeader (types : TypeNameTable)
    (signature : Syntax.FunctionSignature) (returnType : Core.Ty) : Prop where
  noGenerics : signature.genericParameters = none
  noWhere : signature.whereClause = none
  noPublic : signature.modifiers.publicMarker = none
  noPayable : signature.modifiers.payableMarker = none
  returnsMeaning : RuntimeReturnTypeDenotes types signature.returnsClause returnType

def interpretRuntimeFunctionHeader? (types : TypeNameTable)
    (signature : Syntax.FunctionSignature) : Option Core.Ty :=
  match signature.genericParameters, signature.whereClause,
      signature.modifiers.publicMarker, signature.modifiers.payableMarker with
  | none, none, none, none => interpretRuntimeReturnType? types signature.returnsClause
  | _, _, _, _ => none

theorem interpretRuntimeReturnType?_iff {types : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {type : Core.Ty} :
    interpretRuntimeReturnType? types clause = some type ↔ RuntimeReturnTypeDenotes types clause type := by
  constructor
  · intro accepted
    cases clause with
    | none =>
        simp only [interpretRuntimeReturnType?, Option.some.injEq] at accepted
        subst type
        exact .absent
    | some clause =>
        rcases clause with ⟨clauseSpan, ⟨typesSpan, annotations⟩⟩
        cases annotations with
        | nil => simp only [interpretRuntimeReturnType?, reduceCtorEq] at accepted
        | cons annotation rest =>
            cases rest with
            | nil => exact .single (interpretStructuralType?_sound accepted)
            | cons next rest => simp only [interpretRuntimeReturnType?, reduceCtorEq] at accepted
  · intro meaning
    cases meaning with
    | absent => rfl
    | single annotation => exact annotation.complete

theorem RuntimeReturnTypeDenotes.type_unique {types : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {left right : Core.Ty}
    (first : RuntimeReturnTypeDenotes types clause left)
    (second : RuntimeReturnTypeDenotes types clause right) : left = right :=
  Option.some.inj ((interpretRuntimeReturnType?_iff.mpr first).symm.trans
    (interpretRuntimeReturnType?_iff.mpr second))

theorem interpretRuntimeFunctionHeader?_iff {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} {type : Core.Ty} :
    interpretRuntimeFunctionHeader? types signature = some type ↔
      RuntimeFunctionHeader types signature type := by
  constructor
  · intro accepted
    rcases signature with ⟨span, name, generics, parameters, ⟨publicMarker, payableMarker⟩, returns, whereClause⟩
    cases generics <;> cases whereClause <;> cases publicMarker <;> cases payableMarker <;>
      simp only [interpretRuntimeFunctionHeader?, reduceCtorEq] at accepted
    exact ⟨rfl, rfl, rfl, rfl, interpretRuntimeReturnType?_iff.mp accepted⟩
  · intro header
    simp only [interpretRuntimeFunctionHeader?, header.noGenerics, header.noWhere,
      header.noPublic, header.noPayable]
    exact interpretRuntimeReturnType?_iff.mpr header.returnsMeaning

theorem RuntimeFunctionHeader.type_unique {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} {left right : Core.Ty}
    (first : RuntimeFunctionHeader types signature left)
    (second : RuntimeFunctionHeader types signature right) : left = right :=
  first.returnsMeaning.type_unique second.returnsMeaning

theorem interpretRuntimeFunctionHeader?_eq_none_iff {types : TypeNameTable}
    {signature : Syntax.FunctionSignature} :
    interpretRuntimeFunctionHeader? types signature = none ↔
      ¬ ∃ type, RuntimeFunctionHeader types signature type := by
  constructor
  · intro rejected ⟨type, header⟩
    have accepted := interpretRuntimeFunctionHeader?_iff.mpr header
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : interpretRuntimeFunctionHeader? types signature with
    | none => rfl
    | some type => exact False.elim (missing ⟨type, interpretRuntimeFunctionHeader?_iff.mp accepted⟩)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionCompilation`
-/

/-! Compile one restricted explicit entry without supplying argument values.
The retained Core is open in the parameter context, not a source function value. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Data only: a hand-built record does not establish compilation or typing. -/
structure CompiledRuntimeFunction where
  inputs : LocalTypeInputs
  core : Core.Expr
  returnType : Core.Ty

/-- Independent whole-entry evidence fixes the exact elaborated Core and
declared return type without assuming any runtime argument inhabitants. -/
structure RuntimeFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : TypedLetReturnTreeElaborates types owner compiled.inputs
    declaration.value.body compiled.core compiled.returnType

/-- Keep the existing header policy and check the whole recursive typed body. Retain
the actual Core only when its inferred type agrees with the return contract. -/
def compileRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateTypedLetReturnTree? types owner inputs declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionCompilationProperties`
-/

/-! Exact value-free compilation preserves the whole entry contract and types
its open Core. Neither compilation nor these laws construct runtime arguments. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    compileRuntimeFunction? types owner declaration = some compiled := by
  simp only [compileRuntimeFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
    compilation.parameters.complete, compilation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem compileRuntimeFunction?_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeFunction? types owner declaration = some compiled) :
    RuntimeFunctionCompiles types owner declaration compiled := by
  simp only [compileRuntimeFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      declareRuntimeParameters?_sound parameters, elaborateTypedLetReturnTree?_elaborates body⟩
  next => cases result

theorem compileRuntimeFunction?_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeFunction? types owner declaration = some compiled ↔
      RuntimeFunctionCompiles types owner declaration compiled :=
  ⟨compileRuntimeFunction?_sound, RuntimeFunctionCompiles.complete⟩

/-- Uniqueness follows from independent parameter and exact body evidence,
not merely from the fact that two Core expressions have the same type. -/
theorem RuntimeFunctionCompiles.result_unique {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeFunctionCompiles types owner declaration left)
    (second : RuntimeFunctionCompiles types owner declaration right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem compileRuntimeFunction?_eq_none_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} :
    compileRuntimeFunction? types owner declaration = none ↔
      ¬ ∃ compiled, RuntimeFunctionCompiles types owner declaration compiled := by
  constructor
  · intro rejected ⟨compiled, compilation⟩
    have accepted := compilation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : compileRuntimeFunction? types owner declaration with
    | none => rfl
    | some compiled => exact False.elim (missing ⟨compiled, compileRuntimeFunction?_sound accepted⟩)

/-- The actual output is typed in its parameter context. This does not close
the Core expression or supply an environment in which to execute it. -/
theorem RuntimeFunctionCompiles.core_hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.HasType (Resolved.LocalScope.values compiled.inputs.context) compiled.core compiled.returnType :=
  elaborateTypedLetReturnTree?_core_hasType compilation.body.complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionCompilationOwnerProperties`
-/

/-! Value-free compilation retains its exact Core, declared type and ordered
parameter types across owners. Identity-bearing inputs are relabeled, not equated. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Static declaration and whole recursive typed-body evidence transport directly.
No actual arguments or inhabitants of the parameter types are required. -/
theorem RuntimeFunctionCompiles.mapOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeFunctionCompiles types (mapping owner) declaration
      { compiled with inputs := (compiled.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) } := by
  refine ⟨compilation.header, compilation.parameters.map_owner mapping injective, ?_⟩
  exact compilation.body.mapOwner mapping injective

private def compilationSwapOwner
    (left right owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  if owner = left then right else if owner = right then left else owner

private theorem compilationSwapOwner_left (left right : Resolved.DeclarationId) :
    compilationSwapOwner left right left = right := by simp [compilationSwapOwner]

private theorem compilationSwapOwner_involutive (left right owner : Resolved.DeclarationId) :
    compilationSwapOwner left right (compilationSwapOwner left right owner) = owner := by
  by_cases same : left = right
  · subst right
    by_cases present : owner = left <;> simp [compilationSwapOwner, present]
  · by_cases isLeft : owner = left
    · subst owner
      simp [compilationSwapOwner, Ne.symm same]
    · by_cases isRight : owner = right
      · subst owner
        simp [compilationSwapOwner, Ne.symm same]
      · simp [compilationSwapOwner, isLeft, isRight]

private theorem compilationSwapOwner_injective (left right : Resolved.DeclarationId) :
    Function.Injective (compilationSwapOwner left right) := by
  intro first second same
  simpa only [compilationSwapOwner_involutive] using
    congrArg (compilationSwapOwner left right) same

private theorem changeCompilationOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (newOwner : Resolved.DeclarationId) :
    ∃ next, RuntimeFunctionCompiles types newOwner declaration next ∧
      next.core = compiled.core ∧ next.returnType = compiled.returnType ∧
      Resolved.LocalScope.values next.inputs.context =
        Resolved.LocalScope.values compiled.inputs.context := by
  refine ⟨{ compiled with inputs := (compiled.inputs.mapIds
    (ownerLocalIdMap (compilationSwapOwner owner newOwner))
    (ownerLocalIdMap_injective _ (compilationSwapOwner_injective owner newOwner))) },
    ?_, rfl, rfl, ?_⟩
  · simpa only [compilationSwapOwner_left] using compilation.mapOwner
      (compilationSwapOwner owner newOwner) (compilationSwapOwner_injective owner newOwner)
  · simp only [LocalTypeInputs.mapIds_context, Resolved.LocalScope.values_mapIds]

/-- The complete optional static projection agrees, including rejection.
The result does not assert equality of owner-bearing tables or compiled records. -/
theorem compileRuntimeFunction?_owner_projection_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) :
    (compileRuntimeFunction? types leftOwner declaration).map
        (fun compiled => (compiled.core, compiled.returnType,
          Resolved.LocalScope.values compiled.inputs.context)) =
      (compileRuntimeFunction? types rightOwner declaration).map
        (fun compiled => (compiled.core, compiled.returnType,
          Resolved.LocalScope.values compiled.inputs.context)) := by
  cases leftResult : compileRuntimeFunction? types leftOwner declaration with
  | none =>
      cases rightResult : compileRuntimeFunction? types rightOwner declaration with
      | none => rfl
      | some right =>
          obtain ⟨left, compilation, _, _, _⟩ :=
            changeCompilationOwner (compileRuntimeFunction?_sound rightResult) leftOwner
          have accepted := compilation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, compilation, coreEq, typeEq, valuesEq⟩ :=
        changeCompilationOwner (compileRuntimeFunction?_sound leftResult) rightOwner
      rw [compilation.complete]
      simp only [Option.map_some, coreEq, typeEq, valuesEq]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionConditionalParameterCompilationProperties`
-/

/-! Whole-entry positional selectors compile without constructing argument
values. Guard and arm positions may coincide when their annotation types agree. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {inputs : LocalTypeInputs}
  {conditionIndex thenIndex elseIndex : Nat}
  {conditionParameterSpan thenParameterSpan elseParameterSpan : Syntax.SourceSpan}
  {conditionName thenName elseName : Syntax.Identifier}
  {conditionAnnotation thenAnnotation elseAnnotation : Syntax.TypeExpr} {type : Core.Ty}
  {blockSpan ifSpan conditionSpan conditionNameSpan : Syntax.SourceSpan}
  {thenBlockSpan thenReturnSpan thenSpan thenNameSpan : Syntax.SourceSpan}
  {elseBlockSpan elseReturnSpan elseSpan elseNameSpan : Syntax.SourceSpan}

private theorem conditional_parameter_body_elaborates
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    TypedLetReturnTreeElaborates types owner inputs declaration.value.body
      (.ifE (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex))) type := by
  rw [bodyShape]
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position conditionAt
  cases actualMeaning.type_unique conditionMeaning.structural
  refine .conditional (.identifier named) ?_ (.var found)
    (.single (declared.reference_return_elaborates_at thenAt thenMeaning
      thenBlockSpan thenReturnSpan thenSpan thenNameSpan))
    (.single (declared.reference_return_elaborates_at elseAt elseMeaning
      elseBlockSpan elseReturnSpan elseSpan elseNameSpan))
  exact .var (by simpa only [LocalTypeInputs.context_ids] using indexed)

/-- All parameters and the whole header remain prerequisites, even when both
arms select the same parameter or the Bool condition is also returned. -/
theorem runtimeFunction_conditional_parameters_compiles
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    RuntimeFunctionCompiles types owner declaration
      { inputs, core := .ifE
          (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)),
        returnType := type } :=
  ⟨header, declared, conditional_parameter_body_elaborates declared conditionAt thenAt elseAt
    conditionMeaning thenMeaning elseMeaning bodyShape⟩

theorem compileRuntimeFunction?_conditional_parameters
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    compileRuntimeFunction? types owner declaration = some
      { inputs, core := .ifE
          (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)),
        returnType := type } :=
  (runtimeFunction_conditional_parameters_compiles declared conditionAt thenAt elseAt
    conditionMeaning thenMeaning elseMeaning header bodyShape).complete

/-- Existing provenance supplies the full declaration evidence. Exact body
uniqueness distinguishes the positional selector from merely equally typed Core. -/
theorem RuntimeFunctionCompiles.conditional_parameters_core
    {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    compiled.core = .ifE
        (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)) ∧
      compiled.returnType = type :=
  compilation.body.result_unique
    (conditional_parameter_body_elaborates compilation.parameters conditionAt thenAt elseAt
      conditionMeaning thenMeaning elseMeaning bodyShape)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEntry`
-/

/-! An explicitly supplied declaration, owner, type table, and typed arguments
form one restricted external entry. This does not resolve or invoke source calls. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Data only: arbitrary hand-built records receive no safety guarantee. -/
structure PreparedRuntimeFunction where
  inputs : LocalInputs
  core : Core.Expr
  returnType : Core.Ty

/-- Exact preparation provenance, independent of executable preparation.
The body evidence fixes the actual Core, not merely a Core of the same type. -/
structure RuntimeFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : TypedLetReturnTreeElaborates types owner prepared.inputs.toTypeInputs
    declaration.value.body prepared.core prepared.returnType

/-- The whole entry contract, distinct from checking the body by itself. -/
def RuntimeFunctionHasType (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (returnType : Core.Ty) : Prop :=
  ∃ inputs, RuntimeFunctionHeader types declaration.value.signature returnType ∧
    RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs ∧
    TypedLetReturnTreeHasType types owner inputs.toTypeInputs declaration.value.body returnType

/-- Retain the body checker's returned Core only when it matches the explicit
return contract. Unknown or unsupported components have no fallback meaning. -/
def prepareRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateTypedLetReturnTree? types owner inputs.toTypeInputs declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

/-- Execute exactly the prepared Core and values. Preparation is not part of
the Core fuel count, and present exhaustion remains a present result. -/
def runRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core (Resolved.LocalScope.values prepared.inputs.environment) store))

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEntryProperties`
-/

/-! Exact preparation preserves header, positional inputs, and the actual
body Core. No safety claim is made for an arbitrary prepared record. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionPrepares.complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    prepareRuntimeFunction? types owner declaration arguments = some prepared := by
  simp only [prepareRuntimeFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
    preparation.parameters.complete, preparation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem prepareRuntimeFunction?_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeFunction? types owner declaration arguments = some prepared) :
    RuntimeFunctionPrepares types owner declaration arguments prepared := by
  simp only [prepareRuntimeFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      bindRuntimeParameters?_sound parameters, elaborateTypedLetReturnTree?_elaborates body⟩
  next => cases result

theorem prepareRuntimeFunction?_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeFunction? types owner declaration arguments = some prepared ↔
      RuntimeFunctionPrepares types owner declaration arguments prepared :=
  ⟨prepareRuntimeFunction?_sound, RuntimeFunctionPrepares.complete⟩

/-- The independent relation itself determines the complete prepared record. -/
theorem RuntimeFunctionPrepares.result_unique {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : RuntimeFunctionPrepares types owner declaration arguments left)
    (second : RuntimeFunctionPrepares types owner declaration arguments right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem RuntimeFunctionPrepares.hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    RuntimeFunctionHasType types owner declaration arguments prepared.returnType :=
  ⟨prepared.inputs, preparation.header, preparation.parameters, preparation.body.hasType⟩

/-- Whole-entry typing includes declared return agreement, unlike body-only typing. -/
theorem runtimeFunctionHasType_iff_prepares {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} {returnType : Core.Ty} :
    RuntimeFunctionHasType types owner declaration arguments returnType ↔
      ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = returnType := by
  constructor
  · rintro ⟨inputs, header, parameters, typing⟩
    obtain ⟨core, body⟩ := typing.elaborates_exact
    exact ⟨⟨inputs, core, returnType⟩, ⟨header, parameters, body⟩, rfl⟩
  · rintro ⟨prepared, preparation, rfl⟩
    exact preparation.hasType

theorem prepareRuntimeFunction?_eq_none_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} :
    prepareRuntimeFunction? types owner declaration arguments = none ↔
      ¬ ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro rejected ⟨prepared, preparation⟩
    have accepted := preparation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : prepareRuntimeFunction? types owner declaration arguments with
    | none => rfl
    | some prepared => exact False.elim (missing ⟨prepared, prepareRuntimeFunction?_sound accepted⟩)

theorem RuntimeFunctionPrepares.core_hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    Core.HasType (Resolved.LocalScope.values prepared.inputs.context) prepared.core prepared.returnType := by
  simpa only [LocalInputs.toTypeInputs_context] using
    elaborateTypedLetReturnTree?_core_hasType preparation.body.complete

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEntryCost`
-/

/-! Independent cost for a complete restricted entry contract. Preparation
provenance is mandatory; a prepared record alone supplies no such meaning.
The entry wrapper adds no transitions to the return body. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RuntimeFunctionEvaluatesWithCost (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Core.Store → Core.Ty → Core.Value → Core.Store → Nat → Prop where
  | intro {prepared : PreparedRuntimeFunction} {initialStore finalStore : Core.Store}
      {value : Core.Value} {cost : Nat}
      (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
      (bodyCost : TypedLetReturnTreeEvaluatesWithCost owner prepared.inputs.names prepared.inputs.environment
        initialStore declaration.value.body value finalStore cost) :
      RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        initialStore prepared.returnType value finalStore cost

namespace RuntimeFunctionEvaluatesWithCost

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {cost : Nat}

theorem hasType (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) :
    RuntimeFunctionHasType types owner declaration arguments type := by
  cases evaluation with
  | intro preparation _ => exact preparation.hasType

theorem preserves_type (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : Core.ValueHasType value type := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      exact (bodyCost.erase.preserves_type preparation.body.hasType
        (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)
        (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.environmentTyped)).1

theorem store_eq (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : finalStore = initialStore := by
  cases evaluation with
  | intro _ bodyCost => exact bodyCost.store_eq

theorem cost_pos (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
    initialStore type value finalStore cost) : 0 < cost := by
  cases evaluation with
  | intro _ bodyCost => exact bodyCost.cost_pos

theorem deterministic {leftType rightType : Core.Ty} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore leftType left leftStore leftCost)
    (second : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore rightType right rightStore rightCost) :
    leftType = rightType ∧ left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases first with
  | intro firstPreparation firstCost =>
      cases second with
      | intro secondPreparation secondCost =>
          cases firstPreparation.result_unique secondPreparation
          exact ⟨rfl, firstCost.deterministic secondCost⟩

end RuntimeFunctionEvaluatesWithCost
end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEntryExecutionProperties`
-/

/-! Exact fixed-fuel execution of independently prepared runtime entries.
Whole header, parameter, return-type, and exact-body preparation are retained;
no safety statement applies to arbitrary prepared records without provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem aligned (inputs : LocalInputs) : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
  simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds

private theorem actualTypes (inputs : LocalInputs) :
    Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
  simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped

theorem runRuntimeFunction?_eq_some_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeFunction? types owner declaration arguments fuel store = some (type, result) ↔
      ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = type ∧ Core.runStateful fuel (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) store) = result := by
  simp only [runRuntimeFunction?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨prepared, accepted, same⟩
    cases same
    exact ⟨prepared, prepareRuntimeFunction?_iff.mp accepted, rfl, rfl⟩
  · rintro ⟨prepared, preparation, sameType, execution⟩
    exact ⟨prepared, preparation.complete, by simp only [sameType, execution]⟩

theorem RuntimeFunctionEvaluatesWithCost.run_done_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .done value finalStore) ↔ cost ≤ fuel := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      have boundary := bodyCost.checked_runStateful_done_iff preparation.body.complete
        (aligned prepared.inputs) (fuel := fuel)
      simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
        Option.some.injEq, Prod.mk.injEq, true_and] using boundary

theorem RuntimeFunctionEvaluatesWithCost.run_outOfFuel_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .outOfFuel suspended)) ↔ fuel < cost := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      have boundary := bodyCost.checked_runStateful_outOfFuel_iff preparation.body.complete
        (aligned prepared.inputs) (fuel := fuel)
      simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
        Option.some.injEq, Prod.mk.injEq, true_and] using boundary

/-- The source cost already contains the entire independent entry contract;
raw return-body cost alone does not imply entry acceptance. -/
theorem runRuntimeFunction?_done_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (type, .done value finalStore) ↔
      ∃ cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        initialStore type value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp completed
    cases sameType
    obtain ⟨cost, bodyCost, enough⟩ :=
      (elaborateTypedLetReturnTree?_run_done_iff_cost preparation.body.complete (aligned prepared.inputs)).mp execution
    exact ⟨cost, .intro preparation (by simpa only [LocalInputs.toTypeInputs_names] using bodyCost), enough⟩
  · rintro ⟨cost, evaluation, enough⟩
    exact evaluation.run_done_iff.mpr enough

theorem runRuntimeFunction?_outOfFuel_iff_cost
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel store =
      some (type, .outOfFuel suspended)) ↔
      ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store type value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp exhausted
    cases sameType
    obtain ⟨value, evaluated, _⟩ := preparation.body.hasType.evaluates
      (aligned prepared.inputs) (actualTypes prepared.inputs) store
    obtain ⟨cost, bodyCost⟩ := evaluated.exists_cost
    exact ⟨value, cost, .intro preparation (by simpa only [LocalInputs.toTypeInputs_names] using bodyCost),
      (bodyCost.checked_runStateful_outOfFuel_iff preparation.body.complete
        (aligned prepared.inputs)).mp ⟨suspended, execution⟩⟩
  · rintro ⟨value, cost, evaluation, short⟩
    exact evaluation.run_outOfFuel_iff.mpr short

/-- Whole entry typing supplies a typed result and both exact fuel boundaries.
Preparation itself contributes no Core transitions; the store is unchanged. -/
theorem RuntimeFunctionHasType.typed_cost_execution
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty}
    (typing : RuntimeFunctionHasType types owner declaration arguments type) (store : Core.Store) :
    ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store type value store cost ∧ Core.ValueHasType value type ∧ ∀ fuel,
      (runRuntimeFunction? types owner declaration arguments fuel store =
        some (type, .done value store) ↔ cost ≤ fuel) ∧
      ((∃ suspended, runRuntimeFunction? types owner declaration arguments fuel store =
        some (type, .outOfFuel suspended)) ↔ fuel < cost) := by
  obtain ⟨prepared, preparation, sameType⟩ := runtimeFunctionHasType_iff_prepares.mp typing
  cases sameType
  obtain ⟨value, evaluated, valueTyped⟩ := preparation.body.hasType.evaluates
    (aligned prepared.inputs) (actualTypes prepared.inputs) store
  obtain ⟨cost, bodyCost⟩ := evaluated.exists_cost
  have evaluation := RuntimeFunctionEvaluatesWithCost.intro preparation
    (by simpa only [LocalInputs.toTypeInputs_names] using bodyCost)
  exact ⟨value, cost, evaluation, valueTyped, fun _ =>
    ⟨evaluation.run_done_iff, evaluation.run_outOfFuel_iff⟩⟩

/-- The public entry rejects invalid preparation or executes its exact safe
Core. A hand-built prepared record alone is not a premise of this guarantee. -/
theorem runRuntimeFunction?_never_faults
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store)
    (type : Core.Ty) (error : Core.MachineFault) (faultState : Core.State) :
    runRuntimeFunction? types owner declaration arguments fuel store ≠
      some (type, .fault error faultState) := by
  intro fault
  obtain ⟨prepared, preparation, sameType, _⟩ := runRuntimeFunction?_eq_some_iff.mp fault
  cases sameType
  obtain ⟨value, cost, _, _, boundaries⟩ := preparation.hasType.typed_cost_execution store
  by_cases enough : cost ≤ fuel
  · have completed := (boundaries fuel).1.mpr enough
    rw [completed] at fault
    cases fault
  · obtain ⟨suspended, exhausted⟩ := (boundaries fuel).2.mpr (by omega)
    rw [exhausted] at fault
    cases fault

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEvaluator`
-/

/-! The existing whole-entry gate retains all header, argument and return checks.
It performs static lowering; actual result computation follows the original body
directly and never executes the prepared Core or rebinds the arguments. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Return the declared type, actual value and exact existing transition cost.
Successful preparation supplies the original parameter-only input bundle. -/
def evaluateRuntimeFunctionWithCost? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option (Core.Ty × Core.Value × Nat) := do
  let prepared ← prepareRuntimeFunction? types owner declaration arguments
  let (value, cost) ← evaluateTypedLetReturnTreeWithCost? owner
    prepared.inputs.names prepared.inputs.environment declaration.value.body
  return (prepared.returnType, value, cost)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionEvaluatorProperties`
-/

/-! Exact direct results retain the complete preparation contract. Preparation
already supplies actual typed inputs, so successful gating cannot be followed
by raw evaluation failure. No Core execution or invented argument is needed. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem evaluated_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (accepted : evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost))
    (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments store type value store cost := by
  simp only [evaluateRuntimeFunctionWithCost?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨prepared, preparedAt, ⟨actual, actualCost⟩, bodyAt, same⟩ := accepted
  cases same
  exact .intro (prepareRuntimeFunction?_sound preparedAt) (evaluateTypedLetReturnTreeWithCost?_sound bodyAt store)

private theorem evaluated_complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) :
    evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost) := by
  cases evaluation with
  | intro preparation bodyCost =>
      simp only [evaluateRuntimeFunctionWithCost?, preparation.complete,
        evaluateTypedLetReturnTreeWithCost?_complete bodyCost, bind, Option.bind_some, pure]

theorem runtimeFunctionEvaluatesWithCost_iff_evaluate
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments initialStore type value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateRuntimeFunctionWithCost? types owner declaration arguments = some (type, value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluated_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluated_sound accepted _

theorem evaluateRuntimeFunctionWithCost?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} :
    evaluateRuntimeFunctionWithCost? types owner declaration arguments = none ↔
      prepareRuntimeFunction? types owner declaration arguments = none := by
  constructor
  · intro absent
    cases preparedAt : prepareRuntimeFunction? types owner declaration arguments with
    | none => rfl
    | some prepared =>
        have preparation := prepareRuntimeFunction?_sound preparedAt
        obtain ⟨value, raw, _⟩ := preparation.body.hasType.evaluates
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.environmentTyped) []
        obtain ⟨cost, costed⟩ := raw.exists_cost
        have accepted := evaluated_complete (RuntimeFunctionEvaluatesWithCost.intro preparation
          (by simpa only [LocalInputs.toTypeInputs_names] using costed))
        rw [absent] at accepted
        cases accepted
  · intro rejected
    simp only [evaluateRuntimeFunctionWithCost?, rejected, bind, Option.bind_none]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionHeaderTypeExtensionProperties`
-/

/-! Retain complete runtime header policy while extending caller type meanings.
Absent returns still mean Unit; exact annotations retain their original types. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeReturnTypeDenotes.extend_types {old next : TypeNameTable}
    {clause : Option Syntax.ReturnClause} {type : Core.Ty}
    (meaning : RuntimeReturnTypeDenotes old clause type)
    (extension : TypeNameTable.Extends old next) : RuntimeReturnTypeDenotes next clause type := by
  cases meaning with
  | absent => exact .absent
  | single annotation => exact .single (annotation.extend_types extension)

theorem RuntimeFunctionHeader.extend_types {old next : TypeNameTable}
    {signature : Syntax.FunctionSignature} {type : Core.Ty}
    (header : RuntimeFunctionHeader old signature type)
    (extension : TypeNameTable.Extends old next) : RuntimeFunctionHeader next signature type :=
  ⟨header.noGenerics, header.noWhere, header.noPublic, header.noPayable,
    header.returnsMeaning.extend_types extension⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties`
-/

/-! Extending caller meanings preserves the complete compiled record. Exact
body provenance is retained without introducing or supplying runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles old owner declaration compiled)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionCompiles new owner declaration compiled :=
  ⟨compilation.header.extend_types extension,
    RuntimeParametersDeclare.extend_types compilation.parameters extension,
    compilation.body.extend_types extension⟩

theorem compileRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (extension : TypeNameTable.Extends old new)
    (accepted : compileRuntimeFunction? old owner declaration = some compiled) :
    compileRuntimeFunction? new owner declaration = some compiled :=
  ((compileRuntimeFunction?_sound accepted).extend_types extension).complete

/-- Both directions preserve failure as well as the exact static rows, open
Core and result type. No equality of the caller tables themselves is required. -/
theorem compileRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl) :
    compileRuntimeFunction? old owner declaration = compileRuntimeFunction? new owner declaration := by
  cases oldResult : compileRuntimeFunction? old owner declaration with
  | none =>
      cases newResult : compileRuntimeFunction? new owner declaration with
      | none => rfl
      | some compiled =>
          have preserved := compileRuntimeFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some compiled => exact (compileRuntimeFunction?_some_of_extends forward oldResult).symm

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionLocalFragmentProperties`
-/

/-! Only exact whole-entry provenance constrains a retained Core expression.
Compiled/prepared records and same-type replacements alone are not evidence.
The structural conclusion imposes no restriction on actual argument values. -/
set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.Expr.LocalFragment compiled.core :=
  compilation.body.localFragment

theorem RuntimeFunctionPrepares.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    Core.Expr.LocalFragment prepared.core :=
  preparation.body.localFragment

theorem compileRuntimeFunction?_localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeFunction? types owner declaration = some compiled) :
    Core.Expr.LocalFragment compiled.core :=
  (compileRuntimeFunction?_sound accepted).localFragment

theorem prepareRuntimeFunction?_localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeFunction? types owner declaration arguments = some prepared) :
    Core.Expr.LocalFragment prepared.core :=
  (prepareRuntimeFunction?_sound accepted).localFragment

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionOwnerProperties`
-/

/-! Owner relabeling preserves exact prepared Core and runtime values, not
the identity-bearing name tables or contexts. Arbitrary owners are connected
by an injective swap, never by overwriting every local identity's owner. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Covariance uses a globally injective owner map and leaves binder indices
unchanged. The exact Core and declared type are retained in the output record. -/
theorem RuntimeFunctionPrepares.mapOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeFunctionPrepares types (mapping owner) declaration arguments
      { prepared with inputs := (prepared.inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)) } := by
  refine ⟨preparation.header, preparation.parameters.map_owner mapping injective, ?_⟩
  simpa only [LocalInputs.toTypeInputs_mapIds] using preparation.body.mapOwner mapping injective

private def preparationSwapOwner
    (left right owner : Resolved.DeclarationId) : Resolved.DeclarationId :=
  if owner = left then right else if owner = right then left else owner

private theorem preparationSwapOwner_left (left right : Resolved.DeclarationId) :
    preparationSwapOwner left right left = right := by simp [preparationSwapOwner]

private theorem preparationSwapOwner_involutive (left right owner : Resolved.DeclarationId) :
    preparationSwapOwner left right (preparationSwapOwner left right owner) = owner := by
  by_cases same : left = right
  · subst right
    by_cases present : owner = left <;> simp [preparationSwapOwner, present]
  · by_cases isLeft : owner = left
    · subst owner
      simp [preparationSwapOwner, Ne.symm same]
    · by_cases isRight : owner = right
      · subst owner
        simp [preparationSwapOwner, Ne.symm same]
      · simp [preparationSwapOwner, isLeft, isRight]

private theorem preparationSwapOwner_injective (left right : Resolved.DeclarationId) :
    Function.Injective (preparationSwapOwner left right) := by
  intro first second same
  simpa only [preparationSwapOwner_involutive] using
    congrArg (preparationSwapOwner left right) same

private theorem changePreparationOwner {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared)
    (newOwner : Resolved.DeclarationId) :
    ∃ next, RuntimeFunctionPrepares types newOwner declaration arguments next ∧
      next.core = prepared.core ∧ next.returnType = prepared.returnType ∧
      Resolved.LocalScope.values next.inputs.environment =
        Resolved.LocalScope.values prepared.inputs.environment := by
  refine ⟨{ prepared with inputs := (prepared.inputs.mapIds
    (ownerLocalIdMap (preparationSwapOwner owner newOwner))
    (ownerLocalIdMap_injective _ (preparationSwapOwner_injective owner newOwner))) },
    ?_, rfl, rfl, ?_⟩
  · simpa only [preparationSwapOwner_left] using preparation.mapOwner
      (preparationSwapOwner owner newOwner) (preparationSwapOwner_injective owner newOwner)
  · simp only [LocalInputs.mapIds_environment, Resolved.LocalScope.values_mapIds]

/-- The optional projection preserves failure and the exact executable data.
Identity-bearing tables are related by relabeling, not equated with each other. -/
theorem prepareRuntimeFunction?_owner_projection_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeFunction? types leftOwner declaration arguments).map
        (fun prepared => (prepared.core, prepared.returnType,
          Resolved.LocalScope.values prepared.inputs.environment)) =
      (prepareRuntimeFunction? types rightOwner declaration arguments).map
        (fun prepared => (prepared.core, prepared.returnType,
          Resolved.LocalScope.values prepared.inputs.environment)) := by
  cases leftResult : prepareRuntimeFunction? types leftOwner declaration arguments with
  | none =>
      cases rightResult : prepareRuntimeFunction? types rightOwner declaration arguments with
      | none => rfl
      | some right =>
          obtain ⟨left, preparation, _, _, _⟩ :=
            changePreparationOwner (prepareRuntimeFunction?_sound rightResult) leftOwner
          have accepted := preparation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, preparation, coreEq, typeEq, valuesEq⟩ :=
        changePreparationOwner (prepareRuntimeFunction?_sound leftResult) rightOwner
      rw [preparation.complete]
      simp only [Option.map_some, coreEq, typeEq, valuesEq]

/-- Identical Core and value sequences give identical full results at the same
fuel and store, including suspended states and both-sided preparation failure. -/
theorem runRuntimeFunction?_owner_eq
    (types : TypeNameTable) (leftOwner rightOwner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types leftOwner declaration arguments fuel store =
      runRuntimeFunction? types rightOwner declaration arguments fuel store := by
  have same := prepareRuntimeFunction?_owner_projection_eq types leftOwner rightOwner declaration arguments
  cases left : prepareRuntimeFunction? types leftOwner declaration arguments <;>
    cases right : prepareRuntimeFunction? types rightOwner declaration arguments <;>
    simp_all [runRuntimeFunction?]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionParameterCompilationProperties`
-/

/-! Whole-entry compilation of a source-positioned parameter return needs no
runtime arguments. Exact body evidence, not type agreement, fixes its Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {inputs : LocalTypeInputs} {type : Core.Ty}
  {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
  {annotation : Syntax.TypeExpr} {blockSpan returnSpan span nameSpan : Syntax.SourceSpan}

private theorem parameter_body_elaboration
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    TypedLetReturnTreeElaborates types owner inputs declaration.value.body
      (.var (declaration.value.signature.parameters.elements.length - 1 - index)) type := by
  rw [bodyShape]
  exact .single
    (declared.reference_return_elaborates_at parameterAt meaning blockSpan returnSpan span nameSpan)

/-- Header and complete parameter declaration remain necessary even when the
body returns only one parameter. Its source lookup supplies the positional bound. -/
theorem runtimeFunction_parameter_compiles
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    RuntimeFunctionCompiles types owner declaration
      { inputs, core := .var (declaration.value.signature.parameters.elements.length - 1 - index),
        returnType := type } :=
  ⟨header, declared, parameter_body_elaboration declared parameterAt meaning bodyShape⟩

theorem compileRuntimeFunction?_parameter
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    compileRuntimeFunction? types owner declaration = some
      { inputs, core := .var (declaration.value.signature.parameters.elements.length - 1 - index),
        returnType := type } :=
  (runtimeFunction_parameter_compiles declared parameterAt meaning header bodyShape).complete

/-- Existing provenance already supplies the whole header and parameter list.
An equally typed alternative Core is not another result for this source body. -/
theorem RuntimeFunctionCompiles.parameter_return_core {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    compiled.core = .var (declaration.value.signature.parameters.elements.length - 1 - index) ∧
      compiled.returnType = type :=
  compilation.body.result_unique (parameter_body_elaboration compilation.parameters parameterAt meaning bodyShape)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionParameterReturnProperties`
-/

/-! Return any source-positioned runtime argument through the complete explicit
entry contract. Header and full parameter binding remain premises; neither a
selected argument nor a hand-built prepared record bypasses entry checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {inputs : LocalInputs} {index : Nat} {parameterSpan : Syntax.SourceSpan}
  {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
  {blockSpan returnSpan span nameSpan : Syntax.SourceSpan}

theorem runtimeFunction_parameter_prepares
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    RuntimeFunctionPrepares types owner declaration arguments
      { inputs, core := .var (arguments.length - 1 - index), returnType := argument.type } := by
  refine ⟨header, bound, ?_⟩
  rw [bodyShape]
  apply TypedLetReturnTreeElaborates.single
  simpa only [LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using
    (bound.reference_return_elaborates_at parameterAt argumentAt blockSpan returnSpan span nameSpan)

theorem runtimeFunction_parameter_cost
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩)
    (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      store argument.type argument.value store 1 := by
  apply RuntimeFunctionEvaluatesWithCost.intro
    (runtimeFunction_parameter_prepares bound parameterAt argumentAt header bodyShape)
  rw [bodyShape]
  exact .single (.expression (bound.reference_cost_at parameterAt argumentAt span nameSpan store))

/-- Fuel zero retains the actual Core variable and full prepared environment;
every positive fuel returns this exact argument without changing the store. -/
theorem runRuntimeFunction?_parameter
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store = some (argument.type,
      if fuel = 0 then
        .outOfFuel (Core.State.initial (.var (arguments.length - 1 - index))
          (Resolved.LocalScope.values inputs.environment) store)
      else .done argument.value store) := by
  have preparation := runtimeFunction_parameter_prepares bound parameterAt argumentAt header bodyShape
  cases fuel with
  | zero =>
      have path := (bound.reference_cost_at parameterAt argumentAt span nameSpan store).checked_toSteps
        (bound.reference_elaborates_at parameterAt argumentAt span nameSpan) inputs.sameIds
      cases path with
      | cons transition _ =>
          have advanced := Core.advance_next_iff.mpr transition
          simp only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
            Core.runStateful, advanced, ↓reduceIte]
  | succ fuel =>
      have cost := runtimeFunction_parameter_cost bound parameterAt argumentAt header bodyShape store
      simpa only [Nat.succ_ne_zero, ↓reduceIte] using
        (cost.run_done_iff (fuel := fuel + 1)).mpr (by omega)

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionPreparationFactorization`
-/

/-! Value-free compilation factors the existing runtime preparation exactly.
Reconstruction uses the supplied typed arguments, never invented inhabitants.
The type-list guard retains argument count and source order. -/

set_option autoImplicit false

namespace Solcore.Frontend

def PreparedRuntimeFunction.toCompiled (prepared : PreparedRuntimeFunction) : CompiledRuntimeFunction :=
  { inputs := prepared.inputs.toTypeInputs, core := prepared.core, returnType := prepared.returnType }

theorem RuntimeFunctionPrepares.compiles {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    RuntimeFunctionCompiles types owner declaration prepared.toCompiled := by
  exact ⟨preparation.header, preparation.parameters.erase_values, preparation.body⟩

theorem RuntimeFunctionCompiles.prepare_arguments {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse) :
    ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled := by
  obtain ⟨inputs, bound, erased⟩ := compilation.parameters.bind_typed_arguments arguments matchingTypes
  refine ⟨⟨inputs, compiled.core, compiled.returnType⟩,
    ⟨compilation.header, bound, ?_⟩, ?_⟩
  · simpa only [erased] using compilation.body
  · simp only [PreparedRuntimeFunction.toCompiled, erased]

/-- A compiled record needs independent compilation evidence as well as the
exact supplied argument types; the record alone does not imply preparation. -/
theorem runtimeFunctionPrepares_toCompiled_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {compiled : CompiledRuntimeFunction} :
    (∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
      prepared.toCompiled = compiled) ↔
    RuntimeFunctionCompiles types owner declaration compiled ∧
      arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse := by
  constructor
  · rintro ⟨prepared, preparation, rfl⟩
    refine ⟨preparation.compiles, ?_⟩
    have layout := congrArg List.reverse preparation.parameters.argument_types.symm
    simpa only [PreparedRuntimeFunction.toCompiled, LocalInputs.toTypeInputs_context,
      Resolved.LocalScope.values, LocalInputs.context, List.map_map, Function.comp_def,
      List.map_reverse, List.reverse_reverse] using layout
  · rintro ⟨compilation, matchingTypes⟩
    exact compilation.prepare_arguments arguments matchingTypes

/-- Equality includes failure: static compilation and the ordered type guard
account for every rejection of the unchanged runtime preparation endpoint. -/
theorem prepareRuntimeFunction?_factorization (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    (prepareRuntimeFunction? types owner declaration arguments).map PreparedRuntimeFunction.toCompiled =
      (do
        let compiled ← compileRuntimeFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some compiled
        else none) := by
  cases compiledResult : compileRuntimeFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
        apply prepareRuntimeFunction?_eq_none_iff.mpr
        rintro ⟨prepared, preparation⟩
        have accepted := preparation.compiles.complete
        rw [compiledResult] at accepted
        cases accepted
      simp only [rejected, Option.map_none, bind, Option.bind_none]
  | some compiled =>
      have compilation := compileRuntimeFunction?_sound compiledResult
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matching
        simp only [preparation.complete, Option.map_some, erased, bind,
          Option.bind_some, matching, ↓reduceIte]
      · have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
          apply prepareRuntimeFunction?_eq_none_iff.mpr
          rintro ⟨prepared, preparation⟩
          have erased := preparation.compiles.result_unique compilation
          exact matching (runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩).2
        simp only [rejected, Option.map_none, bind, Option.bind_some,
          matching, ↓reduceIte]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionExecutionFactorization`
-/

/-! Exact execution through value-free compilation uses the actual supplied
argument values in reverse source order. The unchanged runner retains every
stateful result, including suspended states; compilation and the ordered type
guard retain the whole entry contract. No additional runner is defined. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Independent compilation and matching typed arguments determine the complete
initial machine state, not only its inferred type or eventual return value. -/
theorem RuntimeFunctionCompiles.run_eq {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store =
      some (compiled.returnType, Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store)) := by
  obtain ⟨prepared, preparation, erased⟩ := compilation.prepare_arguments arguments matchingTypes
  have valuesEq : Resolved.LocalScope.values prepared.inputs.environment =
      arguments.reverse.map (·.value) := by
    simpa only [Resolved.LocalScope.values, LocalInputs.environment, List.map_map,
      Function.comp_def] using preparation.parameters.argument_values
  have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core erased
  have typeEq : prepared.returnType = compiled.returnType :=
    congrArg CompiledRuntimeFunction.returnType erased
  simp only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some,
    pure, valuesEq, coreEq, typeEq]

/-- Failure is exact as well: failed compilation or a mismatched ordered type
list rejects preparation, while acceptance preserves the full Core result. -/
theorem runRuntimeFunction?_factorization (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store =
      (do
        let compiled ← compileRuntimeFunction? types owner declaration
        if arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse then
          some (compiled.returnType, Core.runStateful fuel
            (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store))
        else none) := by
  cases compiledResult : compileRuntimeFunction? types owner declaration with
  | none =>
      have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
        cases preparedResult : prepareRuntimeFunction? types owner declaration arguments with
        | none => rfl
        | some prepared =>
            have projected := prepareRuntimeFunction?_factorization types owner declaration arguments
            simp only [preparedResult, Option.map_some, compiledResult, bind, Option.bind_none,
              reduceCtorEq] at projected
      simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]
  | some compiled =>
      by_cases matching : arguments.map (·.type) =
          (Resolved.LocalScope.values compiled.inputs.context).reverse
      · simpa only [bind, Option.bind_some, matching, ↓reduceIte] using
          (compileRuntimeFunction?_sound compiledResult).run_eq arguments matching fuel store
      · have rejected : prepareRuntimeFunction? types owner declaration arguments = none := by
          cases preparedResult : prepareRuntimeFunction? types owner declaration arguments with
          | none => rfl
          | some prepared =>
              have projected := prepareRuntimeFunction?_factorization types owner declaration arguments
              simp only [preparedResult, Option.map_some, compiledResult, bind, Option.bind_some,
                matching, ↓reduceIte, reduceCtorEq] at projected
        simp only [runRuntimeFunction?, rejected, bind, Option.bind_none,
          Option.bind_some, matching, ↓reduceIte]

/-- Successful optional execution has independent compilation provenance,
the exact supplied argument guard, and the exact actual Core execution. -/
theorem runRuntimeFunction?_eq_some_compiled_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {returnType : Core.Ty} {result : Core.StatefulRunResult} :
    runRuntimeFunction? types owner declaration arguments fuel store = some (returnType, result) ↔
      ∃ compiled, RuntimeFunctionCompiles types owner declaration compiled ∧
        arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse ∧
        returnType = compiled.returnType ∧
        Core.runStateful fuel (Core.State.initial compiled.core
          (arguments.reverse.map (·.value)) store) = result := by
  rw [runRuntimeFunction?_factorization]
  simp only [bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨compiled, accepted, execution⟩
    split at execution
    next matching =>
      obtain ⟨typeEq, resultEq⟩ := Prod.mk.inj (Option.some.inj execution)
      exact ⟨compiled, compileRuntimeFunction?_sound accepted, matching, typeEq.symm, resultEq⟩
    next => cases execution
  · rintro ⟨compiled, compilation, matching, typeEq, execution⟩
    exact ⟨compiled, compilation.complete, by simp only [matching, ↓reduceIte, typeEq, execution]⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionCompiledExecutionProperties`
-/

/-! Independent entry costs describe the actual compiled Core with the actual
supplied argument values. Compilation provenance remains mandatory; an arbitrary
compiled record and an argument-type match alone do not establish safety. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace RuntimeFunctionEvaluatesWithCost

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {compiled : CompiledRuntimeFunction} {initialStore finalStore : Core.Store}
  {type : Core.Ty} {value : Core.Value} {cost fuel : Nat}

/-- Cost evidence already supplies the ordered argument guard and the declared
result type for every independent compilation of this same declaration. -/
theorem compiled_contract
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    arguments.map (·.type) = (Resolved.LocalScope.values compiled.inputs.context).reverse ∧
      type = compiled.returnType := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation _ =>
      have same : prepared.toCompiled = compiled := preparation.compiles.result_unique compilation
      exact ⟨(runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, same⟩).2,
        congrArg CompiledRuntimeFunction.returnType same⟩

/-- The source cost fixes a Core path, not just a terminal observation. The
runtime environment is the reversed list of supplied values, not invented data. -/
theorem compiled_toSteps
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.Steps cost
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore)
      (Core.State.final value finalStore) := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have same : prepared.toCompiled = compiled := preparation.compiles.result_unique compilation
      have coreEq : prepared.core = compiled.core := congrArg CompiledRuntimeFunction.core same
      have valuesEq : Resolved.LocalScope.values prepared.inputs.environment =
          arguments.reverse.map (·.value) := by
        simpa only [LocalInputs.environment, Resolved.LocalScope.values, List.map_map,
          Function.comp_def] using preparation.parameters.argument_values
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      simpa only [coreEq, valuesEq] using
        bodyCost.checked_toSteps preparation.body.complete
          (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds)

theorem compiled_run_done_iff
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.runStateful fuel
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore) =
      .done value finalStore ↔ cost ≤ fuel :=
  (evaluation.compiled_toSteps compilation).runStateful_done_iff

theorem compiled_run_outOfFuel_iff
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore) =
        .outOfFuel suspended) ↔ fuel < cost :=
  (evaluation.compiled_toSteps compilation).runStateful_outOfFuel_iff

end RuntimeFunctionEvaluatesWithCost

/-- Actual typed arguments matching a proven compilation supply a typed result
and both exact compiled-Core fuel boundaries. No inhabitance is inferred from
the static parameter types, and the initial store remains arbitrary. -/
theorem RuntimeFunctionCompiles.typed_compiled_execution
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) =
      (Resolved.LocalScope.values compiled.inputs.context).reverse) (store : Core.Store) :
    ∃ value cost, RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        store compiled.returnType value store cost ∧ Core.ValueHasType value compiled.returnType ∧
      ∀ fuel,
        (Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
            .done value store ↔ cost ≤ fuel) ∧
        ((∃ suspended, Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
            .outOfFuel suspended) ↔ fuel < cost) := by
  obtain ⟨prepared, preparation, same⟩ := compilation.prepare_arguments arguments matchingTypes
  have returnEq : prepared.returnType = compiled.returnType :=
    congrArg CompiledRuntimeFunction.returnType same
  obtain ⟨value, cost, evaluation, valueTyped, _⟩ := preparation.hasType.typed_cost_execution store
  have compiledEvaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      store compiled.returnType value store cost := returnEq ▸ evaluation
  exact ⟨value, cost, compiledEvaluation, returnEq ▸ valueTyped,
    fun _ => ⟨compiledEvaluation.compiled_run_done_iff compilation,
      compiledEvaluation.compiled_run_outOfFuel_iff compilation⟩⟩

/-- Only independently compiled records receive this safety guarantee. The
argument guard checks arity and type order; it is not a substitute for provenance. -/
theorem RuntimeFunctionCompiles.compiled_never_faults
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) =
      (Resolved.LocalScope.values compiled.inputs.context).reverse)
    (fuel : Nat) (store : Core.Store) (error : Core.MachineFault) (faultState : Core.State) :
    Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) ≠
        .fault error faultState := by
  intro fault
  have entryFault := (compilation.run_eq arguments matchingTypes fuel store).trans
    (congrArg (fun result => some (compiled.returnType, result)) fault)
  exact runRuntimeFunction?_never_faults types owner declaration arguments fuel store
    compiled.returnType error faultState entryFault

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionFuelBoundProperties`
-/

/-! Source-derived fuel suffices uniformly over matching actual typed arguments.
Compilation provenance and whole entry typing remain mandatory. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionEvaluatesWithCost.cost_le_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) : cost ≤ typedLetReturnTreeFuelBound declaration.value.body := by
  cases evaluation with
  | intro _ body => exact body.cost_le_fuelBound

theorem RuntimeFunctionHasType.run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {type : Core.Ty}
    (typing : RuntimeFunctionHasType types owner declaration arguments type)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? types owner declaration arguments fuel store =
      some (type, .done value store) := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ := typing.typed_cost_execution store
  exact ⟨value, valueTyped, (boundaries fuel).1.mpr (Nat.le_trans costed.cost_le_fuelBound enough)⟩

/-- One source-computable bound applies to every matching actual argument list;
no value for an uninhabited declared type is manufactured. -/
theorem RuntimeFunctionCompiles.run_done_of_fuelBound
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (store : Core.Store) (fuel : Nat) (enough : typedLetReturnTreeFuelBound declaration.value.body ≤ fuel) :
    ∃ value, Core.ValueHasType value compiled.returnType ∧
      runRuntimeFunction? types owner declaration arguments fuel store = some (compiled.returnType, .done value store) ∧
      Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) =
        .done value store := by
  obtain ⟨value, cost, costed, valueTyped, boundaries⟩ :=
    compilation.typed_compiled_execution arguments matchingTypes store
  have bounded := Nat.le_trans costed.cost_le_fuelBound enough
  exact ⟨value, valueTyped, costed.run_done_iff.mpr bounded, (boundaries fuel).1.mpr bounded⟩

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionObservationProperties`
-/

/-! Independently compiled declarations with the same ordered Core context and
actual Core tree have identical observations on common actual arguments. Source
names, type-name tables, owners, and source ranges need not agree. -/

set_option autoImplicit false

namespace Solcore.Frontend.RuntimeFunctionCompiles

variable {leftTypes rightTypes : TypeNameTable}
  {leftOwner rightOwner : Resolved.DeclarationId}
  {leftDeclaration rightDeclaration : Syntax.FunctionDecl}
  {leftCompiled rightCompiled : CompiledRuntimeFunction}

/-- Equal return types follow from independent compilation and Core typing
uniqueness; equality of the whole static input records is not required. -/
theorem returnType_eq_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core) :
    leftCompiled.returnType = rightCompiled.returnType := by
  have rightTyping := second.core_hasType
  rw [← contextValuesEq, ← coreEq] at rightTyping
  exact Core.typing_deterministic first.core_hasType rightTyping

/-- This equality includes argument rejection and every full stateful result.
The argument list itself is shared, not merely its list of types. -/
theorem run_eq_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? leftTypes leftOwner leftDeclaration arguments fuel store =
      runRuntimeFunction? rightTypes rightOwner rightDeclaration arguments fuel store := by
  have returnTypeEq := first.returnType_eq_of_same_core second contextValuesEq coreEq
  simp only [runRuntimeFunction?_factorization, first.complete, second.complete,
    bind, Option.bind_some, contextValuesEq, coreEq, returnTypeEq]

private theorem cost_of_same_run {arguments : List TypedRuntimeArgument}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (sameRun : ∀ fuel,
      runRuntimeFunction? leftTypes leftOwner leftDeclaration arguments fuel initialStore =
        runRuntimeFunction? rightTypes rightOwner rightDeclaration arguments fuel initialStore)
    (evaluation : RuntimeFunctionEvaluatesWithCost leftTypes leftOwner leftDeclaration arguments
      initialStore type value finalStore cost) :
    RuntimeFunctionEvaluatesWithCost rightTypes rightOwner rightDeclaration arguments
      initialStore type value finalStore cost := by
  have firstDone := evaluation.run_done_iff.mpr (Nat.le_refl cost)
  have secondDone := (sameRun cost).symm.trans firstDone
  obtain ⟨otherCost, otherEvaluation, otherBound⟩ := runRuntimeFunction?_done_iff_cost.mp secondDone
  have secondAtOwnCost := otherEvaluation.run_done_iff.mpr (Nat.le_refl otherCost)
  have firstAtOtherCost := (sameRun otherCost).trans secondAtOwnCost
  have originalBound : cost ≤ otherCost := evaluation.run_done_iff.mp firstAtOtherCost
  have sameCost : otherCost = cost := Nat.le_antisymm otherBound originalBound
  exact sameCost ▸ otherEvaluation

/-- Two exact completion thresholds recover the identical independent cost.
The result type, value, both stores, and supplied arguments remain fixed; no
additional typing, termination, or argument-acceptance premise is introduced. -/
theorem cost_iff_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core)
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost leftTypes leftOwner leftDeclaration arguments
        initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost rightTypes rightOwner rightDeclaration arguments
        initialStore type value finalStore cost := by
  constructor
  · exact cost_of_same_run
      (fun fuel => first.run_eq_of_same_core second contextValuesEq coreEq arguments fuel initialStore)
  · exact cost_of_same_run
      (fun fuel => (first.run_eq_of_same_core second contextValuesEq coreEq arguments fuel initialStore).symm)

end Solcore.Frontend.RuntimeFunctionCompiles

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionResumptionProperties`
-/

/-! Complete entry checkpoints resume their actual Core state. Exact source
costs retain whole preparation, and compiled paths retain compilation provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem runRuntimeFunction?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : runRuntimeFunction? types owner declaration arguments spent store =
      some (type, .outOfFuel checkpoint)) (additional : Nat) :
    runRuntimeFunction? types owner declaration arguments (spent + additional) store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨prepared, preparation, sameType, execution⟩ := runRuntimeFunction?_eq_some_iff.mp exhausted
  exact runRuntimeFunction?_eq_some_iff.mpr
    ⟨prepared, preparation, sameType, (Core.runStateful_resume execution additional).symm⟩

theorem RuntimeFunctionEvaluatesWithCost.residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost spent : Nat} {checkpoint : Core.State}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    (exhausted : runRuntimeFunction? types owner declaration arguments spent initialStore =
      some (type, .outOfFuel checkpoint)) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) := by
  cases evaluation with
  | @intro prepared _ _ _ _ preparation bodyCost =>
      have execution : Core.runStateful spent (Core.State.initial prepared.core
          (Resolved.LocalScope.values prepared.inputs.environment) initialStore) = .outOfFuel checkpoint := by
        simpa only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
          Option.some.injEq, Prod.mk.injEq, true_and] using exhausted
      rw [← LocalInputs.toTypeInputs_names prepared.inputs] at bodyCost
      exact bodyCost.checked_residual_of_outOfFuel preparation.body.complete
        (by simpa only [LocalInputs.toTypeInputs_context] using prepared.inputs.sameIds) execution

theorem RuntimeFunctionEvaluatesWithCost.compiled_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost spent : Nat} {checkpoint : Core.State}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost)
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (exhausted : Core.runStateful spent (Core.State.initial compiled.core
      (arguments.reverse.map (·.value)) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.compiled_toSteps compilation).residual_of_outOfFuel exhausted

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionStaticProperties`
-/

/-! Equal ordered argument types preserve exact static preparation, including
failure. Runtime environments, results, suspended states, and costs may differ. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionPrepares.transport_argument_types {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {leftArguments rightArguments : List TypedRuntimeArgument} {left : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration leftArguments left)
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    ∃ right, RuntimeFunctionPrepares types owner declaration rightArguments right ∧
      right.inputs.ids = left.inputs.ids ∧ right.inputs.names = left.inputs.names ∧
      right.inputs.context = left.inputs.context ∧ right.core = left.core ∧
      right.returnType = left.returnType := by
  obtain ⟨rightInputs, parameters, namesEq, contextEq⟩ :=
    preparation.parameters.transport_types (rightInitial := .empty) rfl rfl sameArgumentTypes
  have idsEq : rightInputs.ids = left.inputs.ids := by
    rw [← LocalInputs.context_ids, ← LocalInputs.context_ids, contextEq]
  have erased : rightInputs.toTypeInputs = left.inputs.toTypeInputs :=
    parameters.erase_values.result_unique preparation.parameters.erase_values
  have body : TypedLetReturnTreeElaborates types owner rightInputs.toTypeInputs declaration.value.body
      left.core left.returnType := by
    rw [erased]
    exact preparation.body
  exact ⟨⟨rightInputs, left.core, left.returnType⟩, ⟨preparation.header, parameters, body⟩,
    idsEq, namesEq, contextEq, rfl, rfl⟩

/-- `Option` equality includes both-sided rejection; successful results retain
their exact static projections without equating the prepared runtime values. -/
theorem prepareRuntimeFunction?_static_projection_eq {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {leftArguments rightArguments : List TypedRuntimeArgument}
    (sameArgumentTypes : leftArguments.map (·.type) = rightArguments.map (·.type)) :
    (prepareRuntimeFunction? types owner declaration leftArguments).map
        (fun prepared => (prepared.inputs.ids, prepared.inputs.names, prepared.inputs.context,
          prepared.core, prepared.returnType)) =
      (prepareRuntimeFunction? types owner declaration rightArguments).map
        (fun prepared => (prepared.inputs.ids, prepared.inputs.names, prepared.inputs.context,
          prepared.core, prepared.returnType)) := by
  cases leftResult : prepareRuntimeFunction? types owner declaration leftArguments with
  | none =>
      cases rightResult : prepareRuntimeFunction? types owner declaration rightArguments with
      | none => rfl
      | some right =>
          obtain ⟨left, preparation, _⟩ :=
            (prepareRuntimeFunction?_sound rightResult).transport_argument_types sameArgumentTypes.symm
          have accepted := preparation.complete
          rw [leftResult] at accepted
          cases accepted
  | some left =>
      obtain ⟨right, preparation, idsEq, namesEq, contextEq, coreEq, typeEq⟩ :=
        (prepareRuntimeFunction?_sound leftResult).transport_argument_types sameArgumentTypes
      rw [preparation.complete]
      simp only [Option.map_some, idsEq, namesEq, contextEq, coreEq, typeEq]

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionStoreProperties`
-/

/-! Store-independent values and exact costs lift through recursive-body and
whole-entry contracts. Full results are not equated: each retains its own store. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionEvaluatesWithCost.change_store
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      initialStore type value finalStore cost) (replacement : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments replacement type value replacement cost := by
  cases evaluation with
  | intro preparation body => exact .intro preparation (body.change_store replacement)

theorem runtimeFunctionEvaluatesWithCost_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {initialStore finalStore replacement : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments initialStore type value finalStore cost ↔
      finalStore = initialStore ∧ RuntimeFunctionEvaluatesWithCost types owner declaration arguments
        replacement type value replacement cost := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluation.change_store replacement⟩
  · rintro ⟨rfl, evaluation⟩
    exact evaluation.change_store _

/-- Values agree at the same fuel, but each completed result carries its own
initial store. This includes cases where preparation rejects on both sides. -/
theorem runRuntimeFunction?_done_store_iff
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (leftStore rightStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) :
    runRuntimeFunction? types owner declaration arguments fuel leftStore = some (type, .done value leftStore) ↔
      runRuntimeFunction? types owner declaration arguments fuel rightStore = some (type, .done value rightStore) := by
  rw [runRuntimeFunction?_done_iff_cost, runRuntimeFunction?_done_iff_cost]
  constructor
  · rintro ⟨cost, evaluation, enough⟩
    exact ⟨cost, evaluation.change_store rightStore, enough⟩
  · rintro ⟨cost, evaluation, enough⟩
    exact ⟨cost, evaluation.change_store leftStore, enough⟩

/-- The corresponding suspended states are existential and are not equated. -/
theorem runRuntimeFunction?_outOfFuel_store_iff
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (leftStore rightStore : Core.Store) (type : Core.Ty) :
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel leftStore =
      some (type, .outOfFuel suspended)) ↔
    (∃ suspended, runRuntimeFunction? types owner declaration arguments fuel rightStore =
      some (type, .outOfFuel suspended)) := by
  rw [runRuntimeFunction?_outOfFuel_iff_cost, runRuntimeFunction?_outOfFuel_iff_cost]
  constructor
  · rintro ⟨value, cost, evaluation, short⟩
    exact ⟨value, cost, evaluation.change_store rightStore, short⟩
  · rintro ⟨value, cost, evaluation, short⟩
    exact ⟨value, cost, evaluation.change_store leftStore, short⟩

theorem RuntimeFunctionCompiles.compiled_done_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (fuel : Nat) (leftStore rightStore : Core.Store) (value : Core.Value) :
    Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) leftStore) =
      .done value leftStore ↔
    Core.runStateful fuel (Core.State.initial compiled.core (arguments.reverse.map (·.value)) rightStore) =
      .done value rightStore := by
  have same := runRuntimeFunction?_done_store_iff types owner declaration arguments fuel leftStore rightStore
    compiled.returnType value
  simpa only [compilation.run_eq arguments matchingTypes, Option.some.injEq, Prod.mk.injEq, true_and] using same

theorem RuntimeFunctionCompiles.compiled_outOfFuel_store_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {compiled : CompiledRuntimeFunction} (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (arguments : List TypedRuntimeArgument)
    (matchingTypes : arguments.map (·.type) = compiled.inputs.context.values.reverse)
    (fuel : Nat) (leftStore rightStore : Core.Store) :
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) leftStore) = .outOfFuel suspended) ↔
    (∃ suspended, Core.runStateful fuel
      (Core.State.initial compiled.core (arguments.reverse.map (·.value)) rightStore) = .outOfFuel suspended) := by
  have same := runRuntimeFunction?_outOfFuel_store_iff types owner declaration arguments fuel leftStore rightStore
    compiled.returnType
  simpa only [compilation.run_eq arguments matchingTypes, Option.some.injEq, Prod.mk.injEq, true_and] using same

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeFunctionTypeExtensionProperties`
-/

/-! Meaning-preserving extension retains the complete actual prepared record
and every successful run result. Mutual extension also retains rejection. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Transport exact provenance with the same original declaration and actual
arguments. No erased projection is used to identify value-bearing records. -/
theorem RuntimeFunctionPrepares.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares old owner declaration arguments prepared)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionPrepares new owner declaration arguments prepared :=
  ⟨preparation.header.extend_types extension,
    RuntimeParametersBind.extend_types preparation.parameters extension,
    preparation.body.extend_types extension⟩

theorem RuntimeFunctionHasType.extend_types {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {returnType : Core.Ty}
    (typing : RuntimeFunctionHasType old owner declaration arguments returnType)
    (extension : TypeNameTable.Extends old new) :
    RuntimeFunctionHasType new owner declaration arguments returnType := by
  obtain ⟨inputs, header, parameters, body⟩ := typing
  exact ⟨inputs, header.extend_types extension,
    RuntimeParametersBind.extend_types parameters extension, body.extend_types extension⟩

theorem prepareRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {prepared : PreparedRuntimeFunction}
    (extension : TypeNameTable.Extends old new)
    (accepted : prepareRuntimeFunction? old owner declaration arguments = some prepared) :
    prepareRuntimeFunction? new owner declaration arguments = some prepared :=
  ((prepareRuntimeFunction?_sound accepted).extend_types extension).complete

/-- Equality includes absence and the actual input values, not just the
compiled Core, declared return type or argument type list. -/
theorem prepareRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) :
    prepareRuntimeFunction? old owner declaration arguments =
      prepareRuntimeFunction? new owner declaration arguments := by
  cases oldResult : prepareRuntimeFunction? old owner declaration arguments with
  | none =>
      cases newResult : prepareRuntimeFunction? new owner declaration arguments with
      | none => rfl
      | some prepared =>
          have preserved := prepareRuntimeFunction?_some_of_extends backward newResult
          rw [oldResult] at preserved
          cases preserved
  | some prepared => exact (prepareRuntimeFunction?_some_of_extends forward oldResult).symm

/-- Present exhaustion is preserved with its full saved state, just as every
other present outcome is. There is no extra work or change to the caller store. -/
theorem runRuntimeFunction?_some_of_extends {old new : TypeNameTable}
    {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl}
    {arguments : List TypedRuntimeArgument} {fuel : Nat} {store : Core.Store}
    {outcome : Core.Ty × Core.StatefulRunResult}
    (extension : TypeNameTable.Extends old new)
    (accepted : runRuntimeFunction? old owner declaration arguments fuel store = some outcome) :
    runRuntimeFunction? new owner declaration arguments fuel store = some outcome := by
  cases preparedResult : prepareRuntimeFunction? old owner declaration arguments with
  | none => simp only [runRuntimeFunction?, preparedResult, bind, Option.bind_none,
      reduceCtorEq] at accepted
  | some prepared =>
      have preserved := prepareRuntimeFunction?_some_of_extends extension preparedResult
      simpa only [runRuntimeFunction?, preparedResult, preserved] using accepted

theorem runRuntimeFunction?_eq_of_mutual_extends {old new : TypeNameTable}
    (forward : TypeNameTable.Extends old new) (backward : TypeNameTable.Extends new old)
    (owner : Resolved.DeclarationId) (declaration : Syntax.FunctionDecl)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? old owner declaration arguments fuel store =
      runRuntimeFunction? new owner declaration arguments fuel store := by
  simp only [runRuntimeFunction?,
    prepareRuntimeFunction?_eq_of_mutual_extends forward backward owner declaration arguments]

end Solcore.Frontend
