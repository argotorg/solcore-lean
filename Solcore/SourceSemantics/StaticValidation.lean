import Solcore.SourceSemantics.Types

/-!
Executable validation for the type-formation fragment of the declarative
source semantics.

Unlike signature-only formation, these checks allow the flexible variables
opened by a source context.  Nominal types are still accepted only as complete
applications of a data or contract declaration in the resolved catalog.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

/-- Failures reported while replaying source-level type formation. -/
inductive StaticValidationError where
  | nestingLimit (type : TypeSystem.Ty)
  | duplicateTypeParameters
  | typeParameterOwnerMismatch
      (currentDeclaration : Option Resolved.DeclarationId)
      (parameter : TypeSystem.TypeParameterId)
  | flexibleVariableOutOfScope (metavariable : TypeSystem.TypeVarId)
  | rigidParameterOutOfScope (parameter : TypeSystem.TypeParameterId)
  | unknownNominal (nominal : Resolved.DeclarationId)
  | nominalArityMismatch
      (nominal : Resolved.DeclarationId) (expected actual : Nat)
  | invalidTypeApplication (type : TypeSystem.Ty)
  | recoveryType
  | duplicateSchemeVariables
  | schemeGeneralizationMismatch
  deriving Repr, DecidableEq

/-- Erase a proof produced by an internal certified validator.  Proof erasure
keeps the public validation API executable while making success soundness a
direct consequence of construction. -/
private def eraseValidationProof {error : Type} {property : Prop} :
    Except error (PLift property) → Except error Unit
  | .error error => .error error
  | .ok _ => .ok ()

private theorem eraseValidationProof_success
    {error : Type} {property : Prop} {result : Except error (PLift property)}
    (success : eraseValidationProof result = .ok ()) : property := by
  cases result with
  | error error => simp [eraseValidationProof] at success
  | ok proof => exact proof.down

private def validateTypeParameterOwnersCertified
    (currentDeclaration : Option Resolved.DeclarationId) :
    (parameters : List TypeSystem.TypeParameterId) →
      Except StaticValidationError
        (PLift (∀ parameter ∈ parameters,
          currentDeclaration = some parameter.owner))
  | [] => .ok ⟨by simp⟩
  | parameter :: parameters =>
      if owned : currentDeclaration = some parameter.owner then
        match validateTypeParameterOwnersCertified currentDeclaration
            parameters with
        | .error error => .error error
        | .ok tailOwned => .ok ⟨by
            intro candidate member
            rcases List.mem_cons.mp member with same | member
            · subst candidate
              exact owned
            · exact tailOwned.down candidate member⟩
      else
        .error (.typeParameterOwnerMismatch currentDeclaration parameter)

private def validateTypeParameterBindersCertified (context : Context) :
    Except StaticValidationError
      (PLift (TypeParameterBindersWellFormed context)) :=
  if nodup : context.typeParameters.Nodup then
    match validateTypeParameterOwnersCertified context.currentDeclaration
        context.typeParameters with
    | .error error => .error error
    | .ok owned => .ok ⟨⟨nodup, owned.down⟩⟩
  else
    .error .duplicateTypeParameters

/-- Validate the rigid parameter row installed in a source context. -/
def validateTypeParameterBinders (context : Context) :
    Except StaticValidationError Unit :=
  eraseValidationProof (validateTypeParameterBindersCertified context)

/-- Successful rigid-parameter validation establishes the declarative binder
invariant. -/
theorem validateTypeParameterBinders_success
    {context : Context}
    (success : validateTypeParameterBinders context = .ok ()) :
    TypeParameterBindersWellFormed context := by
  apply eraseValidationProof_success
    (result := validateTypeParameterBindersCertified context)
  simpa [validateTypeParameterBinders] using success

/-- Split a left-associated type application into its head and source-order
arguments. -/
private def typeApplicationSpineAux :
    TypeSystem.Ty → List TypeSystem.Ty →
      TypeSystem.Ty × List TypeSystem.Ty
  | .application function argument, arguments =>
      typeApplicationSpineAux function (argument :: arguments)
  | head, arguments => (head, arguments)

private def typeApplicationSpine (type : TypeSystem.Ty) :
    TypeSystem.Ty × List TypeSystem.Ty :=
  typeApplicationSpineAux type []

/-- A structural budget covering every branch and nominal argument. -/
private def typeValidationFuel : TypeSystem.Ty → Nat
  | .variable _
  | .parameter _
  | .constructor _
  | .error => 1
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right =>
      typeValidationFuel left + typeValidationFuel right + 1
  | .proxy inner
  | .comptime inner => typeValidationFuel inner + 1

private theorem typeApplicationSpineAux_reconstruct
    (type : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    let result := typeApplicationSpineAux type arguments
    TypeSystem.Ty.applyMany result.1 result.2 =
      TypeSystem.Ty.applyMany type arguments := by
  induction type generalizing arguments with
  | application function argument induction =>
      simpa [typeApplicationSpineAux, TypeSystem.Ty.applyMany] using
        induction (argument :: arguments)
  | «variable» | parameter | constructor | function | product | mapping
  | proxy | comptime | error =>
      simp [typeApplicationSpineAux]

private theorem typeApplicationSpine_reconstruct
    {type head : TypeSystem.Ty} {arguments : List TypeSystem.Ty}
    (spine : typeApplicationSpine type = (head, arguments)) :
    TypeSystem.Ty.applyMany head arguments = type := by
  have reconstructed := typeApplicationSpineAux_reconstruct type []
  simp only [typeApplicationSpine] at spine
  rw [spine] at reconstructed
  simpa [TypeSystem.Ty.applyMany] using reconstructed

private theorem dataType?_eq_some_facts
    {signatures : Frontend.ProgramSignatures}
    {id : Resolved.DeclarationId}
    {dataType : Frontend.ProgramDataSignature}
    (found : signatures.dataType? id = some dataType) :
    dataType ∈ signatures.dataTypes ∧ dataType.id = id := by
  have rawFound : signatures.dataTypes.find?
      (fun candidate => decide (candidate.id = id)) = some dataType := by
    simpa [Frontend.ProgramSignatures.dataType?] using found
  have accepted : decide (dataType.id = id) = true :=
    List.find?_some
      (p := fun candidate : Frontend.ProgramDataSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem contract?_eq_some_facts
    {signatures : Frontend.ProgramSignatures}
    {id : Resolved.DeclarationId}
    {contract : Frontend.ProgramContractSignature}
    (found : signatures.contract? id = some contract) :
    contract ∈ signatures.contracts ∧ contract.id = id := by
  have rawFound : signatures.contracts.find?
      (fun candidate => decide (candidate.id = id)) = some contract := by
    simpa [Frontend.ProgramSignatures.contract?] using found
  have accepted : decide (contract.id = id) = true :=
    List.find?_some
      (p := fun candidate : Frontend.ProgramContractSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private def validateTypesWellScopedWith
    (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId)
    (validate : (type : TypeSystem.Ty) →
      Except StaticValidationError
        (PLift (TypeWellScoped context flexibleVariables type))) :
    (types : List TypeSystem.Ty) →
      Except StaticValidationError
        (PLift (TypesWellScoped context flexibleVariables types))
  | [] => .ok ⟨.nil⟩
  | head :: tail =>
      match validate head with
      | .error error => .error error
      | .ok headWellScoped =>
          match validateTypesWellScopedWith context flexibleVariables validate
              tail with
          | .error error => .error error
          | .ok tailWellScoped =>
              .ok ⟨.cons headWellScoped.down tailWellScoped.down⟩

private def validateNominalWellScopedWith
    (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId)
    (validate : (type : TypeSystem.Ty) →
      Except StaticValidationError
        (PLift (TypeWellScoped context flexibleVariables type)))
    (nominal : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty) :
    Except StaticValidationError
      (PLift (TypeWellScoped context flexibleVariables
        (TypeSystem.Ty.nominal nominal arguments))) :=
  match dataFound : context.signatures.dataType? nominal with
  | some dataType =>
      if arity : arguments.length = dataType.parameters.length then
        match validateTypesWellScopedWith context flexibleVariables validate
            arguments with
        | .error error => .error error
        | .ok argumentsWellScoped =>
            let facts := dataType?_eq_some_facts dataFound
            .ok ⟨by
              rw [← facts.2]
              exact .nominal dataType arguments facts.1 arity
                argumentsWellScoped.down⟩
      else
        .error (.nominalArityMismatch nominal dataType.parameters.length
          arguments.length)
  | none =>
      match contractFound : context.signatures.contract? nominal with
      | some contract =>
          if arity : arguments.length = contract.parameters.length then
            match validateTypesWellScopedWith context flexibleVariables
                validate arguments with
            | .error error => .error error
            | .ok argumentsWellScoped =>
                let facts := contract?_eq_some_facts contractFound
                .ok ⟨by
                  rw [← facts.2]
                  exact .contractNominal contract arguments facts.1 arity
                    argumentsWellScoped.down⟩
          else
            .error (.nominalArityMismatch nominal contract.parameters.length
              arguments.length)
      | none => .error (.unknownNominal nominal)

private def validateTypeWellScopedFuel
    (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId) :
    (fuel : Nat) → (type : TypeSystem.Ty) →
      Except StaticValidationError
        (PLift (TypeWellScoped context flexibleVariables type))
  | 0, type => .error (.nestingLimit type)
  | fuel + 1, type =>
      match typeEq : type with
      | .variable metavariable =>
          if bound : metavariable ∈ flexibleVariables then
            .ok ⟨.variable bound⟩
          else
            .error (.flexibleVariableOutOfScope metavariable)
      | .parameter parameter =>
          if bound : parameter ∈ context.typeParameters then
            if owned : context.currentDeclaration = some parameter.owner then
              .ok ⟨.parameter bound owned⟩
            else
              .error (.typeParameterOwnerMismatch
                context.currentDeclaration parameter)
          else
            .error (.rigidParameterOutOfScope parameter)
      | .constructor (.builtin builtin) => .ok ⟨.builtin builtin⟩
      | .constructor (.declaration nominal) =>
          validateNominalWellScopedWith context flexibleVariables
            (validateTypeWellScopedFuel context flexibleVariables fuel)
            nominal []
      | .application function argument =>
          match spine : typeApplicationSpine type with
          | (.constructor (.declaration nominal), arguments) =>
              match validateNominalWellScopedWith context flexibleVariables
                  (validateTypeWellScopedFuel context flexibleVariables fuel)
                  nominal arguments with
              | .error error => .error error
              | .ok wellScoped => .ok ⟨by
                  have applicationSpine :
                      typeApplicationSpine (.application function argument) =
                        (.constructor (.declaration nominal), arguments) := by
                    simpa [typeEq] using spine
                  have reconstructed :
                      TypeSystem.Ty.applyMany
                          (.constructor (.declaration nominal)) arguments =
                        .application function argument :=
                    typeApplicationSpine_reconstruct applicationSpine
                  rw [← reconstructed]
                  simpa [TypeSystem.Ty.nominal] using wellScoped.down⟩
          | _ => .error (.invalidTypeApplication type)
      | .function parameter result =>
          match validateTypeWellScopedFuel context flexibleVariables fuel
              parameter with
          | .error error => .error error
          | .ok parameterWellScoped =>
              match validateTypeWellScopedFuel context flexibleVariables fuel
                  result with
              | .error error => .error error
              | .ok resultWellScoped =>
                  .ok ⟨.function parameterWellScoped.down
                    resultWellScoped.down⟩
      | .product left right =>
          match validateTypeWellScopedFuel context flexibleVariables fuel left with
          | .error error => .error error
          | .ok leftWellScoped =>
              match validateTypeWellScopedFuel context flexibleVariables fuel
                  right with
              | .error error => .error error
              | .ok rightWellScoped =>
                  .ok ⟨.product leftWellScoped.down rightWellScoped.down⟩
      | .mapping key value =>
          match validateTypeWellScopedFuel context flexibleVariables fuel key with
          | .error error => .error error
          | .ok keyWellScoped =>
              match validateTypeWellScopedFuel context flexibleVariables fuel
                  value with
              | .error error => .error error
              | .ok valueWellScoped =>
                  .ok ⟨.mapping keyWellScoped.down valueWellScoped.down⟩
      | .proxy inner =>
          match validateTypeWellScopedFuel context flexibleVariables fuel inner with
          | .error error => .error error
          | .ok innerWellScoped => .ok ⟨.proxy innerWellScoped.down⟩
      | .comptime inner =>
          match validateTypeWellScopedFuel context flexibleVariables fuel inner with
          | .error error => .error error
          | .ok innerWellScoped => .ok ⟨.comptime innerWellScoped.down⟩
      | .error => .error .recoveryType

private def validateTypeWellScopedCertified
    (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId)
    (type : TypeSystem.Ty) :
    Except StaticValidationError
      (PLift (TypeWellScoped context flexibleVariables type)) :=
  validateTypeWellScopedFuel context flexibleVariables
    (typeValidationFuel type + 1) type

/-- Validate an open source type against an explicit flexible-variable scope.
Rigid parameters come from `context`, and nominal declarations are resolved in
`context.signatures`. -/
def validateTypeWellScoped
    (context : Context)
    (flexibleVariables : List TypeSystem.TypeVarId)
    (type : TypeSystem.Ty) : Except StaticValidationError Unit :=
  eraseValidationProof
    (validateTypeWellScopedCertified context flexibleVariables type)

/-- Successful open-type validation establishes `TypeWellScoped`. -/
theorem validateTypeWellScoped_success
    {context : Context}
    {flexibleVariables : List TypeSystem.TypeVarId}
    {type : TypeSystem.Ty}
    (success : validateTypeWellScoped context flexibleVariables type = .ok ()) :
    TypeWellScoped context flexibleVariables type := by
  apply eraseValidationProof_success
    (result := validateTypeWellScopedCertified context flexibleVariables type)
  simpa [validateTypeWellScoped] using success

private def validateTypeAdmissibleCertified
    (context : Context) (type : TypeSystem.Ty) :
    Except StaticValidationError (PLift (TypeAdmissible context type)) :=
  match validateTypeParameterBindersCertified context with
  | .error error => .error error
  | .ok binders =>
      match validateTypeWellScopedCertified context
          (admissibleTypeVariables context type) type with
      | .error error => .error error
      | .ok typeWellScoped =>
          .ok ⟨⟨binders.down, typeWellScoped.down⟩⟩

/-- Validate an occurrence type, including the context's lexical generalized
variables and optional residual-variable admission. -/
def validateTypeAdmissible (context : Context) (type : TypeSystem.Ty) :
    Except StaticValidationError Unit :=
  eraseValidationProof (validateTypeAdmissibleCertified context type)

/-- Successful occurrence-type validation establishes `TypeAdmissible`. -/
theorem validateTypeAdmissible_success
    {context : Context} {type : TypeSystem.Ty}
    (success : validateTypeAdmissible context type = .ok ()) :
    TypeAdmissible context type := by
  apply eraseValidationProof_success
    (result := validateTypeAdmissibleCertified context type)
  simpa [validateTypeAdmissible] using success

private def validateSchemeWellFormedCertified
    (context : Context) (scheme : TypeSystem.Scheme) :
    Except StaticValidationError (PLift (SchemeWellFormed context scheme)) :=
  match validateTypeParameterBindersCertified context with
  | .error error => .error error
  | .ok binders =>
      if quantifiedNodup : scheme.quantified.Nodup then
        match validateTypeWellScopedCertified context
            (admissibleTypeVariables context scheme.body ++ scheme.quantified)
            scheme.body with
        | .error error => .error error
        | .ok body =>
            .ok ⟨⟨binders.down, quantifiedNodup, body.down⟩⟩
      else
        .error .duplicateSchemeVariables

/-- Validate a rank-1 scheme in the flexible and rigid scope of a context. -/
def validateSchemeWellFormed (context : Context)
    (scheme : TypeSystem.Scheme) : Except StaticValidationError Unit :=
  eraseValidationProof (validateSchemeWellFormedCertified context scheme)

/-- Successful scheme validation establishes `SchemeWellFormed`. -/
theorem validateSchemeWellFormed_success
    {context : Context} {scheme : TypeSystem.Scheme}
    (success : validateSchemeWellFormed context scheme = .ok ()) :
    SchemeWellFormed context scheme := by
  apply eraseValidationProof_success
    (result := validateSchemeWellFormedCertified context scheme)
  simpa [validateSchemeWellFormed] using success

private def validateSchemeGeneralizesExceptCertified
    (context : Context)
    (exemptRequirements : List Frontend.SourceInference.RequirementId)
    (scheme : TypeSystem.Scheme) :
    Except StaticValidationError
      (PLift (SchemeGeneralizesExcept context exemptRequirements scheme)) :=
  if generalizes :
      scheme.quantified = scheme.body.freeVariables.filter fun metavariable =>
        !(GeneralizationBlockedVariablesExcept context exemptRequirements).contains
          metavariable then
    .ok ⟨generalizes⟩
  else
    .error .schemeGeneralizationMismatch

/-- Validate exact rank-1 generalization while omitting the requirement rows
abstracted into the scheme currently being formed. -/
def validateSchemeGeneralizesExcept
    (context : Context)
    (exemptRequirements : List Frontend.SourceInference.RequirementId)
    (scheme : TypeSystem.Scheme) : Except StaticValidationError Unit :=
  eraseValidationProof
    (validateSchemeGeneralizesExceptCertified context exemptRequirements scheme)

/-- Successful qualified-generalization validation establishes the exact
declarative generalization equation. -/
theorem validateSchemeGeneralizesExcept_success
    {context : Context}
    {exemptRequirements : List Frontend.SourceInference.RequirementId}
    {scheme : TypeSystem.Scheme}
    (success : validateSchemeGeneralizesExcept context exemptRequirements
      scheme = .ok ()) :
    SchemeGeneralizesExcept context exemptRequirements scheme := by
  apply eraseValidationProof_success
    (result := validateSchemeGeneralizesExceptCertified context
      exemptRequirements scheme)
  simpa [validateSchemeGeneralizesExcept] using success

/-- Validate ordinary rank-1 generalization with no exempt requirement rows. -/
def validateSchemeGeneralizes (context : Context)
    (scheme : TypeSystem.Scheme) : Except StaticValidationError Unit :=
  validateSchemeGeneralizesExcept context [] scheme

/-- Successful ordinary generalization validation establishes
`SchemeGeneralizes`. -/
theorem validateSchemeGeneralizes_success
    {context : Context} {scheme : TypeSystem.Scheme}
    (success : validateSchemeGeneralizes context scheme = .ok ()) :
    SchemeGeneralizes context scheme := by
  exact validateSchemeGeneralizesExcept_success (by
    simpa [validateSchemeGeneralizes] using success)

end Solcore.SourceSemantics
