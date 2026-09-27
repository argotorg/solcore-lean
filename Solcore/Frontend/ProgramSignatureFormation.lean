import Solcore.Frontend.ProgramSignatures

/-!
Executable formation validation for a completed resolved signature catalog.

This pass deliberately runs after `buildProgramSignatures`: transparent type
aliases have already disappeared, and nominal and trait heads can be checked
against the complete data, contract, and trait catalogs.  The propositions in
this module are frontend-only witnesses; the algorithm-independent source
semantics converts them at its checker boundary.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Failures found while validating types and predicates in a completed
signature catalog.  The owning declaration is retained even when the invalid
node came from a nested method or constructor signature. -/
inductive ProgramSignatureFormationError where
  | nestingLimit
      (owner : Resolved.DeclarationId) (type : TypeSystem.Ty)
  | flexibleVariable
      (owner : Resolved.DeclarationId) (metavariable : TypeSystem.TypeVarId)
  | rigidParameterOutOfScope
      (owner : Resolved.DeclarationId)
      (parameter : TypeSystem.TypeParameterId)
  | rigidParameterOwnerMismatch
      (owner : Resolved.DeclarationId)
      (parameter : TypeSystem.TypeParameterId)
  | unknownNominal
      (owner nominal : Resolved.DeclarationId)
  | nominalArityMismatch
      (owner nominal : Resolved.DeclarationId)
      (expected actual : Nat)
  | invalidApplication
      (owner : Resolved.DeclarationId) (type : TypeSystem.Ty)
  | recoveryType (owner : Resolved.DeclarationId)
  | unknownTrait
      (owner trait : Resolved.DeclarationId)
  | traitArityMismatch
      (owner : Resolved.DeclarationId) (trait : ProgramTraitId)
      (expected actual : Nat)
  deriving Repr, DecidableEq

mutual

  /-- A resolved signature type is closed over precisely its declaration's
  rigid parameter row and uses only exactly applied cataloged nominals. -/
  inductive SignatureTypeFormationValidated
      (signatures : ProgramSignatures)
      (owner : Resolved.DeclarationId)
      (parameters : List TypeSystem.TypeParameterId) :
      TypeSystem.Ty → Prop where
    | parameter
        {parameter : TypeSystem.TypeParameterId}
        (bound : parameter ∈ parameters)
        (owned : parameter.owner = owner) :
        SignatureTypeFormationValidated signatures owner parameters
          (.parameter parameter)
    | builtin (builtin : TypeSystem.BuiltinType) :
        SignatureTypeFormationValidated signatures owner parameters
          (.constructor (.builtin builtin))
    | dataNominal
        (dataType : ProgramDataSignature) (arguments : List TypeSystem.Ty)
        (cataloged : dataType ∈ signatures.dataTypes)
        (arity : arguments.length = dataType.parameters.length)
        (argumentsValidated :
          SignatureTypesFormationValidated signatures owner parameters arguments) :
        SignatureTypeFormationValidated signatures owner parameters
          (TypeSystem.Ty.nominal dataType.id arguments)
    | contractNominal
        (contract : ProgramContractSignature) (arguments : List TypeSystem.Ty)
        (cataloged : contract ∈ signatures.contracts)
        (arity : arguments.length = contract.parameters.length)
        (argumentsValidated :
          SignatureTypesFormationValidated signatures owner parameters arguments) :
        SignatureTypeFormationValidated signatures owner parameters
          (TypeSystem.Ty.nominal contract.id arguments)
    | function
        {parameter result : TypeSystem.Ty}
        (parameterValidated :
          SignatureTypeFormationValidated signatures owner parameters parameter)
        (resultValidated :
          SignatureTypeFormationValidated signatures owner parameters result) :
        SignatureTypeFormationValidated signatures owner parameters
          (.function parameter result)
    | product
        {left right : TypeSystem.Ty}
        (leftValidated :
          SignatureTypeFormationValidated signatures owner parameters left)
        (rightValidated :
          SignatureTypeFormationValidated signatures owner parameters right) :
        SignatureTypeFormationValidated signatures owner parameters
          (.product left right)
    | mapping
        {key value : TypeSystem.Ty}
        (keyValidated :
          SignatureTypeFormationValidated signatures owner parameters key)
        (valueValidated :
          SignatureTypeFormationValidated signatures owner parameters value) :
        SignatureTypeFormationValidated signatures owner parameters
          (.mapping key value)
    | proxy
        {inner : TypeSystem.Ty}
        (innerValidated :
          SignatureTypeFormationValidated signatures owner parameters inner) :
        SignatureTypeFormationValidated signatures owner parameters (.proxy inner)
    | comptime
        {inner : TypeSystem.Ty}
        (innerValidated :
          SignatureTypeFormationValidated signatures owner parameters inner) :
        SignatureTypeFormationValidated signatures owner parameters
          (.comptime inner)

  /-- Source-order companion for a row of validated signature types. -/
  inductive SignatureTypesFormationValidated
      (signatures : ProgramSignatures)
      (owner : Resolved.DeclarationId)
      (parameters : List TypeSystem.TypeParameterId) :
      List TypeSystem.Ty → Prop where
    | nil : SignatureTypesFormationValidated signatures owner parameters []
    | cons
        {head : TypeSystem.Ty} {tail : List TypeSystem.Ty}
        (headValidated :
          SignatureTypeFormationValidated signatures owner parameters head)
        (tailValidated :
          SignatureTypesFormationValidated signatures owner parameters tail) :
        SignatureTypesFormationValidated signatures owner parameters
          (head :: tail)

end

/-- A resolved predicate has closed component types and names a trait at its
exact total arity, including the distinguished subject position. -/
structure SignaturePredicateFormationValidated
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (predicate : ProgramPredicate) : Prop where
  subject : SignatureTypeFormationValidated signatures owner parameters
    predicate.subject
  arguments : SignatureTypesFormationValidated signatures owner parameters
    predicate.arguments
  trait : match predicate.trait with
    | .builtin .int => predicate.arguments = []
    | .declaration id =>
        ∃ signature ∈ signatures.traits,
          signature.id = id ∧
          predicate.arguments.length + 1 = signature.parameters.length

/-- Pointwise formation of a source-ordered predicate row. -/
def SignaturePredicatesFormationValidated
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (predicates : List ProgramPredicate) : Prop :=
  ∀ predicate, predicate ∈ predicates →
    SignaturePredicateFormationValidated signatures owner parameters predicate

/-- Every type and predicate retained in the directly resolved signature
catalog is formed in its declaration's rigid scope.  Implementation methods
are intentionally absent: their formation follows from the corresponding
trait method under the already validated implementation-head substitution. -/
structure ProgramSignatureFormationValidated
    (signatures : ProgramSignatures) : Prop where
  functions : ∀ signature, signature ∈ signatures.functions →
    SignatureTypesFormationValidated signatures signature.id
        signature.scheme.parameters signature.parameterTypes ∧
      SignatureTypesFormationValidated signatures signature.id
        signature.scheme.parameters signature.returnTypes ∧
      SignaturePredicatesFormationValidated signatures signature.id
        signature.scheme.parameters signature.scheme.predicates
  dataTypes : ∀ signature, signature ∈ signatures.dataTypes →
    ∀ constructor, constructor ∈ signature.constructors →
      SignatureTypesFormationValidated signatures signature.id
        signature.parameters constructor.payloadTypes
  traits : ∀ signature, signature ∈ signatures.traits →
    SignaturePredicatesFormationValidated signatures signature.id
        signature.parameters signature.wherePredicates ∧
      ∀ method, method ∈ signature.methods →
        SignatureTypesFormationValidated signatures signature.id
            signature.parameters method.parameterTypes ∧
          SignatureTypesFormationValidated signatures signature.id
            signature.parameters method.returnTypes ∧
          SignaturePredicatesFormationValidated signatures signature.id
            signature.parameters method.wherePredicates
  implementations : ∀ signature, signature ∈ signatures.implementations →
    SignaturePredicateFormationValidated signatures signature.id
        signature.parameters signature.head ∧
      SignaturePredicatesFormationValidated signatures signature.id
        signature.parameters signature.wherePredicates

private def validateAll {value error : Type}
    (validate : value → Except error Unit) : List value → Except error Unit
  | [] => .ok ()
  | head :: tail =>
      match validate head with
      | .error error => .error error
      | .ok () => validateAll validate tail

/-- Split one left-associated application into its head and source-order
arguments. -/
private def signatureTypeApplicationSpineAux :
    TypeSystem.Ty → List TypeSystem.Ty →
      TypeSystem.Ty × List TypeSystem.Ty
  | .application function argument, arguments =>
      signatureTypeApplicationSpineAux function (argument :: arguments)
  | head, arguments => (head, arguments)

private def signatureTypeApplicationSpine (type : TypeSystem.Ty) :
    TypeSystem.Ty × List TypeSystem.Ty :=
  signatureTypeApplicationSpineAux type []

/-- A structural budget large enough for every branch and every argument of a
resolved type. -/
private def signatureTypeFuel : TypeSystem.Ty → Nat
  | .variable _
  | .parameter _
  | .constructor _
  | .error => 1
  | .application left right
  | .function left right
  | .product left right
  | .mapping left right => signatureTypeFuel left + signatureTypeFuel right + 1
  | .proxy inner
  | .comptime inner => signatureTypeFuel inner + 1

private def validateSignatureNominalWith
    (validate : TypeSystem.Ty →
      Except ProgramSignatureFormationError Unit)
    (signatures : ProgramSignatures)
    (owner nominal : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty) :
    Except ProgramSignatureFormationError Unit :=
  match signatures.dataType? nominal with
  | some dataType =>
      if arguments.length = dataType.parameters.length then
        validateAll validate arguments
      else
        .error (.nominalArityMismatch owner nominal
          dataType.parameters.length arguments.length)
  | none =>
      match signatures.contract? nominal with
      | some contract =>
          if arguments.length = contract.parameters.length then
            validateAll validate arguments
          else
            .error (.nominalArityMismatch owner nominal
              contract.parameters.length arguments.length)
      | none => .error (.unknownNominal owner nominal)

private def validateSignatureTypeFuel
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId) :
    Nat → TypeSystem.Ty → Except ProgramSignatureFormationError Unit
  | 0, type => .error (.nestingLimit owner type)
  | fuel + 1, type =>
      match type with
      | .variable metavariable =>
          .error (.flexibleVariable owner metavariable)
      | .parameter parameter =>
          if parameter ∈ parameters then
            if parameter.owner = owner then .ok ()
            else .error (.rigidParameterOwnerMismatch owner parameter)
          else
            .error (.rigidParameterOutOfScope owner parameter)
      | .constructor (.builtin _) => .ok ()
      | .constructor (.declaration nominal) =>
          validateSignatureNominalWith
            (validateSignatureTypeFuel signatures owner parameters fuel)
            signatures owner nominal []
      | .application _ _ =>
          match signatureTypeApplicationSpine type with
          | (.constructor (.declaration nominal), arguments) =>
              validateSignatureNominalWith
                (validateSignatureTypeFuel signatures owner parameters fuel)
                signatures owner nominal arguments
          | _ => .error (.invalidApplication owner type)
      | .function parameter result =>
          match validateSignatureTypeFuel signatures owner parameters fuel
              parameter with
          | .error error => .error error
          | .ok () =>
              validateSignatureTypeFuel signatures owner parameters fuel result
      | .product left right =>
          match validateSignatureTypeFuel signatures owner parameters fuel left with
          | .error error => .error error
          | .ok () =>
              validateSignatureTypeFuel signatures owner parameters fuel right
      | .mapping key value =>
          match validateSignatureTypeFuel signatures owner parameters fuel key with
          | .error error => .error error
          | .ok () =>
              validateSignatureTypeFuel signatures owner parameters fuel value
      | .proxy inner =>
          validateSignatureTypeFuel signatures owner parameters fuel inner
      | .comptime inner =>
          validateSignatureTypeFuel signatures owner parameters fuel inner
      | .error => .error (.recoveryType owner)

private def validateSignatureType
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) : Except ProgramSignatureFormationError Unit :=
  validateSignatureTypeFuel signatures owner parameters
    (signatureTypeFuel type + 1) type

/-- Validate one already-resolved type against a completed signature catalog
and an explicit rigid-parameter scope.  Source-body annotation checking uses
this public boundary after name resolution. -/
def validateResolvedTypeFormation
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) : Except ProgramSignatureFormationError Unit :=
  validateSignatureType signatures owner parameters type

private def validateSignatureTypes
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (types : List TypeSystem.Ty) : Except ProgramSignatureFormationError Unit :=
  validateAll (validateSignatureType signatures owner parameters) types

private def validateSignaturePredicate
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (predicate : ProgramPredicate) :
    Except ProgramSignatureFormationError Unit :=
  match validateSignatureType signatures owner parameters predicate.subject with
  | .error error => .error error
  | .ok () =>
      match validateSignatureTypes signatures owner parameters
          predicate.arguments with
      | .error error => .error error
      | .ok () =>
          match predicate.trait with
          | .builtin .int =>
              if predicate.arguments.isEmpty then .ok ()
              else .error (.traitArityMismatch owner predicate.trait 1
                (predicate.arguments.length + 1))
          | .declaration traitId =>
              match signatures.trait? traitId with
              | none => .error (.unknownTrait owner traitId)
              | some trait =>
                  if predicate.arguments.length + 1 = trait.parameters.length then
                    .ok ()
                  else
                    .error (.traitArityMismatch owner predicate.trait
                      trait.parameters.length (predicate.arguments.length + 1))

private def validateSignaturePredicates
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (predicates : List ProgramPredicate) :
    Except ProgramSignatureFormationError Unit :=
  validateAll
    (validateSignaturePredicate signatures owner parameters) predicates

private def validateFunctionSignatureFormation
    (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature) :
    Except ProgramSignatureFormationError Unit :=
  match validateSignatureTypes signatures signature.id
      signature.scheme.parameters signature.parameterTypes with
  | .error error => .error error
  | .ok () =>
      match validateSignatureTypes signatures signature.id
          signature.scheme.parameters signature.returnTypes with
      | .error error => .error error
      | .ok () =>
          validateSignaturePredicates signatures signature.id
            signature.scheme.parameters signature.scheme.predicates

private def validateDataSignatureFormation
    (signatures : ProgramSignatures)
    (signature : ProgramDataSignature) :
    Except ProgramSignatureFormationError Unit :=
  validateAll (fun constructor =>
    validateSignatureTypes signatures signature.id signature.parameters
      constructor.payloadTypes) signature.constructors

private def validateTraitMethodSignatureFormation
    (signatures : ProgramSignatures)
    (trait : ProgramTraitSignature)
    (method : ProgramTraitMethodSignature) :
    Except ProgramSignatureFormationError Unit :=
  match validateSignatureTypes signatures trait.id trait.parameters
      method.parameterTypes with
  | .error error => .error error
  | .ok () =>
      match validateSignatureTypes signatures trait.id trait.parameters
          method.returnTypes with
      | .error error => .error error
      | .ok () =>
          validateSignaturePredicates signatures trait.id trait.parameters
            method.wherePredicates

private def validateTraitSignatureFormation
    (signatures : ProgramSignatures)
    (signature : ProgramTraitSignature) :
    Except ProgramSignatureFormationError Unit :=
  match validateSignaturePredicates signatures signature.id
      signature.parameters signature.wherePredicates with
  | .error error => .error error
  | .ok () =>
      validateAll
        (validateTraitMethodSignatureFormation signatures signature)
        signature.methods

private def validateImplementationSignatureFormation
    (signatures : ProgramSignatures)
    (signature : ProgramImplementationSignature) :
    Except ProgramSignatureFormationError Unit :=
  match validateSignaturePredicate signatures signature.id signature.parameters
      signature.head with
  | .error error => .error error
  | .ok () =>
      validateSignaturePredicates signatures signature.id signature.parameters
        signature.wherePredicates

private def validateProgramSignatureFormationAux
    (signatures : ProgramSignatures) :
    Except ProgramSignatureFormationError Unit :=
  match validateAll (validateFunctionSignatureFormation signatures)
      signatures.functions with
  | .error error => .error error
  | .ok () =>
      match validateAll (validateDataSignatureFormation signatures)
          signatures.dataTypes with
      | .error error => .error error
      | .ok () =>
          match validateAll (validateTraitSignatureFormation signatures)
              signatures.traits with
          | .error error => .error error
          | .ok () =>
              validateAll (validateImplementationSignatureFormation signatures)
                signatures.implementations

/-- Validate every directly resolved type and predicate in a completed
signature catalog.  Validation is stable and fail-fast in category, signature,
and field source order; signature-construction failures still take precedence
because the checker invokes this only after successful collection. -/
def validateProgramSignatureFormation
    (signatures : ProgramSignatures) :
    Except (List ProgramSignatureFormationError) Unit :=
  match validateProgramSignatureFormationAux signatures with
  | .ok () => .ok ()
  | .error error => .error [error]

private theorem validateAll_success
    {value error : Type} {validate : value → Except error Unit}
    {values : List value} {property : value → Prop}
    (success : validateAll validate values = .ok ())
    (sound : ∀ candidate, validate candidate = .ok () → property candidate) :
    ∀ candidate, candidate ∈ values → property candidate := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      cases headResult : validate head with
      | error error => simp [validateAll, headResult] at success
      | ok headUnit =>
          cases headUnit
          have tailSuccess : validateAll validate tail = .ok () := by
            simpa [validateAll, headResult] using success
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact sound candidate headResult
          · exact induction tailSuccess candidate member

private theorem signatureTypeApplicationSpineAux_reconstruct
    (type : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    let result := signatureTypeApplicationSpineAux type arguments
    TypeSystem.Ty.applyMany result.1 result.2 =
      TypeSystem.Ty.applyMany type arguments := by
  induction type generalizing arguments with
  | application function argument induction =>
      simpa [signatureTypeApplicationSpineAux, TypeSystem.Ty.applyMany] using
        induction (argument :: arguments)
  | «variable» | parameter | constructor | function | product | mapping
  | proxy | comptime | error =>
      simp [signatureTypeApplicationSpineAux]

private theorem signatureTypeApplicationSpine_reconstruct
    {type head : TypeSystem.Ty} {arguments : List TypeSystem.Ty}
    (spine : signatureTypeApplicationSpine type = (head, arguments)) :
    TypeSystem.Ty.applyMany head arguments = type := by
  have reconstructed :=
    signatureTypeApplicationSpineAux_reconstruct type []
  simp only [signatureTypeApplicationSpine] at spine
  rw [spine] at reconstructed
  simpa [TypeSystem.Ty.applyMany] using reconstructed

private theorem dataType?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {dataType : ProgramDataSignature}
    (found : signatures.dataType? id = some dataType) :
    dataType ∈ signatures.dataTypes ∧ dataType.id = id := by
  have rawFound : signatures.dataTypes.find?
      (fun candidate => decide (candidate.id = id)) = some dataType := by
    simpa [ProgramSignatures.dataType?] using found
  have accepted : decide (dataType.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramDataSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem contract?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {contract : ProgramContractSignature}
    (found : signatures.contract? id = some contract) :
    contract ∈ signatures.contracts ∧ contract.id = id := by
  have rawFound : signatures.contracts.find?
      (fun candidate => decide (candidate.id = id)) = some contract := by
    simpa [ProgramSignatures.contract?] using found
  have accepted : decide (contract.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramContractSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem trait?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {trait : ProgramTraitSignature}
    (found : signatures.trait? id = some trait) :
    trait ∈ signatures.traits ∧ trait.id = id := by
  have rawFound : signatures.traits.find?
      (fun candidate => decide (candidate.id = id)) = some trait := by
    simpa [ProgramSignatures.trait?] using found
  have accepted : decide (trait.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramTraitSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem signatureTypesFormationValidated_of_forall
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {types : List TypeSystem.Ty}
    (validated : ∀ type, type ∈ types →
      SignatureTypeFormationValidated signatures owner parameters type) :
    SignatureTypesFormationValidated signatures owner parameters types := by
  induction types with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (validated head (by simp))
        (induction fun type member => validated type (by simp [member]))

private def SignatureNominalFormationValidated
    (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId)
    (parameters : List TypeSystem.TypeParameterId)
    (nominal : Resolved.DeclarationId)
    (arguments : List TypeSystem.Ty) : Prop :=
  (∃ dataType ∈ signatures.dataTypes,
      dataType.id = nominal ∧
      arguments.length = dataType.parameters.length ∧
      SignatureTypesFormationValidated signatures owner parameters arguments) ∨
    (∃ contract ∈ signatures.contracts,
      contract.id = nominal ∧
      arguments.length = contract.parameters.length ∧
      SignatureTypesFormationValidated signatures owner parameters arguments)

private theorem validateSignatureNominalWith_success
    {signatures : ProgramSignatures}
    {owner nominal : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {arguments : List TypeSystem.Ty}
    {validate : TypeSystem.Ty →
      Except ProgramSignatureFormationError Unit}
    (success : validateSignatureNominalWith validate signatures owner nominal
      arguments = .ok ())
    (sound : ∀ type, validate type = .ok () →
      SignatureTypeFormationValidated signatures owner parameters type) :
    SignatureNominalFormationValidated signatures owner parameters nominal
      arguments := by
  cases dataFound : signatures.dataType? nominal with
  | some dataType =>
      rcases dataType?_eq_some_facts dataFound with ⟨cataloged, id_eq⟩
      by_cases arity : arguments.length = dataType.parameters.length
      · have argumentsSuccess : validateAll validate arguments = .ok () := by
          simpa [validateSignatureNominalWith, dataFound, arity] using success
        exact Or.inl ⟨dataType, cataloged, id_eq, arity,
          signatureTypesFormationValidated_of_forall
            (validateAll_success argumentsSuccess sound)⟩
      · simp [validateSignatureNominalWith, dataFound, arity] at success
  | none =>
      cases contractFound : signatures.contract? nominal with
      | some contract =>
          rcases contract?_eq_some_facts contractFound with ⟨cataloged, id_eq⟩
          by_cases arity : arguments.length = contract.parameters.length
          · have argumentsSuccess : validateAll validate arguments = .ok () := by
              simpa [validateSignatureNominalWith, dataFound, contractFound,
                arity] using success
            exact Or.inr ⟨contract, cataloged, id_eq, arity,
              signatureTypesFormationValidated_of_forall
                (validateAll_success argumentsSuccess sound)⟩
          · simp [validateSignatureNominalWith, dataFound, contractFound,
              arity] at success
      | none =>
          simp [validateSignatureNominalWith, dataFound, contractFound] at success

private theorem validateSignatureTypeFuel_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {fuel : Nat} {type : TypeSystem.Ty}
    (success : validateSignatureTypeFuel signatures owner parameters fuel type =
      .ok ()) :
    SignatureTypeFormationValidated signatures owner parameters type := by
  induction fuel generalizing type with
  | zero => simp [validateSignatureTypeFuel] at success
  | succ fuel induction =>
      cases type with
      | «variable» metavariable =>
          simp [validateSignatureTypeFuel] at success
      | parameter parameter =>
          by_cases bound : parameter ∈ parameters
          · by_cases owned : parameter.owner = owner
            · exact .parameter bound owned
            · simp [validateSignatureTypeFuel, bound, owned] at success
          · simp [validateSignatureTypeFuel, bound] at success
      | constructor constructor =>
          cases constructor with
          | builtin builtin => exact .builtin builtin
          | declaration nominal =>
              have nominalValidated := validateSignatureNominalWith_success
                (parameters := parameters) success
                (fun type typeSuccess => induction typeSuccess)
              rcases nominalValidated with
                ⟨dataType, cataloged, id_eq, arity, argumentsValidated⟩ |
                ⟨contract, cataloged, id_eq, arity, argumentsValidated⟩
              · subst nominal
                simpa [TypeSystem.Ty.nominal, TypeSystem.Ty.applyMany] using
                  SignatureTypeFormationValidated.dataNominal dataType []
                    cataloged arity argumentsValidated
              · subst nominal
                simpa [TypeSystem.Ty.nominal, TypeSystem.Ty.applyMany] using
                  SignatureTypeFormationValidated.contractNominal contract []
                    cataloged arity argumentsValidated
      | application function argument =>
          cases spine : signatureTypeApplicationSpine
              (.application function argument) with
          | mk head arguments =>
              cases head with
              | constructor constructor =>
                  cases constructor with
                  | declaration nominal =>
                      have nominalSuccess :
                          validateSignatureNominalWith
                              (validateSignatureTypeFuel signatures owner
                                parameters fuel)
                              signatures owner nominal arguments = .ok () := by
                        simpa [validateSignatureTypeFuel, spine] using success
                      have nominalValidated :=
                        validateSignatureNominalWith_success
                          (parameters := parameters) nominalSuccess
                          (fun type typeSuccess => induction typeSuccess)
                      have reconstructed :=
                        signatureTypeApplicationSpine_reconstruct spine
                      rcases nominalValidated with
                        ⟨dataType, cataloged, id_eq, arity,
                          argumentsValidated⟩ |
                        ⟨contract, cataloged, id_eq, arity,
                          argumentsValidated⟩
                      · subst nominal
                        rw [← reconstructed]
                        exact .dataNominal dataType arguments cataloged arity
                          argumentsValidated
                      · subst nominal
                        rw [← reconstructed]
                        exact .contractNominal contract arguments cataloged arity
                          argumentsValidated
                  | builtin builtin =>
                      simp [validateSignatureTypeFuel, spine] at success
              | «variable» metavariable =>
                  simp [validateSignatureTypeFuel, spine] at success
              | parameter parameter =>
                  simp [validateSignatureTypeFuel, spine] at success
              | application left right =>
                  simp [validateSignatureTypeFuel, spine] at success
              | function parameter result =>
                  simp [validateSignatureTypeFuel, spine] at success
              | product left right =>
                  simp [validateSignatureTypeFuel, spine] at success
              | mapping key value =>
                  simp [validateSignatureTypeFuel, spine] at success
              | proxy inner =>
                  simp [validateSignatureTypeFuel, spine] at success
              | comptime inner =>
                  simp [validateSignatureTypeFuel, spine] at success
              | error =>
                  simp [validateSignatureTypeFuel, spine] at success
      | function parameter result =>
          cases parameterResult : validateSignatureTypeFuel signatures owner
              parameters fuel parameter with
          | error error =>
              simp [validateSignatureTypeFuel, parameterResult] at success
          | ok parameterUnit =>
              cases parameterUnit
              have resultSuccess : validateSignatureTypeFuel signatures owner
                  parameters fuel result = .ok () := by
                simpa [validateSignatureTypeFuel, parameterResult] using success
              exact .function (induction parameterResult)
                (induction resultSuccess)
      | product left right =>
          cases leftResult : validateSignatureTypeFuel signatures owner
              parameters fuel left with
          | error error =>
              simp [validateSignatureTypeFuel, leftResult] at success
          | ok leftUnit =>
              cases leftUnit
              have rightSuccess : validateSignatureTypeFuel signatures owner
                  parameters fuel right = .ok () := by
                simpa [validateSignatureTypeFuel, leftResult] using success
              exact .product (induction leftResult) (induction rightSuccess)
      | mapping key value =>
          cases keyResult : validateSignatureTypeFuel signatures owner
              parameters fuel key with
          | error error =>
              simp [validateSignatureTypeFuel, keyResult] at success
          | ok keyUnit =>
              cases keyUnit
              have valueSuccess : validateSignatureTypeFuel signatures owner
                  parameters fuel value = .ok () := by
                simpa [validateSignatureTypeFuel, keyResult] using success
              exact .mapping (induction keyResult) (induction valueSuccess)
      | proxy inner =>
          exact .proxy (induction (by
            simpa [validateSignatureTypeFuel] using success))
      | comptime inner =>
          exact .comptime (induction (by
            simpa [validateSignatureTypeFuel] using success))
      | error =>
          simp [validateSignatureTypeFuel] at success

private theorem validateSignatureType_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty}
    (success : validateSignatureType signatures owner parameters type = .ok ()) :
    SignatureTypeFormationValidated signatures owner parameters type :=
  validateSignatureTypeFuel_success success

/-- The public single-type validator returns only semantically formed resolved
types. -/
theorem validateResolvedTypeFormation_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty}
    (success : validateResolvedTypeFormation signatures owner parameters type =
      .ok ()) :
    SignatureTypeFormationValidated signatures owner parameters type :=
  validateSignatureType_success success

private theorem validateSignatureTypes_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {types : List TypeSystem.Ty}
    (success : validateSignatureTypes signatures owner parameters types = .ok ()) :
    SignatureTypesFormationValidated signatures owner parameters types :=
  signatureTypesFormationValidated_of_forall
    (validateAll_success success fun _ => validateSignatureType_success)

private theorem validateSignaturePredicate_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {predicate : ProgramPredicate}
    (success : validateSignaturePredicate signatures owner parameters predicate =
      .ok ()) :
    SignaturePredicateFormationValidated signatures owner parameters
      predicate := by
  cases subjectResult : validateSignatureType signatures owner parameters
      predicate.subject with
  | error error =>
      simp [validateSignaturePredicate, subjectResult] at success
  | ok subjectUnit =>
      cases subjectUnit
      cases argumentsResult : validateSignatureTypes signatures owner parameters
          predicate.arguments with
      | error error =>
          simp [validateSignaturePredicate, subjectResult, argumentsResult]
            at success
      | ok argumentsUnit =>
          cases argumentsUnit
          refine {
            subject := validateSignatureType_success subjectResult
            arguments := validateSignatureTypes_success argumentsResult
            trait := ?_
          }
          cases traitCase : predicate.trait with
          | builtin builtin =>
              cases builtin with
              | int =>
                  by_cases empty : predicate.arguments.isEmpty
                  · simpa [traitCase] using empty
                  · simp [validateSignaturePredicate, subjectResult,
                      argumentsResult, traitCase, empty] at success
          | declaration traitId =>
              cases traitFound : signatures.trait? traitId with
              | none =>
                  simp [validateSignaturePredicate, subjectResult,
                    argumentsResult, traitCase, traitFound] at success
              | some trait =>
                  rcases trait?_eq_some_facts traitFound with
                    ⟨cataloged, id_eq⟩
                  by_cases arity :
                      predicate.arguments.length + 1 = trait.parameters.length
                  · have witness : ∃ signature ∈ signatures.traits,
                        signature.id = traitId ∧
                        predicate.arguments.length + 1 =
                          signature.parameters.length :=
                      ⟨trait, cataloged, id_eq, arity⟩
                    simpa [traitCase] using witness
                  · simp [validateSignaturePredicate, subjectResult,
                      argumentsResult, traitCase, traitFound, arity] at success

private theorem validateSignaturePredicates_success
    {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeSystem.TypeParameterId}
    {predicates : List ProgramPredicate}
    (success : validateSignaturePredicates signatures owner parameters
      predicates = .ok ()) :
    SignaturePredicatesFormationValidated signatures owner parameters
      predicates :=
  validateAll_success success fun _ => validateSignaturePredicate_success

private theorem validateFunctionSignatureFormation_success
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    (success : validateFunctionSignatureFormation signatures signature =
      .ok ()) :
    SignatureTypesFormationValidated signatures signature.id
        signature.scheme.parameters signature.parameterTypes ∧
      SignatureTypesFormationValidated signatures signature.id
        signature.scheme.parameters signature.returnTypes ∧
      SignaturePredicatesFormationValidated signatures signature.id
        signature.scheme.parameters signature.scheme.predicates := by
  cases parametersResult : validateSignatureTypes signatures signature.id
      signature.scheme.parameters signature.parameterTypes with
  | error error =>
      simp [validateFunctionSignatureFormation, parametersResult] at success
  | ok parametersUnit =>
      cases parametersUnit
      cases returnsResult : validateSignatureTypes signatures signature.id
          signature.scheme.parameters signature.returnTypes with
      | error error =>
          simp [validateFunctionSignatureFormation, parametersResult,
            returnsResult] at success
      | ok returnsUnit =>
          cases returnsUnit
          have predicatesSuccess : validateSignaturePredicates signatures
              signature.id signature.scheme.parameters
              signature.scheme.predicates = .ok () := by
            simpa [validateFunctionSignatureFormation, parametersResult,
              returnsResult] using success
          exact ⟨validateSignatureTypes_success parametersResult,
            validateSignatureTypes_success returnsResult,
            validateSignaturePredicates_success predicatesSuccess⟩

private theorem validateDataSignatureFormation_success
    {signatures : ProgramSignatures}
    {signature : ProgramDataSignature}
    (success : validateDataSignatureFormation signatures signature = .ok ()) :
    ∀ constructor, constructor ∈ signature.constructors →
      SignatureTypesFormationValidated signatures signature.id
        signature.parameters constructor.payloadTypes := by
  exact validateAll_success success fun constructor constructorSuccess =>
    validateSignatureTypes_success constructorSuccess

private theorem validateTraitMethodSignatureFormation_success
    {signatures : ProgramSignatures}
    {trait : ProgramTraitSignature}
    {method : ProgramTraitMethodSignature}
    (success : validateTraitMethodSignatureFormation signatures trait method =
      .ok ()) :
    SignatureTypesFormationValidated signatures trait.id trait.parameters
        method.parameterTypes ∧
      SignatureTypesFormationValidated signatures trait.id trait.parameters
        method.returnTypes ∧
      SignaturePredicatesFormationValidated signatures trait.id
        trait.parameters method.wherePredicates := by
  cases parametersResult : validateSignatureTypes signatures trait.id
      trait.parameters method.parameterTypes with
  | error error =>
      simp [validateTraitMethodSignatureFormation, parametersResult] at success
  | ok parametersUnit =>
      cases parametersUnit
      cases returnsResult : validateSignatureTypes signatures trait.id
          trait.parameters method.returnTypes with
      | error error =>
          simp [validateTraitMethodSignatureFormation, parametersResult,
            returnsResult] at success
      | ok returnsUnit =>
          cases returnsUnit
          have predicatesSuccess : validateSignaturePredicates signatures trait.id
              trait.parameters method.wherePredicates = .ok () := by
            simpa [validateTraitMethodSignatureFormation, parametersResult,
              returnsResult] using success
          exact ⟨validateSignatureTypes_success parametersResult,
            validateSignatureTypes_success returnsResult,
            validateSignaturePredicates_success predicatesSuccess⟩

private theorem validateTraitSignatureFormation_success
    {signatures : ProgramSignatures}
    {signature : ProgramTraitSignature}
    (success : validateTraitSignatureFormation signatures signature = .ok ()) :
    SignaturePredicatesFormationValidated signatures signature.id
        signature.parameters signature.wherePredicates ∧
      ∀ method, method ∈ signature.methods →
        SignatureTypesFormationValidated signatures signature.id
            signature.parameters method.parameterTypes ∧
          SignatureTypesFormationValidated signatures signature.id
            signature.parameters method.returnTypes ∧
          SignaturePredicatesFormationValidated signatures signature.id
            signature.parameters method.wherePredicates := by
  cases predicatesResult : validateSignaturePredicates signatures signature.id
      signature.parameters signature.wherePredicates with
  | error error =>
      simp [validateTraitSignatureFormation, predicatesResult] at success
  | ok predicatesUnit =>
      cases predicatesUnit
      have methodsSuccess : validateAll
          (validateTraitMethodSignatureFormation signatures signature)
          signature.methods = .ok () := by
        simpa [validateTraitSignatureFormation, predicatesResult] using success
      exact ⟨validateSignaturePredicates_success predicatesResult,
        validateAll_success methodsSuccess fun _ =>
          validateTraitMethodSignatureFormation_success⟩

private theorem validateImplementationSignatureFormation_success
    {signatures : ProgramSignatures}
    {signature : ProgramImplementationSignature}
    (success : validateImplementationSignatureFormation signatures signature =
      .ok ()) :
    SignaturePredicateFormationValidated signatures signature.id
        signature.parameters signature.head ∧
      SignaturePredicatesFormationValidated signatures signature.id
        signature.parameters signature.wherePredicates := by
  cases headResult : validateSignaturePredicate signatures signature.id
      signature.parameters signature.head with
  | error error =>
      simp [validateImplementationSignatureFormation, headResult] at success
  | ok headUnit =>
      cases headUnit
      have predicatesSuccess : validateSignaturePredicates signatures signature.id
          signature.parameters signature.wherePredicates = .ok () := by
        simpa [validateImplementationSignatureFormation, headResult] using success
      exact ⟨validateSignaturePredicate_success headResult,
        validateSignaturePredicates_success predicatesSuccess⟩

private theorem validateProgramSignatureFormationAux_success
    {signatures : ProgramSignatures}
    (success : validateProgramSignatureFormationAux signatures = .ok ()) :
    ProgramSignatureFormationValidated signatures := by
  cases functionsResult : validateAll
      (validateFunctionSignatureFormation signatures) signatures.functions with
  | error error =>
      simp [validateProgramSignatureFormationAux, functionsResult] at success
  | ok functionsUnit =>
      cases functionsUnit
      cases dataResult : validateAll (validateDataSignatureFormation signatures)
          signatures.dataTypes with
      | error error =>
          simp [validateProgramSignatureFormationAux, functionsResult,
            dataResult] at success
      | ok dataUnit =>
          cases dataUnit
          cases traitsResult : validateAll
              (validateTraitSignatureFormation signatures) signatures.traits with
          | error error =>
              simp [validateProgramSignatureFormationAux, functionsResult,
                dataResult, traitsResult] at success
          | ok traitsUnit =>
              cases traitsUnit
              have implementationsResult : validateAll
                  (validateImplementationSignatureFormation signatures)
                  signatures.implementations = .ok () := by
                simpa [validateProgramSignatureFormationAux, functionsResult,
                  dataResult, traitsResult] using success
              exact {
                functions := validateAll_success functionsResult fun _ =>
                  validateFunctionSignatureFormation_success
                dataTypes := validateAll_success dataResult fun _ =>
                  validateDataSignatureFormation_success
                traits := validateAll_success traitsResult fun _ =>
                  validateTraitSignatureFormation_success
                implementations := validateAll_success implementationsResult
                  fun _ => validateImplementationSignatureFormation_success
              }

/-- Successful executable formation validation exposes the exact structural
witness consumed by the source-semantics checker boundary. -/
theorem validateProgramSignatureFormation_success
    {signatures : ProgramSignatures}
    (success : validateProgramSignatureFormation signatures = .ok ()) :
    ProgramSignatureFormationValidated signatures := by
  cases auxiliaryResult : validateProgramSignatureFormationAux signatures with
  | error error =>
      simp [validateProgramSignatureFormation, auxiliaryResult] at success
  | ok auxiliaryUnit =>
      cases auxiliaryUnit
      exact validateProgramSignatureFormationAux_success auxiliaryResult

end Solcore.Frontend
