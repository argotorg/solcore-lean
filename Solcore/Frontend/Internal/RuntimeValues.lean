import Solcore.Frontend.SourceCompilationPlan
import Solcore.Core.Primitive

/-!
# Source runtime values

Source values and heap observations shared by compiler adapters, and bounded input validation.
-/

section
-- leanmerge: from Solcore.Frontend.SourceRuntimePlanAPI
/-! Historical source plan names remain available through the pure runtime
carriers. These aliases import no source execution code. -/

namespace Solcore.Frontend.SourceTypedRuntime

/- Compatibility names for the shared compilation-plan API. -/
export SourceCompilationPlan (
  exactSpecialization
  runtimeEvidenceGoal
  validateRuntimeEvidence
  validateAuthenticatedRuntimeEvidence
  validateRuntimeEvidence_success_matches
  validateAuthenticatedRuntimeEvidence_success_matches
  materializeCallEvidence
  materializeCallEvidence_success_matches
  exactDirectCallRuntimeEvidence
  exactDeclarationReferenceRuntimeEvidence
  exactDirectCallRuntimeEvidence_success_matches
  exactDeclarationReferenceRuntimeEvidence_success_matches
  exactRuntimeRequirementEvidence
  exactRuntimeRequirementEvidence_success_goal
  exactRuntimeRequirementEvidenceList
  exactRuntimeRequirementEvidenceList_success_matches
  validateExecutablePlan
  validateCanonicalInputPlan
  prepareExecutablePlanEvidenceWithBudget
  prepareExecutablePlanEvidence
  validateExecutablePlanEvidence)

end Solcore.Frontend.SourceTypedRuntime
end

section
-- leanmerge: from Solcore.Frontend.SourceRuntimeValues
/-! Source values and heap observations shared by compiler adapters.
The historical public namespace is retained for API compatibility. This module
contains no expression, statement, or callable evaluator. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem SourceCompilationPlan

/-- Erase staging wrappers while preserving the complete runtime type shape.
`comptime<T>` changes when a value is available, not its runtime
representation.  Erasure is recursive because staging wrappers may occur
inside products, functions, mappings, proxies, and nominal arguments.  The
twelve fixed-width integer types have runtime type `word`, because their
values are canonical words; input validation checks the canonical range. -/
@[simp] def runtimeType : Ty → Ty
  | .variable id => .variable id
  | .parameter id => .parameter id
  | .constructor (.builtin (.fixed _)) => .word
  | .constructor id => .constructor id
  | .application function argument =>
      .application (runtimeType function) (runtimeType argument)
  | .function parameter result =>
      .function (runtimeType parameter) (runtimeType result)
  | .product left right => .product (runtimeType left) (runtimeType right)
  | .mapping key value => .mapping (runtimeType key) (runtimeType value)
  | .proxy inner => .proxy (runtimeType inner)
  | .comptime inner => runtimeType inner
  | .error => .error

@[simp] theorem runtimeType_idempotent (type : Ty) :
    runtimeType (runtimeType type) = runtimeType type := by
  induction type
  case constructor id =>
    cases id with
    | builtin builtin => cases builtin <;> rfl
    | declaration _ => rfl
  all_goals simp_all [runtimeType]

abbrev Environment := List (Resolved.LocalId × Location)

/-- Values which deliberately retain source-level types.  Mapping entries are
ordered by first insertion; replacement preserves that order. -/
inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : Value)
  | proxy (inner : Ty)
  | constructed
      (instantiation : DataConstructorInstantiation)
      (arguments : List Value)
  | mapping
      (keyType valueType : Ty)
      (entries : List (Value × Value))
  | closure
      (parameters : List TypedBinder)
      (resultType : Ty)
      (body : List StatementId)
      (source : TypedSource)
      (owner : Key)
      (captured : Environment)
      (evidence : RuntimeEvidenceEnvironment)
  /-- A source observation of a principal value at one concrete occurrence.
  The wrapper records the occurrence substitution and evidence separately from
  the original closure's plan provenance. Core adapters prepare these views
  before execution and call the corresponding native closure. -/
  | instantiated
      (substitution : Substitution)
      (requirements : List LocalRequirementWitness)
      (principal : Value)
  /-- One closed view of a source declaration.  The evidence list is stored
  in the declaration's predicate order so an indirect invocation has the same
  authenticated dictionary that was available at the reference occurrence. -/
  | global (key : Key) (evidence : RuntimeEvidenceEnvironment)
  | builtin (function : BuiltinFunctionId)
  deriving Repr

structure Cell where
  type : Ty
  value : Option Value
  deriving Repr

structure RuntimeState where
  heap : List Cell := []
  deriving Repr

namespace RuntimeState

def read? (state : RuntimeState) (location : Location) : Option Cell :=
  state.heap[location.index]?

/-- Replace one existing cell.  The explicit recursion avoids exposing an
index proof in the runtime API. -/
def replaceCell : Nat → Cell → List Cell → List Cell
  | _, _, [] => []
  | 0, replacement, _ :: rest => replacement :: rest
  | index + 1, replacement, cell :: rest =>
      cell :: replaceCell index replacement rest

def write? (state : RuntimeState) (location : Location)
    (value : Option Value) : Option RuntimeState := do
  let cell ← state.read? location
  pure { heap := replaceCell location.index { cell with value } state.heap }

def allocate (state : RuntimeState) (type : Ty) (value : Option Value) :
    Location × RuntimeState :=
  (⟨state.heap.length⟩, { heap := state.heap ++ [{ type, value }] })

end RuntimeState

/-- Ordinary executable defaults retain the raw metadata of proxies and
mappings. In particular, a missing mapping entry uses its stored value type.
This pure constructor is shared by the Core adapter and compiler-time code. -/
def defaultValue? : Nat → Ty → Option Value
  | 0, _ => none
  | _ + 1, .constructor (.builtin .unit) => some .unit
  | _ + 1, .constructor (.builtin .bool) => some (.bool false)
  | _ + 1, .constructor (.builtin .word) => some (.word Core.Word.zero)
  | _ + 1, .constructor (.builtin (.fixed _)) => some (.word Core.Word.zero)
  | _ + 1, .constructor (.builtin .integer) => some (.integer 0)
  | fuel + 1, .product left right => do
      pure (.product (← defaultValue? fuel left) (← defaultValue? fuel right))
  | _ + 1, .proxy inner => some (.proxy inner)
  | _ + 1, .mapping key value => some (.mapping key value [])
  | fuel + 1, .comptime inner => defaultValue? fuel inner
  | _, _ => none


private def findSpecialization? (plan : Plan) (key : Key) :
    Option SourceSpecialization.SpecializedFunction :=
  plan.specializations.find? fun specialized => decide (specialized.key = key)

mutual

  def valueTypes? (plan : Plan) : List Value → Option (List Ty)
    | [] => some []
    | value :: values => do
        let type ← Value.type? plan value
        let types ← valueTypes? plan values
        pure (type :: types)

  def Value.type? (plan : Plan) : Value → Option Ty
    | .unit => some .unit
    | .bool _ => some .bool
    | .word _ => some .word
    | .integer _ => some .integer
    | .product left right => do
        pure (.product (← left.type? plan) (← right.type? plan))
    | .proxy inner => some (.proxy (runtimeType inner))
    | .constructed instantiation arguments => do
        let actual ← valueTypes? plan arguments
        if actual = instantiation.payloadTypes.map runtimeType then
          some (runtimeType instantiation.resultType)
        else
          none
    | .mapping keyType valueType _ =>
        some (.mapping (runtimeType keyType) (runtimeType valueType))
    | .closure parameters resultType _ _ _ _ _ =>
        some (runtimeType
          (.function (Ty.productMany (parameters.map (·.scheme.body))) resultType))
    | .instantiated substitution _ principal =>
        (runtimeType ∘ substitution.apply) <$> principal.type? plan
    | .global key _ => do
        let specialized ← findSpecialization? plan key
        pure (runtimeType specialized.function.type)
    | .builtin function => some (runtimeType function.type)

end

inductive RunResult where
  | done (value : Value) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)
  deriving Repr

end Solcore.Frontend.SourceTypedRuntime
end

section
-- leanmerge: from Solcore.Frontend.SourceRuntimeValidation
/-! Bounded source input validation shared by runtime adapters. These checks
authenticate values and exact global evidence without executing source code.
Their results and error order preserve the existing public input contract. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceTypedRuntime
open SourceInference TypeSystem SourceCompilationPlan

/-- Exactly one catalog entry with this data identity. -/
private def exactDataType? (signatures : ProgramSignatures)
    (id : Resolved.DeclarationId) : Option ProgramDataSignature :=
  match signatures.dataTypes.filter fun dataType => decide (dataType.id = id) with
  | [dataType] => some dataType
  | _ => none

/-- Exactly one catalog constructor with this identity. -/
private def exactConstructor? (dataType : ProgramDataSignature)
    (id : ProgramDataConstructorId) : Option ProgramDataConstructorSignature :=
  match dataType.constructors.filter fun constructor =>
      decide (constructor.id = id) with
  | [constructor] => some constructor
  | _ => none

/-- Reconstruct constructor metadata from the authoritative signature catalog.
Self-consistent but forged `DataConstructorInstantiation` values do not pass. -/
def validConstructorInstantiation (signatures : ProgramSignatures)
    (instantiation : DataConstructorInstantiation) : Bool :=
  match exactDataType? signatures instantiation.constructor.dataType with
  | none => false
  | some dataType =>
      match exactConstructor? dataType instantiation.constructor with
      | none => false
      | some constructor =>
          let parameters := instantiation.parameterSubstitution.map Prod.fst
          if parameters != dataType.parameters then
            false
          else
            match dataType.parameters.mapM
                instantiation.parameterSubstitution.lookup? with
            | none => false
            | some arguments =>
                let expectedPayload := constructor.payloadTypes.map
                  instantiation.parameterSubstitution.apply
                let expectedResult := Ty.nominal dataType.id arguments
                instantiation.payloadTypes = expectedPayload &&
                  instantiation.resultType = expectedResult

/-- Erase staging wrappers only, keeping the fixed-width integer types: the type
whose canonical values a runtime input must have. -/
@[simp] def unstagedType : Ty → Ty
  | .application function argument =>
      .application (unstagedType function) (unstagedType argument)
  | .function parameter result =>
      .function (unstagedType parameter) (unstagedType result)
  | .product left right => .product (unstagedType left) (unstagedType right)
  | .mapping key value => .mapping (unstagedType key) (unstagedType value)
  | .proxy inner => .proxy (unstagedType inner)
  | .comptime inner => unstagedType inner
  | type => type

/-- Exact outcome of bounded recursive runtime-input validation. -/
inductive TypeValidation where
  | valid
  | invalid
  | unsupportedStaged
  | outOfFuel
  deriving Repr, BEq, DecidableEq

private def combineValidation (first second : TypeValidation) : TypeValidation :=
  match first with
  | .valid => second
  | .invalid => .invalid
  | .unsupportedStaged => .unsupportedStaged
  | .outOfFuel => .outOfFuel

mutual

  private def valuesValidateFuel (fuel : Nat)
      (signatures : ProgramSignatures) (plan : Plan) :
      List Ty → List Value → TypeValidation
    | [], [] => .valid
    | expected :: expectedRest, actual :: actualRest =>
        combineValidation
          (Value.validateTypeFuel fuel signatures plan expected actual)
          (valuesValidateFuel fuel signatures plan expectedRest actualRest)
    | _, _ => .invalid

  private def mappingEntriesValidateFuel (fuel : Nat)
      (signatures : ProgramSignatures) (plan : Plan)
      (keyType valueType : Ty) : List (Value × Value) → TypeValidation
    | [] => .valid
    | entry :: rest =>
        combineValidation
          (Value.validateTypeFuel fuel signatures plan keyType entry.1)
          (combineValidation
            (Value.validateTypeFuel fuel signatures plan valueType entry.2)
            (mappingEntriesValidateFuel fuel signatures plan keyType valueType
              rest))

  /-- Bounded deep validation which distinguishes malformed input from budget
  exhaustion.  A word at a fixed-width integer type must be canonical for it. -/
  def Value.validateTypeFuel :
      Nat → ProgramSignatures → Plan → Ty → Value → TypeValidation
    | 0, _, _, _, _ => .outOfFuel
    | fuel + 1, signatures, plan, expected, actual =>
        match unstagedType expected, actual with
        | .constructor (.builtin .unit), .unit => .valid
        | .constructor (.builtin .bool), .bool _ => .valid
        | .constructor (.builtin .word), .word _ => .valid
        | .constructor (.builtin (.fixed type)), .word value =>
            if type.canonical value.val then .valid else .invalid
        | .constructor (.builtin .integer), .integer _ => .valid
        | .product leftType rightType, .product left right =>
            combineValidation
              (Value.validateTypeFuel fuel signatures plan leftType left)
              (Value.validateTypeFuel fuel signatures plan rightType right)
        | .proxy inner, .proxy actualInner =>
            if runtimeType inner = runtimeType actualInner then .valid else .invalid
        | .mapping keyType valueType, .mapping actualKey actualValue entries =>
            if decide (runtimeType keyType = runtimeType actualKey) &&
                decide (runtimeType valueType = runtimeType actualValue) then
              mappingEntriesValidateFuel fuel signatures plan keyType valueType
                entries
            else
              .invalid
        | _, .constructed instantiation arguments =>
            if decide (runtimeType expected =
                runtimeType instantiation.resultType) &&
                validConstructorInstantiation signatures instantiation then
              valuesValidateFuel fuel signatures plan
                instantiation.payloadTypes arguments
            else
              .invalid
        | .function _ _, .global key evidence =>
            match exactSpecialization plan key with
            | .ok specialized =>
                if runtimeType specialized.function.type =
                    runtimeType expected then
                  match validateAuthenticatedRuntimeEvidence signatures key
                      specialized.assumptions evidence with
                  | .ok () => .valid
                  | .error _ => .invalid
                else .invalid
            | .error _ => .invalid
        | .function _ _, .builtin function =>
            if runtimeType function.type = runtimeType expected then
              .valid
            else
              .invalid
        | _, _ => .invalid

end

/-- Boolean compatibility projection of exact bounded validation. -/
def Value.hasTypeFuel (fuel : Nat) (signatures : ProgramSignatures)
    (plan : Plan) (expected : Ty) (value : Value) : Bool :=
  Value.validateTypeFuel fuel signatures plan expected value == .valid

namespace Value

/-- Deep validation against source types and the authoritative nominal catalog.
The explicit budget also bounds recursively nested constructor and mapping
inputs. -/
def hasType (signatures : ProgramSignatures) (plan : Plan) (fuel : Nat)
    (expected : Ty) (value : Value) : Bool :=
  Value.hasTypeFuel fuel signatures plan expected value

end Value

def validateInputs (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) : List Ty → List Value → Option RuntimeError
  | [], [] => none
  | expected :: expectedRest, actual :: actualRest =>
      match actual.validateTypeFuel fuel signatures plan expected with
      | .valid => validateInputs signatures plan fuel expectedRest actualRest
      | .invalid => some (.typeMismatch expected (actual.type? plan))
      | .unsupportedStaged => some (.unsupportedStagedInput expected)
      | .outOfFuel => some (.inputValidationFuelExhausted expected fuel)
  | expected, actual => some (.argumentArityMismatch expected.length actual.length)


end Solcore.Frontend.SourceTypedRuntime
end
