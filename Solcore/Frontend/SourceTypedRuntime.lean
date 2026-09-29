import Solcore.Core.Primitive
import Solcore.Frontend.ExecutableImplMethods
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Frontend.WordLiteral

/-!
Execution of closed, specialized typed-source programs.

This runtime is intentionally additive.  The established `SourceRuntime`
continues to provide the Core-compatible execution path, while this module
keeps source types and source occurrence identities intact.  In particular it
can represent nominal constructors, mappings, proxies, mutable lexical cells,
and statement control flow which have no faithful `Core.Ty` projection.

Lexical environments contain locations rather than values.  A closure therefore
observes later writes to a captured local, and a block can discard its local
bindings without discarding heap effects.  All recursive execution is bounded
by explicit fuel.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Location where
  index : Nat
  deriving Repr, BEq, DecidableEq

abbrev Environment := List (Resolved.LocalId × Location)

/-- Closed trait evidence available while one specialized function body is
executing.  The carrier deliberately excludes `PredicateEvidence.assumption`:
every entry has already been discharged by an enclosing call.  Call assembly
and `Matches`, rather than the list carrier itself, enforce the specialized
signature's predicate order. -/
abbrev RuntimeEvidenceEnvironment := List TypedTraitResolution.Evidence

namespace RuntimeEvidenceEnvironment

def goals (environment : RuntimeEvidenceEnvironment) : List ProgramPredicate :=
  environment.map fun
    | .byImpl goal _ _ => goal

/-- The executable dictionary has exactly the goals, order, and multiplicity
declared by the specialization about to execute. -/
def Matches (environment : RuntimeEvidenceEnvironment)
    (predicates : List ProgramPredicate) : Prop :=
  environment.goals = predicates

theorem Matches.length_eq
    {environment : RuntimeEvidenceEnvironment}
    {predicates : List ProgramPredicate}
    (agreement : environment.Matches predicates) :
    environment.length = predicates.length := by
  unfold Matches goals at agreement
  rw [← agreement, List.length_map]

end RuntimeEvidenceEnvironment

/-- Runtime evidence attached to one concrete use of a qualified local
scheme.  Requirement identities, rather than predicate equality, connect the
assumption in the stored lambda body to the independently solved obligation at
the local-reference occurrence. -/
structure LocalRequirementWitness where
  templateRequirement : RequirementId
  actualRequirement : RequirementId
  predicate : ProgramPredicate
  evidence : TypedTraitResolution.Evidence
  deriving Repr

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
  /-- A runtime-only view of a principal value at one concrete occurrence.
  The wrapper keeps the stored closure and its plan provenance unchanged;
  callable execution applies the substitution to the closure's checked source
  graph just before entering its body. -/
  | instantiated
      (substitution : Substitution)
      (requirements : List LocalRequirementWitness)
      (principal : Value)
  | global (key : Key)
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
private def replaceCell : Nat → Cell → List Cell → List Cell
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

private def lookupLocation? (environment : Environment)
    (id : Resolved.LocalId) : Option Location :=
  (environment.find? fun entry => decide (entry.1 = id)).map Prod.snd

private def findSpecialization? (plan : Plan) (key : Key) :
    Option SourceSpecialization.SpecializedFunction :=
  plan.specializations.find? fun specialized => decide (specialized.key = key)

private def resultType? (function : CheckedFunction) : Option Ty :=
  match function.type with
  | .function _ result => some result
  | _ => none

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
    | .proxy inner => some (.proxy inner)
    | .constructed instantiation arguments => do
        let actual ← valueTypes? plan arguments
        if actual = instantiation.payloadTypes then
          some instantiation.resultType
        else
          none
    | .mapping keyType valueType _ => some (.mapping keyType valueType)
    | .closure parameters resultType _ _ _ _ _ =>
        some (.function (Ty.productMany (parameters.map (·.scheme.body))) resultType)
    | .instantiated substitution _ principal =>
        substitution.apply <$> principal.type? plan
    | .global key => do
        let specialized ← findSpecialization? plan key
        pure specialized.function.type
    | .builtin function => some function.type

end

namespace Cell

/-- Shallow agreement between a heap cell's declared type and its initialized
value.  This deliberately follows `Value.type?`: it does not validate mapping
entries, closure bodies or captures, constructor catalog authenticity, or the
heap reachable through captured locations.  Uninitialized cells are valid. -/
def HasShallowType (cell : Cell) (plan : Plan) : Prop :=
  ∀ value, cell.value = some value → value.type? plan = some cell.type

end Cell

namespace RuntimeState

/-- Every current heap cell has shallow agreement between its annotation and
optional value.  This is a foundation for a later deep heap/capture invariant,
not a claim that recursively contained runtime data has been validated. -/
def HasShallowTypes (state : RuntimeState) (plan : Plan) : Prop :=
  ∀ cell, cell ∈ state.heap → cell.HasShallowType plan

theorem mem_replaceCell
    (index : Nat) (replacement selected : Cell) (heap : List Cell)
    (member : selected ∈ replaceCell index replacement heap) :
    selected = replacement ∨ selected ∈ heap := by
  induction heap generalizing index with
  | nil => simp [replaceCell] at member
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp only [replaceCell, List.mem_cons] at member ⊢
          rcases member with equal | member
          · exact .inl equal
          · exact .inr (.inr member)
      | succ index =>
          simp only [replaceCell, List.mem_cons] at member ⊢
          rcases member with equal | member
          · exact .inr (.inl equal)
          · rcases inductionHypothesis index member with equal | old
            · exact .inl equal
            · exact .inr (.inr old)

private theorem replaceCell_typeVector
    (heap : List Cell) (index : Nat) (previous replacement : Cell)
    (found : heap[index]? = some previous)
    (sameType : replacement.type = previous.type) :
    (replaceCell index replacement heap).map Cell.type = heap.map Cell.type := by
  induction heap generalizing index with
  | nil => simp at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp at found
          cases found
          simp [replaceCell, sameType]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          simpa [replaceCell] using
            inductionHypothesis index found

/-- A heap write changes only a cell's optional value, never the vector of
declared cell types. -/
theorem write?_typeVector_eq
    (state updated : RuntimeState) (location : Location)
    (value : Option Value)
    (written : state.write? location value = some updated) :
    updated.heap.map Cell.type = state.heap.map Cell.type := by
  unfold RuntimeState.write? at written
  cases found : state.read? location with
  | none => simp [found] at written
  | some previous =>
      simp only [found] at written
      cases written
      apply replaceCell_typeVector state.heap location.index previous
        { previous with value }
      · simpa [RuntimeState.read?] using found
      · rfl

/-- Replacing the optional value of one readable cell preserves shallow heap
typing when the replacement value agrees with that cell's retained type. -/
theorem HasShallowTypes.write?
    {plan : Plan} {state updated : RuntimeState} {location : Location}
    {previous : Cell} {value : Option Value}
    (typing : state.HasShallowTypes plan)
    (found : state.read? location = some previous)
    (replacement : ({ previous with value }).HasShallowType plan)
    (written : state.write? location value = some updated) :
    updated.HasShallowTypes plan := by
  unfold RuntimeState.write? at written
  rw [found] at written
  cases written
  intro selected member
  rcases mem_replaceCell location.index { previous with value } selected
      state.heap member with equal | old
  · subst selected
    exact replacement
  · exact typing selected old

/-- Allocating a value whose shallow type agrees with the new cell preserves
the heap invariant.  This is the heap step used by parameter and pattern
binding in the evaluator. -/
theorem HasShallowTypes.allocateValue
    {plan : Plan} {state : RuntimeState}
    (typing : state.HasShallowTypes plan) (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    (state.allocate type (some value)).2.HasShallowTypes plan := by
  intro selected member
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact typing selected old
  · simp only [List.mem_singleton] at fresh
    subst selected
    intro found equal
    cases equal
    exact typed

end RuntimeState

mutual

  private def valuesEqual : List Value → List Value → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        valueEqual left right && valuesEqual lefts rights
    | _, _ => false

  private def valueEqual : Value → Value → Bool
    | .unit, .unit => true
    | .bool left, .bool right => left == right
    | .word left, .word right => left == right
    | .integer left, .integer right => left == right
    | .product leftHead leftTail, .product rightHead rightTail =>
        valueEqual leftHead rightHead && valueEqual leftTail rightTail
    | .proxy left, .proxy right => decide (left = right)
    | .constructed left leftArguments,
        .constructed right rightArguments =>
        decide (left = right) && valuesEqual leftArguments rightArguments
    | .global left, .global right => decide (left = right)
    | .builtin left, .builtin right => left == right
    | _, _ => false

end

private def packValues : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: values => .product value (packValues values)

private def unpackValues : Nat → Value → Option (List Value)
  | 0, .unit => some []
  | 0, _ => none
  | 1, value => some [value]
  | count + 2, .product value rest => do
      pure (value :: (← unpackValues (count + 1) rest))
  | _ + 2, _ => none

def defaultValue? : Nat → Ty → Option Value
  | 0, _ => none
  | _ + 1, .constructor (.builtin .unit) => some .unit
  | _ + 1, .constructor (.builtin .bool) => some (.bool false)
  | _ + 1, .constructor (.builtin .word) => some (.word Core.Word.zero)
  | _ + 1, .constructor (.builtin .integer) => some (.integer 0)
  | fuel + 1, .product left right => do
      pure (.product (← defaultValue? fuel left) (← defaultValue? fuel right))
  | _ + 1, .proxy inner => some (.proxy inner)
  | _ + 1, .mapping key value => some (.mapping key value [])
  | fuel + 1, .comptime inner => defaultValue? fuel inner
  | _, _ => none

def mappingLookup? (key : Value) : List (Value × Value) → Option Value
  | [] => none
  | entry :: rest =>
      if valueEqual key entry.1 then some entry.2 else mappingLookup? key rest

def mappingInsert (key value : Value) :
    List (Value × Value) → List (Value × Value)
  | [] => [(key, value)]
  | entry :: rest =>
      if valueEqual key entry.1 then (key, value) :: rest
      else entry :: mappingInsert key value rest

/-- Insertion either contributes the new pair or retains an old pair. -/
theorem mappingInsert_member
    (key value : Value) (entries : List (Value × Value))
    (selected : Value × Value)
    (member : selected ∈ mappingInsert key value entries) :
    selected = (key, value) ∨ selected ∈ entries := by
  induction entries with
  | nil =>
      simp [mappingInsert] at member
      exact .inl member
  | cons entry rest inductionHypothesis =>
      by_cases sameKey : valueEqual key entry.1
      · simp [mappingInsert, sameKey] at member ⊢
        rcases member with fresh | old
        · exact Or.inl fresh
        · exact Or.inr (Or.inr old)
      · simp [mappingInsert, sameKey] at member ⊢
        rcases member with old | tail
        · exact Or.inr (Or.inl old)
        · rcases inductionHypothesis tail with fresh | old
          · exact Or.inl fresh
          · exact Or.inr (Or.inr old)

inductive RuntimeError where
  | missingSpecialization (key : Key)
  | duplicateSpecialization (key : Key) (count : Nat)
  | specializationOwnershipMismatch
      (key : Key) (declaration functionDeclaration typedBodyOwner :
        Resolved.DeclarationId)
  | missingInstantiationTarget
      (declaration : Resolved.DeclarationId) (type : Ty)
  | duplicateInstantiationTargets
      (declaration : Resolved.DeclarationId) (type : Ty) (count : Nat)
  | invalidFunctionType (key : Key) (type : Ty)
  | inferredResultTypeMismatch (key : Key) (declared inferred : Ty)
  | unresolvedAssumptions (key : Key) (predicates : List ProgramPredicate)
  | runtimeEvidenceCountMismatch (key : Key) (expected actual : Nat)
  | runtimeEvidenceGoalMismatch
      (key : Key) (index : Nat)
      (expected actual : ProgramPredicate)
  | runtimeEvidenceResolutionNoSolution (key : Key)
      (predicate : ProgramPredicate)
  | runtimeEvidenceResolutionInconclusive (key : Key)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId Ty ProgramImplId)
  | missingRuntimeAssumptionEvidence
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | comptimeContract
      (key : Key) (parameterComptime : List Bool) (returnComptime : Bool)
  | markedBinder (id : Resolved.LocalId)
  | stagedBinderType (id : Resolved.LocalId) (type : Ty)
  | stagedResultType (key : Key) (type : Ty)
  | stagedExpressionType (id : ExpressionId) (type : Ty)
  | stagedLambdaResult (id : ExpressionId) (type : Ty)
  | unsupportedStagedInput (expected : Ty)
  | inputValidationFuelExhausted (expected : Ty) (fuel : Nat)
  | missingExpression (id : ExpressionId)
  | missingStatement (id : StatementId)
  | expectedStatementRoot (id : ExpressionId)
  | unboundLocal (id : Resolved.LocalId)
  | danglingLocation (location : Location)
  | uninitializedLocal (id : Resolved.LocalId)
  | duplicateCallEdge (caller : Key) (id : ExpressionId) (count : Nat)
  | missingCallEdge (caller : Key) (id : ExpressionId)
  | callRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (expected actual : Nat)
  | invalidDirectCallRequirementLayout
      (caller : Key) (id : ExpressionId)
      (requirements : List RequirementId)
  | duplicateCallRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | missingSolvedRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | duplicateSolvedRequirements
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (count : Nat)
  | callRequirementPredicateMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | callRequirementEvidenceGoalMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : ProgramPredicate)
  | unsupportedCallAssumptionEvidence
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (predicate : ProgramPredicate)
  | callEvidenceResolutionNoSolution
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (goal : ProgramPredicate)
  | callEvidenceResolutionInconclusive
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId Ty ProgramImplId)
  | callEvidenceNotSelected
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (goal : ProgramPredicate) (implementation : ProgramImplId)
  | localSchemeInstanceMismatch
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (expected actual : Ty)
  | localSchemeRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (expected actual : Nat)
  | duplicateLocalSchemeTemplateRequirement
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | duplicateLocalSchemeActualRequirement
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | localSchemeTemplateExpectedAssumption
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | localSchemeActualExpectedImplementation
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | nonGroundLocalSchemePredicate
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
      (requirement : RequirementId) (predicate : ProgramPredicate)
  | unsupportedQualifiedLocalReference
      (caller : Key) (id : ExpressionId) (binder : Resolved.LocalId)
  | unsupportedQualifiedLocalInitializer
      (caller : Key) (binder : Resolved.LocalId) (initializer : ExpressionId)
  | unsupportedLocalSchemeTemplateUse
      (caller : Key) (binder : Resolved.LocalId)
      (requirement : RequirementId)
  | unsupportedConstrainedDeclarationReference
      (caller : Key) (call callee : ExpressionId)
  | duplicateReferenceEdge (caller : Key) (id : ExpressionId) (count : Nat)
  | missingReferenceEdge (caller : Key) (id : ExpressionId)
  | declarationMetadataMismatch (call callee : ExpressionId)
  | malformedLiteral (id : ExpressionId)
  | literalMetadataMismatch (id : ExpressionId)
  | expectedBool (actual : Option Ty)
  | expectedWord (actual : Option Ty)
  | expectedInteger (actual : Option Ty)
  | expectedFunction (actual : Option Ty)
  | expectedMapping (actual : Option Ty)
  | expectedConstructor (actual : Option Ty)
  | expectedProduct (actual : Option Ty)
  | typeMismatch (expected : Ty) (actual : Option Ty)
  | resultTypeMismatch (expected : Ty) (actual : Option Ty)
  | argumentArityMismatch (expected actual : Nat)
  | invalidUnaryOperand (operator : Syntax.UnaryOp) (actual : Option Ty)
  | invalidBinaryOperands
      (operator : Syntax.BinaryOp) (left right : Option Ty)
  | invalidAssignmentOperands
      (operator : Syntax.ValueAssignOp) (left right : Option Ty)
  | invalidMember (name : String) (index : Nat) (actual : Option Ty)
  | invalidPlaceProjection
  | invalidExpressionCoercionPath
      (expression : ExpressionId) (source target : Ty)
  | invalidIndirectArgumentCoercionPath (expression : ExpressionId)
  | duplicateCoercionRequirement
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
  | coercionPredicateMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (source target : Ty) (actual : ProgramPredicate)
  | coercionTraitMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (trait : ProgramTraitId)
  | coercionMethodRequirementCountMismatch
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (expected actual : Nat)
  | executableCoercionMethod
      (caller : Key) (id : ExpressionId) (requirement : RequirementId)
      (error : ExecutableImplMethods.Error)
  | unsupportedCoercion (source target : Ty)
  | unsupportedRequirements (requirements : List RequirementId)
  | unsupportedExpressionCoercions (expression : ExpressionId)
  | unsupportedIndirectCoercions (expression : ExpressionId)
  | invalidLiteralEvidence (requirement : RequirementId)
  | invalidPatternMetadata
  | malformedPattern
  | controlEscapedFunction
  | functionFellThrough (expected : Ty)
  | invalidBuiltin (function : BuiltinFunctionId)
  deriving Repr, DecidableEq

inductive ExpressionResult where
  | done (value : Value) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)
  deriving Repr

/-- Explicit statement transfer.  Fallthrough, break, and continue retain the
current lexical environment so sequencing and loop headers can observe locals;
scoped constructs deliberately replace it with their entry environment. -/
inductive FlowOutcome where
  | fallthrough (environment : Environment) (state : RuntimeState)
  | returned (value : Value) (state : RuntimeState)
  | breaking (environment : Environment) (state : RuntimeState)
  | continuing (environment : Environment) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)
  deriving Repr

inductive RunResult where
  | done (value : Value) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)
  deriving Repr

def exactSpecialization (plan : Plan) (key : Key) :
    Except RuntimeError SourceSpecialization.SpecializedFunction :=
  match plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
  | [] => .error (.missingSpecialization key)
  | [specialized] => .ok specialized
  | candidates => .error (.duplicateSpecialization key candidates.length)

private def exactParameterBinding? (substitution : ParameterSubstitution)
    (parameter : TypeParameterId) : Option Ty :=
  match substitution.filter fun entry => entry.1 == parameter with
  | [entry] => some entry.2
  | _ => none

private def parameterSubstitutionsEquivalent
    (left right : ParameterSubstitution) : Bool :=
  left.length == right.length &&
    left.all (fun entry =>
      exactParameterBinding? right entry.1 == some entry.2) &&
    right.all fun entry =>
      exactParameterBinding? left entry.1 == some entry.2

private def specializationOwnershipCoherent
    (specialized : SourceSpecialization.SpecializedFunction) : Bool :=
  decide (specialized.key.declaration = specialized.declaration ∧
    specialized.function.declaration = specialized.declaration ∧
    specialized.function.typedBody.owner = specialized.declaration)

private def specializationMatchesInstantiation
    (specialized : SourceSpecialization.SpecializedFunction)
    (instantiation : DeclarationInstantiation) : Bool :=
  specializationOwnershipCoherent specialized &&
    specialized.key.arguments ==
      specialized.parameterSubstitution.map Prod.snd &&
    specialized.declaration == instantiation.declaration &&
    parameterSubstitutionsEquivalent specialized.parameterSubstitution
      instantiation.parameterSubstitution &&
    specialized.function.type == instantiation.type &&
    specialized.assumptions == instantiation.predicates &&
    specialized.function.typedBody.inputs.map (·.comptime) ==
      instantiation.parameterComptime &&
    specialized.function.returnComptime == instantiation.returnComptime

private def exactInstantiationKey (plan : Plan)
    (instantiation : DeclarationInstantiation) : Except RuntimeError Key :=
  match plan.specializations.filter fun specialized =>
      specializationMatchesInstantiation specialized instantiation with
  | [] => .error (.missingInstantiationTarget instantiation.declaration
      instantiation.type)
  | [specialized] => .ok specialized.key
  | candidates => .error (.duplicateInstantiationTargets
      instantiation.declaration instantiation.type candidates.length)

private def exactCallKey (plan : Plan) (caller : Key) (id : ExpressionId)
    (callee : Key) :
    Except RuntimeError Key :=
  match plan.callEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) &&
        decide (edge.callee = callee) with
  | [] => .error (.missingCallEdge caller id)
  | [edge] => .ok edge.callee
  | edges => .error (.duplicateCallEdge caller id edges.length)

private def exactReferenceKey (plan : Plan) (caller : Key)
    (id : ExpressionId) (callee : Key) : Except RuntimeError Key :=
  match plan.referenceEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) &&
        decide (edge.callee = callee) with
  | [] => .error (.missingReferenceEdge caller id)
  | [edge] => .ok edge.callee
  | edges => .error (.duplicateReferenceEdge caller id edges.length)

private def exactExpression (source : TypedSource) (id : ExpressionId) :
    Except RuntimeError ExpressionNode :=
  match source.lookupExpression? id with
  | some node => .ok node
  | none => .error (.missingExpression id)

private def exactStatement (source : TypedSource) (id : StatementId) :
    Except RuntimeError StatementNode :=
  match source.lookupStatement? id with
  | some node => .ok node
  | none => .error (.missingStatement id)

private def validateDirectDeclarationCallee (source : TypedSource)
    (call callee : ExpressionId)
    (instantiation : DeclarationInstantiation) : Except RuntimeError Unit :=
  match source.lookupExpression? callee with
  | some { type, form := .reference _ (.declaration reference), .. } =>
      if reference = instantiation && type = instantiation.type then
        pure ()
      else
        throw (.declarationMetadataMismatch call callee)
  | _ => throw (.declarationMetadataMismatch call callee)

private def exactSolvedRequirement? (function : CheckedFunction)
    (id : RequirementId) : Option SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.id == id with
  | [solved] => some solved
  | _ => none

private def firstDuplicateRequirement :
    List RequirementId → Option RequirementId
  | [] => none
  | requirement :: rest =>
      if rest.contains requirement then some requirement
      else firstDuplicateRequirement rest

private def coercionRequirementIds (steps : List CoercionStep) :
    List RequirementId :=
  steps.flatMap (fun step => step.requirements)

private def deduplicateRequirementLists
    (candidates : List (List RequirementId)) : List (List RequirementId) :=
  candidates.foldl (fun unique candidate =>
    if unique.contains candidate then unique else unique ++ [candidate]) []

/-- A direct call may carry a result path selected during overload resolution
before its signature predicates and a contextual result path after them.  The
IR deliberately concatenates both paths, so recover the unique middle ledger
by considering every path split and checking the stored order exactly. -/
private def directCallRequirementCandidates (node : ExpressionNode)
    (predicateCount : Nat) : List (List RequirementId) :=
  deduplicateRequirementLists <| (List.range (node.coercions.length + 1)).filterMap
    fun split =>
      let before := coercionRequirementIds (node.coercions.take split)
      let after := coercionRequirementIds (node.coercions.drop split)
      let middleAndAfter := node.requirements.drop before.length
      let middle := middleAndAfter.take predicateCount
      if node.requirements.take before.length = before &&
          middle.length = predicateCount &&
          middleAndAfter.drop predicateCount = after then
        some middle
      else
        none

private def requirementPredicatesMatch (function : CheckedFunction)
    (requirements : List RequirementId)
    (predicates : List ProgramPredicate) : Bool :=
  requirements.length == predicates.length &&
    (List.zip requirements predicates).all fun pair =>
      match exactSolvedRequirement? function pair.1 with
      | some solved => solved.predicate == pair.2 && solved.evidence.goal == pair.2
      | none => false

private def exactDirectCallRequirementIds
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError (List RequirementId) := do
  if node.coercions.isEmpty &&
      node.requirements.length != instantiation.predicates.length then
    throw (.callRequirementCountMismatch caller.key node.id
      instantiation.predicates.length node.requirements.length)
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateCallRequirement caller.key node.id requirement)
  | none => pure ()
  let structuralCandidates := directCallRequirementCandidates node
    instantiation.predicates.length
  let candidates := structuralCandidates.filter fun requirements =>
    requirementPredicatesMatch caller.function requirements
      instantiation.predicates
  match structuralCandidates with
  | [requirements] => return requirements
  | _ => pure ()
  match candidates with
  | [requirements] => pure requirements
  | _ => throw (.invalidDirectCallRequirementLayout caller.key node.id
      node.requirements)

private def ordinaryOwnedRequirements? (node : ExpressionNode) :
    Option (List RequirementId) :=
  let coercions := coercionRequirementIds node.coercions
  if node.requirements.length < coercions.length then
    none
  else
    let owned := node.requirements.take
      (node.requirements.length - coercions.length)
    if node.requirements = owned ++ coercions then some owned else none

private def directLambdaLetBinder? (source : TypedSource)
    (id : Resolved.LocalId) : Option TypedBinder :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id != id || binder.scheme.quantified.isEmpty then
          none
        else if SourceSpecialization.isDirectLambdaInitializer source
            initializer then
          some binder
        else
          none
    | _ => none

private def exactCallSolvedRequirement
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId) :
    Except RuntimeError SolvedRequirement :=
  let candidates := caller.function.solvedRequirements.filter fun solved =>
    decide (solved.id = requirement)
  match candidates with
  | [] => .error (.missingSolvedRequirement caller.key occurrence requirement)
  | [solved] => .ok solved
  | solved => .error (.duplicateSolvedRequirements caller.key occurrence
      requirement solved.length)

private def localRequirementWitnesses
    (caller : SourceSpecialization.SpecializedFunction)
    (binder : TypedBinder) (node : ExpressionNode) :
    Except RuntimeError (Substitution × List LocalRequirementWitness) := do
  let substitution ←
    match SourceSpecialization.matchClosedSchemeInstance? binder.scheme
        node.rawType with
    | some substitution => pure substitution
    | none => throw (.localSchemeInstanceMismatch caller.key node.id binder.id
        binder.scheme.body node.rawType)
  if binder.schemeRequirements.length != node.requirements.length then
    throw (.localSchemeRequirementCountMismatch caller.key node.id binder.id
      binder.schemeRequirements.length node.requirements.length)
  let templateIds := binder.schemeRequirements.map (·.templateRequirement)
  match firstDuplicateRequirement templateIds with
  | some requirement =>
      throw (.duplicateLocalSchemeTemplateRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  match firstDuplicateRequirement node.requirements with
  | some requirement =>
      throw (.duplicateLocalSchemeActualRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  let pairs := List.zip binder.schemeRequirements node.requirements
  let mut witnesses := []
  for (template, actualRequirement) in pairs do
    let templateSolved ← exactCallSolvedRequirement caller node.id
      template.templateRequirement
    if templateSolved.predicate != template.predicate then
      throw (.callRequirementPredicateMismatch caller.key node.id
        template.templateRequirement template.predicate
        templateSolved.predicate)
    if templateSolved.evidence.goal != template.predicate then
      throw (.callRequirementEvidenceGoalMismatch caller.key node.id
        template.templateRequirement template.predicate
        templateSolved.evidence.goal)
    match templateSolved.evidence with
    | .assumption _ => pure ()
    | .implementation _ =>
        throw (.localSchemeTemplateExpectedAssumption caller.key node.id
          binder.id template.templateRequirement)
    let predicate :=
      (template.applySubstitution substitution).predicate
    if !(TypedTraitResolution.predicateVariables predicate).isEmpty then
      throw (.nonGroundLocalSchemePredicate caller.key node.id binder.id
        actualRequirement predicate)
    let actualSolved ← exactCallSolvedRequirement caller node.id
      actualRequirement
    if actualSolved.predicate != predicate then
      throw (.callRequirementPredicateMismatch caller.key node.id
        actualRequirement predicate actualSolved.predicate)
    if actualSolved.evidence.goal != predicate then
      throw (.callRequirementEvidenceGoalMismatch caller.key node.id
        actualRequirement predicate actualSolved.evidence.goal)
    let evidence ← match actualSolved.evidence with
      | .implementation evidence => pure evidence
      | .assumption _ =>
          throw (.localSchemeActualExpectedImplementation caller.key node.id
            binder.id actualRequirement)
    witnesses := witnesses ++ [{
      templateRequirement := template.templateRequirement
      actualRequirement
      predicate
      evidence
    }]
  pure (substitution, witnesses)

private def runtimeEvidenceGoal :
    TypedTraitResolution.Evidence → ProgramPredicate
  | .byImpl goal _ _ => goal

private def validateRuntimeEvidenceGoals (key : Key) :
    Nat → List ProgramPredicate → RuntimeEvidenceEnvironment →
      Except RuntimeError Unit
  | _, [], [] => pure ()
  | index, expected :: expectedRest, evidence :: evidenceRest => do
      let actual := runtimeEvidenceGoal evidence
      if actual = expected then
        validateRuntimeEvidenceGoals key (index + 1) expectedRest evidenceRest
      else
        throw (.runtimeEvidenceGoalMismatch key index expected actual)
  | _, expected, evidence =>
      throw (.runtimeEvidenceCountMismatch key expected.length evidence.length)

/-- Check the closed dictionary at a specialization boundary.  Its carrier
already rules out assumption leaves; this additionally fixes source order and
multiplicity to the callee's specialized `where` predicates. -/
private def validateRuntimeEvidence (key : Key)
    (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment) : Except RuntimeError Unit := do
  if predicates.length = environment.length then
    validateRuntimeEvidenceGoals key 0 predicates environment
  else
    throw (.runtimeEvidenceCountMismatch key predicates.length
      environment.length)

private theorem validateRuntimeEvidenceGoals_success
    (key : Key) (index : Nat) (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment)
    (success : validateRuntimeEvidenceGoals key index predicates environment =
      .ok ()) :
    environment.Matches predicates := by
  induction predicates generalizing index environment with
  | nil =>
      cases environment with
      | nil => rfl
      | cons evidence rest =>
          simp [validateRuntimeEvidenceGoals] at success
  | cons predicate predicates induction =>
      cases environment with
      | nil => simp [validateRuntimeEvidenceGoals] at success
      | cons evidence rest =>
          cases evidence with
          | byImpl goal implementation premises =>
              by_cases same : goal = predicate
              · have tailSuccess :
                    validateRuntimeEvidenceGoals key (index + 1) predicates
                      rest = .ok () := by
                  simpa [validateRuntimeEvidenceGoals, runtimeEvidenceGoal,
                    same] using success
                have tail := induction (index := index + 1)
                  (environment := rest) tailSuccess
                unfold RuntimeEvidenceEnvironment.Matches
                  RuntimeEvidenceEnvironment.goals at tail ⊢
                simp [same, tail]
              · simp [validateRuntimeEvidenceGoals, runtimeEvidenceGoal,
                  same] at success

/-- Successful executable validation exposes the ordered closed-dictionary
invariant used by the evaluator boundary. -/
private theorem validateRuntimeEvidence_success_matches
    (key : Key) (predicates : List ProgramPredicate)
    (environment : RuntimeEvidenceEnvironment)
    (success : validateRuntimeEvidence key predicates environment = .ok ()) :
    environment.Matches predicates := by
  unfold validateRuntimeEvidence at success
  split at success
  · exact validateRuntimeEvidenceGoals_success key 0 predicates environment
      success
  · simp at success

private def availableRuntimeEvidence?
    (environment : RuntimeEvidenceEnvironment)
    (predicate : ProgramPredicate) : Option TypedTraitResolution.Evidence :=
  environment.find? fun evidence =>
    decide (runtimeEvidenceGoal evidence = predicate)

/-- Materialize call evidence in the callee declaration's predicate order.
Concrete implementation evidence is retained verbatim.  A caller assumption
is closed by the dictionary supplied when the caller specialization was
entered; no trait search occurs during execution. -/
private def materializeCallEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId)
    (available : RuntimeEvidenceEnvironment) :
    List RequirementId → List ProgramPredicate →
      Except RuntimeError RuntimeEvidenceEnvironment
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      if solved.predicate != predicate then
        throw (.callRequirementPredicateMismatch caller.key occurrence
          requirement predicate solved.predicate)
      let goal := solved.evidence.goal
      if goal != solved.predicate then
        throw (.callRequirementEvidenceGoalMismatch caller.key occurrence
          requirement solved.predicate goal)
      let evidence ← match solved.evidence with
        | .implementation evidence => pure evidence
        | .assumption assumption =>
            match availableRuntimeEvidence? available assumption with
            | some evidence => pure evidence
            | none => throw (.missingRuntimeAssumptionEvidence caller.key
                occurrence requirement assumption)
      pure (evidence :: (← materializeCallEvidence caller occurrence available
        requirements predicates))
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def exactDirectCallRuntimeEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (instantiation : DeclarationInstantiation) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  materializeCallEvidence caller node.id available requirements
    instantiation.predicates

private def validateSelectedCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) (requirement : RequirementId)
    (goal : ProgramPredicate) (evidence : TypedTraitResolution.Evidence) :
    Except RuntimeError Unit :=
  match (TypedTraitResolution.resolve signatures.resolutionRules 32 goal).outcome with
  | .noSolution =>
      .error (.callEvidenceResolutionNoSolution caller.key occurrence
        requirement goal)
  | .inconclusive reason =>
      .error (.callEvidenceResolutionInconclusive caller.key occurrence
        requirement reason)
  | .success selected =>
      if selected == evidence then
        .ok ()
      else
        let .byImpl _ implementation _ := evidence
        .error (.callEvidenceNotSelected caller.key occurrence requirement
          goal implementation)

/-- Recover one concrete requirement witness at runtime.  Assumption markers
are discharged from the caller's closed dictionary; concrete witnesses are
authenticated again against the authoritative whole-program resolver. -/
private def exactRuntimeRequirementEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (requirement : RequirementId) (expected : ProgramPredicate) :
    Except RuntimeError TypedTraitResolution.Evidence := do
  let solved ← exactCallSolvedRequirement caller node.id requirement
  if solved.predicate != expected then
    throw (.callRequirementPredicateMismatch caller.key node.id requirement
      expected solved.predicate)
  if solved.evidence.goal != expected then
    throw (.callRequirementEvidenceGoalMismatch caller.key node.id requirement
      expected solved.evidence.goal)
  let evidence ← match solved.evidence with
    | .implementation evidence => pure evidence
    | .assumption predicate =>
        match availableRuntimeEvidence? available predicate with
        | some evidence => pure evidence
        | none => throw (.missingRuntimeAssumptionEvidence caller.key node.id
            requirement predicate)
  validateSelectedCallImplementationEvidence program.signatures caller node.id
    requirement expected evidence
  pure evidence

private def exactRuntimeRequirementEvidenceList (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment) :
    List RequirementId → List ProgramPredicate →
      Except RuntimeError (List TypedTraitResolution.Evidence)
  | [], [] => pure []
  | requirement :: requirements, predicate :: predicates => do
      let evidence ← exactRuntimeRequirementEvidence program caller node
        available requirement predicate
      pure (evidence :: (← exactRuntimeRequirementEvidenceList program caller
        node available requirements predicates))
  | requirements, predicates =>
      throw (.coercionMethodRequirementCountMismatch caller.key node.id
        { index := 0 } predicates.length requirements.length)

/-- Authenticate one retained `Coerce<From, To>` edge and recover the exact
checked implementation method selected by its evidence. -/
private def checkedCoercionMethod (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (available : RuntimeEvidenceEnvironment)
    (step : CoercionStep) :
    Except RuntimeError ExecutableImplMethods.CheckedMethod := do
  match firstDuplicateRequirement step.requirements with
  | some requirement =>
      throw (.duplicateCoercionRequirement caller.key node.id requirement)
  | none => pure ()
  let solved ← exactCallSolvedRequirement caller node.id step.requirement
  let predicate := solved.predicate
  unless predicate.subject = step.source && predicate.arguments = [step.target] do
    throw (.coercionPredicateMismatch caller.key node.id step.requirement
      step.source step.target predicate)
  let traitId ← match predicate.trait with
    | .declaration id => pure id
    | trait => throw (.coercionTraitMismatch caller.key node.id
        step.requirement trait)
  let trait ← match program.signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.coercionTraitMismatch caller.key node.id
        step.requirement predicate.trait)
  unless trait.name = "Coerce" && trait.parameters.length = 2 do
    throw (.coercionTraitMismatch caller.key node.id step.requirement
      predicate.trait)
  let traitMethod ← match trait.methods.filter fun method =>
      method.name == "coerce" with
    | [method] => pure method
    | [] => throw (.executableCoercionMethod caller.key node.id
        step.requirement (.missingTraitMethod trait.id "coerce"))
    | methods => throw (.executableCoercionMethod caller.key node.id
        step.requirement (.multipleTraitMethods trait.id methods.length))
  let substitution : ParameterSubstitution :=
    trait.parameters.zip [predicate.subject, step.target]
  let methodPredicates := traitMethod.wherePredicates.map
    (ProgramPredicate.applyParameters substitution)
  if step.methodRequirements.length != methodPredicates.length then
    throw (.coercionMethodRequirementCountMismatch caller.key node.id
      step.requirement methodPredicates.length step.methodRequirements.length)
  let primary ← exactRuntimeRequirementEvidence program caller node available
    step.requirement predicate
  let methodEvidence ← exactRuntimeRequirementEvidenceList program caller node
    available step.methodRequirements methodPredicates
  (ExecutableImplMethods.checkMethodWithEvidenceAndArity program primary
    methodEvidence 2 "coerce").mapError fun error =>
      .executableCoercionMethod caller.key node.id step.requirement error

private def resolveClosedCoercionEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (requirement : RequirementId) :
    List ProgramPredicate →
      Except RuntimeError (List TypedTraitResolution.Evidence)
  | [] => pure []
  | predicate :: predicates =>
      match (TypedTraitResolution.resolve program.signatures.resolutionRules 32
          predicate).outcome with
      | .noSolution =>
          throw (.callEvidenceResolutionNoSolution caller.key node.id
            requirement predicate)
      | .inconclusive reason =>
          throw (.callEvidenceResolutionInconclusive caller.key node.id
            requirement reason)
      | .success evidence => do
          let .byImpl goal _ _ := evidence
          if goal != predicate then
            throw (.callRequirementEvidenceGoalMismatch caller.key node.id
              requirement predicate goal)
          pure (evidence :: (← resolveClosedCoercionEvidence program caller
            node requirement predicates))

/-- The synthetic checked method lists trait-header, implementation-head, and
method predicates in that order.  Reconstruct the same closed runtime
dictionary rather than depending on incidental evidence-list order. -/
private def coercionMethodRuntimeEvidence (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep)
    (method : ExecutableImplMethods.CheckedMethod) :
    Except RuntimeError RuntimeEvidenceEnvironment := do
  let traitEvidence ← resolveClosedCoercionEvidence program caller node
    step.requirement method.traitPredicates
  let environment := traitEvidence ++ method.implementationPremises ++
    method.methodPremises
  validateRuntimeEvidence method.specialized.key method.specialized.assumptions
    environment
  pure environment

private def resolveRuntimeEvidenceEnvironment (program : CheckedProgram)
    (key : Key) : List ProgramPredicate →
      Except RuntimeError RuntimeEvidenceEnvironment
  | [] => pure []
  | predicate :: predicates =>
      match (TypedTraitResolution.resolve program.signatures.resolutionRules 32
          predicate).outcome with
      | .noSolution =>
          throw (.runtimeEvidenceResolutionNoSolution key predicate)
      | .inconclusive reason =>
          throw (.runtimeEvidenceResolutionInconclusive key reason)
      | .success evidence => do
          let .byImpl goal _ _ := evidence
          if goal != predicate then
            throw (.runtimeEvidenceGoalMismatch key 0 predicate goal)
          pure (evidence :: (← resolveRuntimeEvidenceEnvironment program key
            predicates))

private def directLambdaBodyRoots? (source : TypedSource)
    (binderId : Resolved.LocalId) : Option (List NodeId) :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id != binderId then
          none
        else
          match source.lookupExpression? initializer with
          | some { form := .lambda _ _ body, .. } =>
              some (body.map NodeId.statement)
          | _ => none
    | _ => none

private def directLambdaInitializer? (source : TypedSource)
    (binderId : Resolved.LocalId) : Option ExpressionId :=
  source.nodes.findSome? fun
    | .statement { form := .letDecl binder (some initializer), .. } =>
        if binder.id == binderId &&
            SourceSpecialization.isDirectLambdaInitializer source initializer then
          some initializer
        else
          none
    | _ => none

private def directLexicalChildren (source : TypedSource)
    (id : NodeId) : List NodeId :=
  match source.lookupNode? id.occurrenceId with
  | some (.expression { form := .lambda _ _ _, .. }) => []
  | some (.expression node) =>
      SourceSpecialization.expressionChildNodeIds node
  | some (.statement node) =>
      SourceSpecialization.statementChildNodeIds source node
  | none => []

private def directLexicalFuel (source : TypedSource)
    (roots : List NodeId) : Nat :=
  roots.length + source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (SourceSpecialization.expressionChildNodeIds expression).length
      | .statement statement =>
          (SourceSpecialization.statementChildNodeIds source statement).length) 0 + 1

private def collectDirectLexicalNodes (source : TypedSource) :
    Nat → List NodeId → List NodeId → List NodeId
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, pending :: rest, seen =>
      if seen.contains pending then
        collectDirectLexicalNodes source fuel rest seen
      else
        let nextSeen := seen ++ [pending]
        let children := (directLexicalChildren source pending).filter fun child =>
          !nextSeen.contains child && !rest.contains child
        collectDirectLexicalNodes source fuel (rest ++ children) nextSeen

private def directLambdaBodyContains (source : TypedSource)
    (binder : TypedBinder) (occurrence : ExpressionId) : Bool :=
  match directLambdaBodyRoots? source binder.id with
  | none => false
  | some roots =>
      (collectDirectLexicalNodes source (directLexicalFuel source roots)
        roots []).contains (.expression occurrence)

private def expressionRequirementCount (source : TypedSource)
    (requirement : RequirementId) : Nat :=
  source.nodes.foldl (fun count node =>
    match node with
    | .expression expression =>
        count + (expression.requirements.filter fun candidate =>
          candidate == requirement).length
    | .statement _ => count) 0

private def scopedLocalTemplateOwner? (source : TypedSource)
    (occurrence : ExpressionId) (requirement : RequirementId)
    (predicate : ProgramPredicate) : Option TypedBinder :=
  if expressionRequirementCount source requirement != 1 then
    none
  else
    match source.nodes.filterMap fun
      | .statement { form := .letDecl binder (some initializer), .. } =>
          if binder.scheme.quantified.isEmpty ||
              !SourceSpecialization.isDirectLambdaInitializer source initializer ||
              !directLambdaBodyContains source binder occurrence ||
              !(binder.schemeRequirements.any fun owned =>
                owned.templateRequirement == requirement &&
                  owned.predicate == predicate) then
            none
          else
            some binder
      | _ => none with
    | [binder] => some binder
    | _ => none

private def validateExecutableCallRequirementEvidence
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    List RequirementId → List ProgramPredicate → Except RuntimeError Unit
  | [], [] => pure ()
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      if solved.predicate != predicate then
        throw (.callRequirementPredicateMismatch caller.key occurrence
          requirement predicate solved.predicate)
      if solved.evidence.goal != predicate then
        throw (.callRequirementEvidenceGoalMismatch caller.key occurrence
          requirement predicate solved.evidence.goal)
      match solved.evidence with
      | .implementation _ => pure ()
      | .assumption assumption =>
          let declarationAssumption := caller.assumptions.contains predicate
          let localTemplate :=
            (scopedLocalTemplateOwner? caller.function.typedBody occurrence
              requirement predicate).isSome
          unless declarationAssumption || localTemplate do
            throw (.unsupportedCallAssumptionEvidence caller.key occurrence
              requirement assumption)
      validateExecutableCallRequirementEvidence caller occurrence requirements
        predicates
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def validateExecutableDirectCallRequirements
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  validateExecutableCallRequirementEvidence caller node.id requirements
    instantiation.predicates

private def validateExecutableCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (occurrence : ExpressionId) :
    List RequirementId → List ProgramPredicate → Except RuntimeError Unit
  | [], [] => pure ()
  | requirement :: requirements, predicate :: predicates => do
      let solved ← exactCallSolvedRequirement caller occurrence requirement
      match solved.evidence with
      | .assumption _ => pure ()
      | .implementation evidence =>
          validateSelectedCallImplementationEvidence signatures caller
            occurrence requirement predicate evidence
      validateExecutableCallImplementationEvidence signatures caller occurrence
        requirements predicates
  | requirements, predicates =>
      throw (.callRequirementCountMismatch caller.key occurrence
        predicates.length requirements.length)

private def validateExecutableDirectCallImplementationEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    Except RuntimeError Unit := do
  validateExecutableDirectCallRequirements caller node instantiation
  let requirements ← exactDirectCallRequirementIds caller node instantiation
  validateExecutableCallImplementationEvidence signatures caller node.id
    requirements instantiation.predicates

private def nodeUseCount (source : TypedSource) (target : NodeId) : Nat :=
  let rootCount := (source.roots.filter fun root => root == target).length
  source.nodes.foldl (fun count node =>
    count + match node with
      | .expression expression =>
          (SourceSpecialization.expressionChildNodeIds expression |>.filter
            fun child => child == target).length
      | .statement statement =>
          (SourceSpecialization.statementChildNodeIds source statement |>.filter
            fun child => child == target).length) rootCount

private def indirectCalleeUseCount (source : TypedSource)
    (target : ExpressionId) : Nat :=
  source.nodes.foldl (fun count node =>
    match node with
    | .expression { form := .call callee _ (.indirect _), .. } =>
        if callee == target then count + 1 else count
    | _ => count) 0

private def isExclusiveIndirectCallee (source : TypedSource)
    (target : ExpressionId) : Bool :=
  indirectCalleeUseCount source target == 1 &&
    nodeUseCount source (.expression target) == 1

private def directDeclarationCalleeUseCount (source : TypedSource)
    (target : ExpressionId) : Nat :=
  source.nodes.foldl (fun count node =>
    match node with
    | .expression { form := .call callee _ (.declaration _), .. } =>
        if callee == target then count + 1 else count
    | _ => count) 0

private def validateQualifiedLocalTemplateCoverage
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (binder : TypedBinder) : Except RuntimeError Unit := do
  let templateIds := binder.schemeRequirements.map (·.templateRequirement)
  match firstDuplicateRequirement templateIds with
  | some requirement =>
      throw (.duplicateLocalSchemeTemplateRequirement caller.key node.id
        binder.id requirement)
  | none => pure ()
  let source := caller.function.typedBody
  let initializer ← match directLambdaInitializer? source binder.id with
    | some initializer => pure initializer
    | none => throw (.unsupportedQualifiedLocalReference caller.key node.id
        binder.id)
  unless nodeUseCount source (.expression initializer) == 1 do
    throw (.unsupportedQualifiedLocalInitializer caller.key binder.id initializer)
  let templateCalls := source.nodes.filterMap fun
    | .expression expression@{
        form := .call _ _ (.declaration instantiation), .. } =>
        if expression.requirements.any templateIds.contains then
          some (expression, instantiation)
        else
          none
    | _ => none
  for (call, instantiation) in templateCalls do
    let expected := binder.schemeRequirements.filter fun template =>
      call.requirements.contains template.templateRequirement
    let actual := (List.zip call.requirements instantiation.predicates).filter
      fun pair => templateIds.contains pair.1
    unless actual.map Prod.fst == expected.map (·.templateRequirement) &&
        actual.map Prod.snd == expected.map (·.predicate) do
      match expected.head? with
      | some first =>
          throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
            first.templateRequirement)
      | none => throw (.unsupportedRequirements call.requirements)
  for template in binder.schemeRequirements do
    let uses := source.nodes.filterMap fun
      | .expression expression =>
          if expression.requirements.contains template.templateRequirement then
            some expression
          else
            none
      | .statement _ => none
    let (call, callee, instantiation) ← match uses with
      | [call] =>
          match call.form with
          | .call callee _ (.declaration instantiation) =>
              pure (call, callee, instantiation)
          | _ => throw (.unsupportedLocalSchemeTemplateUse caller.key
              binder.id template.templateRequirement)
      | _ => throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
          template.templateRequirement)
    unless directLambdaBodyContains source binder call.id do
      throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
        template.templateRequirement)
    unless call.requirements.length == instantiation.predicates.length &&
        (List.zip call.requirements instantiation.predicates).any (fun pair =>
          pair.1 == template.templateRequirement &&
            pair.2 == template.predicate) do
      throw (.unsupportedLocalSchemeTemplateUse caller.key binder.id
        template.templateRequirement)
    unless directDeclarationCalleeUseCount source callee == 1 &&
        nodeUseCount source (.expression callee) == 1 do
      throw (.unsupportedConstrainedDeclarationReference caller.key call.id
        callee)

private def validateQualifiedLocalReference
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (binder : TypedBinder) :
    Except RuntimeError (List LocalRequirementWitness) := do
  validateQualifiedLocalTemplateCoverage caller node binder
  unless isExclusiveIndirectCallee caller.function.typedBody node.id do
    throw (.unsupportedQualifiedLocalReference caller.key node.id binder.id)
  let (_, witnesses) ← localRequirementWitnesses caller binder node
  pure witnesses

private def validateQualifiedLocalReferenceEvidence
    (signatures : ProgramSignatures)
    (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (binder : TypedBinder) : Except RuntimeError Unit := do
  let witnesses ← validateQualifiedLocalReference caller node binder
  for witness in witnesses do
    validateSelectedCallImplementationEvidence signatures caller node.id
      witness.actualRequirement witness.predicate witness.evidence

private def literalEvidenceIsBuiltin (function : CheckedFunction)
    (resolution : IntegerLiteralResolution) : Bool :=
  match exactSolvedRequirement? function resolution.requirement with
  | none => false
  | some solved =>
      let expected := ProgramSignatures.builtinIntPredicate resolution.targetType
      solved.predicate == expected &&
        match solved.evidence with
        | .assumption _ => false
        | .implementation (.byImpl goal implementation premises) =>
            goal == expected && premises.isEmpty &&
              match resolution.targetType with
              | .constructor (.builtin .word) =>
                  implementation == ProgramImplId.builtin .intWord
              | .constructor (.builtin .integer) =>
                  implementation == ProgramImplId.builtin .intInteger
              | _ => false

private def validateLiteralResolution (function : CheckedFunction)
    (source : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) : Except RuntimeError Unit := do
  unless numericLiteralValue? source = some resolution.rawValue &&
      literalEvidenceIsBuiltin function resolution do
    throw (.invalidLiteralEvidence resolution.requirement)

private def patternLiteralResolutions :
    List MatchPatternInstruction →
      List (Syntax.CoreLiteralValue × IntegerLiteralResolution)
  | [] => []
  | .integerLiteral source resolution :: rest =>
      (source, resolution) :: patternLiteralResolutions rest
  | _ :: rest => patternLiteralResolutions rest

private def patternLiterals (pattern : TypedMatchPattern) :
    List (Syntax.CoreLiteralValue × IntegerLiteralResolution) :=
  match pattern.resolution with
  | .integerLiteral source resolution => [(source, resolution)]
  | .constructor _ instructions
  | .tuple instructions => patternLiteralResolutions instructions
  | .wildcard | .binder _ => []

private def validatePatternMetadata (function : CheckedFunction)
    (pattern : TypedMatchPattern) : Except RuntimeError Unit := do
  let literals := patternLiterals pattern
  unless pattern.requirements = literals.map fun entry => entry.2.requirement do
    throw .invalidPatternMetadata
  for literal in literals do
    validateLiteralResolution function literal.1 literal.2

private def validateAssignmentMetadata
    (assignment : AssignmentResolution) : Except RuntimeError Unit :=
  unless assignment.requirements.isEmpty do
    throw (.unsupportedRequirements assignment.requirements)

private def validateForItemMetadata : ForItemForm → Except RuntimeError Unit
  | .assignValue assignment _ _
  | .assignBitNot assignment => validateAssignmentMetadata assignment
  | .letDecl _ _ | .expression _ => pure ()

private def validateExpressionMetadata
    (specialized : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Except RuntimeError Unit := do
  let function := specialized.function
  unless node.hasValidCoercionPath do
    throw (.invalidExpressionCoercionPath node.id node.rawType node.type)
  match node.form with
  | .integerLiteral source resolution =>
      unless node.requirements =
          [resolution.requirement] ++ coercionRequirementIds node.coercions do
        throw (.unsupportedRequirements node.requirements)
      validateLiteralResolution function source resolution
  | .call _ arguments (.indirect metadata) =>
      unless arguments.length = metadata.argumentCount do
        throw (.argumentArityMismatch metadata.argumentCount arguments.length)
      unless metadata.hasValidArgumentCoercionPath do
        throw (.invalidIndirectArgumentCoercionPath node.id)
      unless node.requirements =
          coercionRequirementIds metadata.argumentCoercions ++
            coercionRequirementIds node.coercions do
        throw (.unsupportedRequirements node.requirements)
  | .call _ _ (.declaration instantiation) =>
      validateExecutableDirectCallRequirements specialized node instantiation
  | .reference _ (.local binderId) =>
      let owned ← match ordinaryOwnedRequirements? node with
        | some requirements => pure requirements
        | none => throw (.unsupportedRequirements node.requirements)
      let ownedNode := { node with requirements := owned, coercions := [] }
      match directLambdaLetBinder? function.typedBody binderId with
      | some binder =>
          if binder.schemeRequirements.isEmpty then
            unless owned.isEmpty do
              throw (.unsupportedRequirements owned)
          else
            discard <| validateQualifiedLocalReference specialized ownedNode binder
      | none =>
          unless owned.isEmpty do
            throw (.unsupportedRequirements owned)
  | _ =>
      match ordinaryOwnedRequirements? node with
      | some [] => pure ()
      | _ => throw (.unsupportedRequirements node.requirements)

private def validateStatementMetadata (function : CheckedFunction) :
    StatementForm → Except RuntimeError Unit
  | .assignValue assignment _ _
  | .assignBitNot assignment => validateAssignmentMetadata assignment
  | .matchWith resolution => do
      let expected := resolution.cases.flatMap fun arm =>
        arm.pattern.requirements
      unless resolution.requirements = expected do
        throw .invalidPatternMetadata
      for arm in resolution.cases do
        validatePatternMetadata function arm.pattern
  | .forLoop initializer _ post _ =>
      for item in initializer ++ post do
        validateForItemMetadata item
  | _ => pure ()

/-- The effectful runtime implements builtin operations directly, but does not
silently reinterpret user-selected trait methods or coercions as builtins. -/
private def validateExecutableMetadata
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit :=
  let function := specialized.function
  for node in function.typedBody.nodes do
    match node with
    | .expression expression =>
        validateExpressionMetadata specialized expression
    | .statement statement => validateStatementMetadata function statement.form

private def typeContainsStaged : Ty → Bool
  | .constructor (.builtin .integer)
  | .comptime _ => true
  | .application function argument
  | .function function argument
  | .product function argument
  | .mapping function argument =>
      typeContainsStaged function || typeContainsStaged argument
  | .proxy inner => typeContainsStaged inner
  | .variable _ | .parameter _ | .constructor _ | .error => false

private def validateRuntimeBinder (binder : TypedBinder) :
    Except RuntimeError Unit := do
  if binder.comptime then throw (.markedBinder binder.id)
  if typeContainsStaged binder.scheme.body then
    throw (.stagedBinderType binder.id binder.scheme.body)

private def validateForItemBinder : ForItemForm → Except RuntimeError Unit
  | .letDecl binder _ => validateRuntimeBinder binder
  | .expression _ | .assignValue _ _ _ | .assignBitNot _ => pure ()

private def validatePatternInstructionBinder :
    MatchPatternInstruction → Except RuntimeError Unit
  | .binder binder => validateRuntimeBinder binder
  | .wildcard | .integerLiteral _ _ | .constructor _ _ | .tuple _ => pure ()

private def validatePatternBinders (pattern : TypedMatchPattern) :
    Except RuntimeError Unit := do
  match pattern.resolution with
  | .binder binder => validateRuntimeBinder binder
  | .constructor _ instructions | .tuple instructions =>
      for instruction in instructions do
        validatePatternInstructionBinder instruction
  | .wildcard | .integerLiteral _ _ => pure ()

private def validateRuntimeBinders (function : CheckedFunction) :
    Except RuntimeError Unit := do
  for node in function.typedBody.nodes do
    match node with
    | .expression expression => do
        if typeContainsStaged expression.type then
          throw (.stagedExpressionType expression.id expression.type)
        match expression.form with
        | .lambda parameters resultType _ => do
            for parameter in parameters do validateRuntimeBinder parameter
            if typeContainsStaged resultType then
              throw (.stagedLambdaResult expression.id resultType)
        | _ => pure ()
    | .statement { form := .letDecl binder _, .. } =>
        validateRuntimeBinder binder
    | .statement { form := .forLoop initializer _ post _, .. } =>
        for item in initializer ++ post do validateForItemBinder item
    | .statement { form := .matchWith resolution, .. } =>
        for arm in resolution.cases do validatePatternBinders arm.pattern
    | _ => pure ()

private def validateSpecializationMetadataWith
    (allowAssumptions : Bool)
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit := do
  unless specializationOwnershipCoherent specialized do
    throw (.specializationOwnershipMismatch specialized.key
      specialized.declaration specialized.function.declaration
      specialized.function.typedBody.owner)
  unless allowAssumptions || specialized.assumptions.isEmpty do
    throw (.unresolvedAssumptions specialized.key specialized.assumptions)
  let parameterComptime :=
    specialized.function.typedBody.inputs.map (·.comptime)
  if parameterComptime.any fun marked => marked then
    throw (.comptimeContract specialized.key parameterComptime
      specialized.function.returnComptime)
  if specialized.function.returnComptime then
    throw (.comptimeContract specialized.key parameterComptime true)
  if typeContainsStaged specialized.function.inferredBodyType then
    throw (.stagedResultType specialized.key
      specialized.function.inferredBodyType)
  for binder in specialized.function.typedBody.inputs do
    validateRuntimeBinder binder
  validateRuntimeBinders specialized.function
  validateExecutableMetadata specialized
  let declaredResult ← match resultType? specialized.function with
    | some result => pure result
    | none => throw (.invalidFunctionType specialized.key
        specialized.function.type)
  unless declaredResult = specialized.function.inferredBodyType do
    throw (.inferredResultTypeMismatch specialized.key declaredResult
      specialized.function.inferredBodyType)

private def validateSpecializationMetadata
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit :=
  validateSpecializationMetadataWith false specialized

/-- Assumptions are executable only for a specialization reached exclusively
as a direct-call target.  Public seeds and first-class declaration references
continue to use the closed-specialization contract. -/
private def allowsDirectAssumptionInvocation (plan : Plan) (key : Key) : Bool :=
  plan.callEdges.any (fun edge => edge.callee == key) &&
    !plan.seedKeys.contains key &&
    !plan.referenceEdges.any fun edge => edge.callee == key

/-- Preflight every reachable specialization before selecting this runtime as
an executable backend.  The canonical worklist has already fixed the finite
call graph; this pass rejects metadata which the typed runtime deliberately
does not dispatch instead of postponing that rejection until a call happens. -/
def validateExecutablePlan (plan : Plan) : Except RuntimeError Unit := do
  for specialized in plan.specializations do
    validateSpecializationMetadataWith
      (allowsDirectAssumptionInvocation plan specialized.key) specialized

/-- Signature-aware safe-boundary validation.  The structural pass retains
its existing diagnostics and ordering; the second pass authenticates every
implementation witness used by a direct declaration call against the
authoritative resolution catalog. -/
def validateExecutablePlanEvidence (program : CheckedProgram)
    (plan : Plan) : Except RuntimeError Unit := do
  validateExecutablePlan plan
  for specialized in plan.specializations do
    let available ← resolveRuntimeEvidenceEnvironment program specialized.key
      specialized.assumptions
    for sourceNode in specialized.function.typedBody.nodes do
      match sourceNode with
      | .expression node =>
          for step in node.coercions do
            let method ← checkedCoercionMethod program specialized node
              available step
            discard <| coercionMethodRuntimeEvidence program specialized node
              step method
          match node.form with
          | .call _ _ (.indirect metadata) =>
              for step in metadata.argumentCoercions do
                let method ← checkedCoercionMethod program specialized node
                  available step
                discard <| coercionMethodRuntimeEvidence program specialized
                  node step method
          | _ => pure ()
          match node.form with
          | .call _ _ (.declaration instantiation) =>
              validateExecutableDirectCallImplementationEvidence
                program.signatures
                specialized node instantiation
          | .reference _ (.local binderId) =>
              match directLambdaLetBinder?
                  specialized.function.typedBody binderId with
              | some binder =>
                  unless binder.schemeRequirements.isEmpty do
                    validateQualifiedLocalReferenceEvidence program.signatures
                      specialized node binder
              | none => pure ()
          | _ => pure ()
      | .statement _ => pure ()

private def applyCoercion (plan : Plan) (step : CoercionStep)
    (value : Value) : Except RuntimeError Value := do
  if value.type? plan != some step.source then
    throw (.typeMismatch step.source (value.type? plan))
  if step.source = step.target then
    pure value
  else
    match value, step.source, step.target with
    | .integer integer, .constructor (.builtin .integer),
        .constructor (.builtin .word) =>
        pure (.word (Core.Word.ofIntModulo integer))
    | .word word, .constructor (.builtin .word),
        .constructor (.builtin .integer) =>
        pure (.integer (Int.ofNat word.val))
    | _, _, _ => throw (.unsupportedCoercion step.source step.target)

private def applyCoercions (plan : Plan) :
    List CoercionStep → Value → Except RuntimeError Value
  | [], value => pure value
  | step :: rest, value => do
      applyCoercions plan rest (← applyCoercion plan step value)

private def finishExpression (plan : Plan) (node : ExpressionNode)
    (result : ExpressionResult) : ExpressionResult :=
  match result with
  | .done value state =>
      match applyCoercions plan node.coercions value with
      | .error error => .fault error state
      | .ok coerced =>
          if coerced.type? plan = some node.type then .done coerced state
          else .fault (.typeMismatch node.type (coerced.type? plan)) state
  | .outOfFuel state => .outOfFuel state
  | .fault error state => .fault error state

private inductive ValuesResult where
  | done (values : List Value) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)

private def evaluateList
    (evaluateOne : RuntimeState → ExpressionId → ExpressionResult) :
    RuntimeState → List ExpressionId → ValuesResult
  | state, [] => .done [] state
  | state, expression :: expressions =>
      match evaluateOne state expression with
      | .done value nextState =>
          match evaluateList evaluateOne nextState expressions with
          | .done values finalState => .done (value :: values) finalState
          | .outOfFuel finalState => .outOfFuel finalState
          | .fault error finalState => .fault error finalState
      | .outOfFuel finalState => .outOfFuel finalState
      | .fault error finalState => .fault error finalState

private def applyUnary (plan : Plan) (operator : Syntax.UnaryOp)
    (value : Value) : Except RuntimeError Value :=
  match operator, value with
  | .logicalNot, .bool operand => pure (.bool (!operand))
  | .bitNot, .word operand => pure (.word operand.bitNot)
  | _, actual => throw (.invalidUnaryOperand operator (actual.type? plan))

private def applyBinary (plan : Plan) (operator : Syntax.BinaryOp)
    (left right : Value) : Except RuntimeError Value :=
  match operator, left, right with
  | .multiply, .word left, .word right => pure (.word (left.mul right))
  | .divide, .word left, .word right => pure (.word (left.udiv right))
  | .modulo, .word left, .word right => pure (.word (left.umod right))
  | .add, .word left, .word right => pure (.word (left.add right))
  | .subtract, .word left, .word right => pure (.word (left.sub right))
  | .bitAnd, .word left, .word right => pure (.word (left.bitAnd right))
  | .bitXor, .word left, .word right => pure (.word (left.bitXor right))
  | .bitOr, .word left, .word right => pure (.word (left.bitOr right))
  | .less, .word left, .word right => pure (.bool (decide (left < right)))
  | .greater, .word left, .word right => pure (.bool (decide (left > right)))
  | .lessEqual, .word left, .word right => pure (.bool (decide (left ≤ right)))
  | .greaterEqual, .word left, .word right => pure (.bool (decide (left ≥ right)))
  | .multiply, .integer left, .integer right => pure (.integer (left * right))
  | .divide, .integer left, .integer right =>
      if right = 0 then pure (.integer 0) else pure (.integer (left / right))
  | .modulo, .integer left, .integer right =>
      if right = 0 then pure (.integer 0) else pure (.integer (left % right))
  | .add, .integer left, .integer right => pure (.integer (left + right))
  | .subtract, .integer left, .integer right => pure (.integer (left - right))
  | .less, .integer left, .integer right => pure (.bool (decide (left < right)))
  | .greater, .integer left, .integer right => pure (.bool (decide (left > right)))
  | .lessEqual, .integer left, .integer right => pure (.bool (decide (left ≤ right)))
  | .greaterEqual, .integer left, .integer right => pure (.bool (decide (left ≥ right)))
  | .equal, left, right => pure (.bool (valueEqual left right))
  | .notEqual, left, right => pure (.bool (!(valueEqual left right)))
  | .logicalAnd, .bool left, .bool right => pure (.bool (left && right))
  | .logicalOr, .bool left, .bool right => pure (.bool (left || right))
  | _, left, right =>
      throw (.invalidBinaryOperands operator (left.type? plan) (right.type? plan))

private def assignmentBinary? : Syntax.ValueAssignOp → Option Syntax.BinaryOp
  | .equal => none
  | .add => some .add
  | .subtract => some .subtract
  | .multiply => some .multiply
  | .divide => some .divide
  | .modulo => some .modulo
  | .bitAnd => some .bitAnd
  | .bitXor => some .bitXor
  | .bitOr => some .bitOr

private def applyBuiltin (function : BuiltinFunctionId)
    (arguments : List Value) : Except RuntimeError Value :=
  match function, arguments with
  | .integerSub, [.integer left, .integer right] =>
      pure (.integer (left - right))
  | .wordFromInteger, [.integer value] =>
      pure (.word (Core.Word.ofIntModulo value))
  | .integerAdd, [.integer left, .integer right] =>
      pure (.integer (left + right))
  | .integerEq, [.integer left, .integer right] =>
      pure (.bool (decide (left = right)))
  | .integerLt, [.integer left, .integer right] =>
      pure (.bool (decide (left < right)))
  | .integerMul, [.integer left, .integer right] =>
      pure (.integer (left * right))
  | .wordToInteger, [.word value] =>
      pure (.integer (Int.ofNat value.val))
  | function, arguments =>
      if arguments.length != function.parameterTypes.length then
        throw (.argumentArityMismatch function.parameterTypes.length
          arguments.length)
      else
        throw (.invalidBuiltin function)

def replaceValueAt : Nat → Value → List Value → Option (List Value)
  | _, _, [] => none
  | 0, replacement, _ :: rest => some (replacement :: rest)
  | index + 1, replacement, value :: rest => do
      pure (value :: (← replaceValueAt index replacement rest))

/-- A successful payload replacement contributes only the replacement value
or a value already present in the original payload vector. -/
theorem replaceValueAt_member
    (index : Nat) (replacement : Value)
    (arguments replaced : List Value)
    (selected : Value)
    (written : replaceValueAt index replacement arguments = some replaced)
    (member : selected ∈ replaced) :
    selected = replacement ∨ selected ∈ arguments := by
  induction arguments generalizing index replaced with
  | nil => simp [replaceValueAt] at written
  | cons first rest inductionHypothesis =>
      cases index with
      | zero =>
          simp [replaceValueAt] at written
          cases written
          simp only [List.mem_cons] at member ⊢
          rcases member with fresh | old
          · exact Or.inl fresh
          · exact Or.inr (Or.inr old)
      | succ index =>
          cases tailWrite : replaceValueAt index replacement rest with
          | none => simp [replaceValueAt, tailWrite] at written
          | some replacedTail =>
              simp [replaceValueAt, tailWrite] at written
              cases written
              simp only [List.mem_cons] at member ⊢
              rcases member with old | tail
              · exact Or.inr (Or.inl old)
              · rcases inductionHypothesis index replacedTail tailWrite tail with
                  fresh | old
                · exact Or.inl fresh
                · exact Or.inr (Or.inr old)

private inductive PatternResult where
  | matched (bindings : List (TypedBinder × Value))
  | noMatch
  | malformed

private structure InstructionResult where
  bindings : List (TypedBinder × Value)
  rest : List MatchPatternInstruction

private def literalPatternMatches (resolution : IntegerLiteralResolution)
    (value : Value) : Bool :=
  match resolution.targetType, value with
  | .constructor (.builtin .word), .word actual =>
      actual == Core.Word.ofNatModulo resolution.rawValue
  | .constructor (.builtin .integer), .integer actual =>
      actual == Int.ofNat resolution.rawValue
  | _, _ => false

mutual

  private def matchInstructionFuel : Nat → Value →
      List MatchPatternInstruction → Option InstructionResult
    | 0, _, _ => none
    | _ + 1, _, [] => none
    | _ + 1, _, .wildcard :: rest => some { bindings := [], rest }
    | _ + 1, value, .integerLiteral _ resolution :: rest =>
        if literalPatternMatches resolution value then
          some { bindings := [], rest }
        else
          none
    | _ + 1, value, .binder binder :: rest =>
        some { bindings := [(binder, value)], rest }
    | fuel + 1, value, .constructor instantiation argumentCount :: rest =>
        match value with
        | .constructed actual arguments =>
            if decide (actual = instantiation) &&
                arguments.length = argumentCount then
              matchInstructionsFuel fuel arguments rest
            else
              none
        | _ => none
    | fuel + 1, value, .tuple elementCount :: rest => do
        let elements ← unpackValues elementCount value
        matchInstructionsFuel fuel elements rest

  private def matchInstructionsFuel : Nat → List Value →
      List MatchPatternInstruction → Option InstructionResult
    | 0, [], instructions => some { bindings := [], rest := instructions }
    | 0, _ :: _, _ => none
    | _ + 1, [], instructions => some { bindings := [], rest := instructions }
    | fuel + 1, value :: values, instructions => do
        let first ← matchInstructionFuel fuel value instructions
        let tail ← matchInstructionsFuel fuel values first.rest
        pure {
          bindings := first.bindings ++ tail.bindings
          rest := tail.rest
        }

end

private def matchPattern (pattern : TypedMatchPattern)
    (value : Value) : PatternResult :=
  match pattern.resolution with
  | .wildcard => .matched []
  | .integerLiteral _ resolution =>
      if literalPatternMatches resolution value then .matched [] else .noMatch
  | .binder binder => .matched [(binder, value)]
  | .constructor instantiation instructions =>
      match value with
      | .constructed actual arguments =>
          if decide (actual = instantiation) &&
              arguments.length = instantiation.payloadTypes.length then
            match matchInstructionsFuel (instructions.length + 1)
                arguments instructions with
            | some result =>
                if result.rest.isEmpty then .matched result.bindings
                else .malformed
            | none => .noMatch
          else
            .noMatch
      | _ => .noMatch
  | .tuple instructions =>
      let elementCount := match pattern.source with
        | .tuple _ count => count
        | _ => 0
      match unpackValues elementCount value with
      | none => .noMatch
      | some elements =>
          match matchInstructionsFuel (instructions.length + 1)
              elements instructions with
          | some result =>
              if result.rest.isEmpty then .matched result.bindings
              else .malformed
          | none => .noMatch

def bindValues (plan : Plan) : Environment → RuntimeState →
    List (TypedBinder × Value) →
      Except RuntimeError (Environment × RuntimeState)
  | environment, state, [] => pure (environment, state)
  | environment, state, (binder, value) :: rest => do
      if value.type? plan != some binder.scheme.body then
        throw (.typeMismatch binder.scheme.body (value.type? plan))
      let (location, state) := state.allocate binder.scheme.body (some value)
      bindValues plan ((binder.id, location) :: environment) state rest

/-- The successful parameter/pattern-binding path of the evaluator preserves
shallow heap typing across every allocated binding cell. -/
theorem bindValues_ok_preserves_shallow_types
    (plan : Plan) (bindings : List (TypedBinder × Value))
    (environment finalEnvironment : Environment)
    (state finalState : RuntimeState)
    (typing : state.HasShallowTypes plan)
    (bound : bindValues plan environment state bindings =
      .ok (finalEnvironment, finalState)) :
    finalState.HasShallowTypes plan := by
  induction bindings generalizing environment state with
  | nil =>
      simp [bindValues] at bound
      obtain ⟨rfl, rfl⟩ := bound
      exact typing
  | cons binding rest inductionHypothesis =>
      obtain ⟨binder, value⟩ := binding
      by_cases typed : value.type? plan = some binder.scheme.body
      · simp [bindValues, typed, bne] at bound
        exact inductionHypothesis _ _
          (typing.allocateValue binder.scheme.body value typed) bound
      · simp [bindValues, typed, bne] at bound
        change Except.error _ = Except.ok (finalEnvironment, finalState) at bound
        cases bound

private def statementIds : List NodeId → Except RuntimeError (List StatementId)
  | [] => pure []
  | .statement id :: roots => do
      pure (id :: (← statementIds roots))
  | .expression id :: _ => throw (.expectedStatementRoot id)

private def executeSequence
    (executeOne : Environment → RuntimeState → StatementId → FlowOutcome) :
    Environment → RuntimeState → List StatementId → FlowOutcome
  | environment, state, [] => .fallthrough environment state
  | environment, state, statement :: statements =>
      match executeOne environment state statement with
      | .fallthrough nextEnvironment nextState =>
          executeSequence executeOne nextEnvironment nextState statements
      | .returned value finalState => .returned value finalState
      | .breaking finalEnvironment finalState =>
          .breaking finalEnvironment finalState
      | .continuing finalEnvironment finalState =>
          .continuing finalEnvironment finalState
      | .outOfFuel finalState => .outOfFuel finalState
      | .fault error finalState => .fault error finalState

private def restoreScope (outer : Environment) : FlowOutcome → FlowOutcome
  | .fallthrough _ state => .fallthrough outer state
  | .returned value state => .returned value state
  | .breaking _ state => .breaking outer state
  | .continuing _ state => .continuing outer state
  | .outOfFuel state => .outOfFuel state
  | .fault error state => .fault error state

inductive ModificationResult where
  | done (value : Value) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)

inductive RuntimeProjection where
  | index (key : Value)
  | member (name : String) (index : Nat)

structure ResolvedPlace where
  location : Location
  rootType : Ty
  valueType : Ty
  projections : List RuntimeProjection
  /-- Value selected after evaluating the target path and before evaluating the
  assignment RHS.  Compound assignment uses this snapshot, while the final
  structural write starts from the latest root so unrelated RHS effects survive. -/
  selected : Option Value

private inductive PlaceResult where
  | done (place : ResolvedPlace) (state : RuntimeState)
  | outOfFuel (state : RuntimeState)
  | fault (error : RuntimeError) (state : RuntimeState)

/-- Evaluate every place index once, left-to-right.  This phase is deliberately
separate from reading or updating the place, so assignment RHS effects happen
after target selection and cannot cause an index expression to be repeated. -/
private def resolveProjections
    (evaluateOne : RuntimeState → ExpressionId → ExpressionResult) :
    RuntimeState → List PlaceProjection →
      Except (Option RuntimeError × RuntimeState)
        (List RuntimeProjection × RuntimeState)
  | state, [] => pure ([], state)
  | state, .member name index :: rest => do
      let (resolved, finalState) ← resolveProjections evaluateOne state rest
      pure (.member name index :: resolved, finalState)
  | state, .index expression :: rest =>
      match evaluateOne state expression with
      | .done key nextState =>
          match resolveProjections evaluateOne nextState rest with
          | .ok (resolved, finalState) =>
              .ok (.index key :: resolved, finalState)
          | .error error => .error error
      | .outOfFuel finalState => .error (none, finalState)
      | .fault error finalState => .error (some error, finalState)

private def readResolvedValue (plan : Plan) :
    Option Value → List RuntimeProjection → Except RuntimeError (Option Value)
  | current, [] => pure current
  | none, _ :: _ => throw .invalidPlaceProjection
  | some current, .index key :: rest =>
      match current with
      | .mapping keyType valueType entries => do
          if key.type? plan != some keyType then
            throw (.typeMismatch keyType (key.type? plan))
          let selected ← match mappingLookup? key entries with
            | some value => pure value
            | none => match defaultValue? (valueType.size + 1) valueType with
              | some value => pure value
              | none => throw (.typeMismatch valueType none)
          readResolvedValue plan (some selected) rest
      | actual => throw (.expectedMapping (actual.type? plan))
  | some current, .member name index :: rest =>
      match current with
      | .constructed _ arguments =>
          match arguments[index]? with
          | some selected => readResolvedValue plan (some selected) rest
          | none => throw (.invalidMember name index (current.type? plan))
      | actual => throw (.invalidMember name index (actual.type? plan))

private def resolvePlace (plan : Plan)
    (evaluateOne : RuntimeState → ExpressionId → ExpressionResult)
    (environment : Environment) (state : RuntimeState)
    (place : PlaceResolution) : PlaceResult :=
  match lookupLocation? environment place.root with
  | none => .fault (.unboundLocal place.root) state
  | some location =>
      match state.read? location with
      | none => .fault (.danglingLocation location) state
      | some _ =>
          match resolveProjections evaluateOne state place.projections with
          | .ok (projections, finalState) =>
              match finalState.read? location with
              | none => .fault (.danglingLocation location) finalState
              | some cell =>
                  let initial := match cell.value, cell.type with
                    | none, .mapping key value => some (.mapping key value [])
                    | value, _ => value
                  match readResolvedValue plan initial projections with
                  | .error error => .fault error finalState
                  | .ok selected => .done {
                      location
                      rootType := cell.type
                      valueType := place.type
                      projections
                      selected
                    } finalState
          | .error (none, finalState) => .outOfFuel finalState
          | .error (some error, finalState) => .fault error finalState

def updateResolvedValue (plan : Plan) (expected : Ty)
    (modify : Option Value → Except RuntimeError Value) :
    Option Value → List RuntimeProjection → Except RuntimeError Value
  | current, [] => do
      let updated ← modify current
      if updated.type? plan = some expected then pure updated
      else throw (.typeMismatch expected (updated.type? plan))
  | none, _ :: _ => throw .invalidPlaceProjection
  | some current, .index key :: rest =>
      match current with
      | .mapping keyType valueType entries => do
          if key.type? plan != some keyType then
            throw (.typeMismatch keyType (key.type? plan))
          let selected ← match mappingLookup? key entries with
            | some value => pure value
            | none => match defaultValue? (valueType.size + 1) valueType with
              | some value => pure value
              | none => throw (.typeMismatch valueType none)
          let updated ← updateResolvedValue plan expected modify
            (some selected) rest
          pure (.mapping keyType valueType (mappingInsert key updated entries))
      | actual => throw (.expectedMapping (actual.type? plan))
  | some current, .member name index :: rest =>
      match current with
      | .constructed instantiation arguments => do
          let selected ← match arguments[index]? with
            | some value => pure value
            | none => throw (.invalidMember name index (current.type? plan))
          let updated ← updateResolvedValue plan expected modify
            (some selected) rest
          let arguments ← match replaceValueAt index updated arguments with
            | some values => pure values
            | none => throw (.invalidMember name index (current.type? plan))
          pure (.constructed instantiation arguments)
      | actual => throw (.invalidMember name index (actual.type? plan))

/-- Interpret an uninitialized mapping cell as its empty mapping before a
structural place update. -/
def initialRootValue (cell : Cell) : Option Value :=
  match cell.value, cell.type with
  | none, .mapping key value => some (.mapping key value [])
  | value, _ => value

def writeResolvedPlace (plan : Plan) (state : RuntimeState)
    (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value) : ModificationResult :=
  match state.read? place.location with
  | none => .fault (.danglingLocation place.location) state
  | some cell =>
      if cell.type != place.rootType then
        .fault (.typeMismatch place.rootType (some cell.type)) state
      else
        let initial := initialRootValue cell
        match updateResolvedValue plan place.valueType modify initial
            place.projections with
        | .error error => .fault error state
        | .ok updated =>
            if updated.type? plan != some place.rootType then
              .fault (.typeMismatch place.rootType (updated.type? plan)) state
            else
              match state.write? place.location (some updated) with
              | some finalState => .done updated finalState
              | none => .fault (.danglingLocation place.location) state

/-- Even a forged place cannot overwrite a cell whose annotation differs from
the root type captured during place resolution. -/
private theorem writeResolvedPlace_rejects_mismatched_root
    (plan : Plan) (state : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value) (cell : Cell)
    (found : state.read? place.location = some cell)
    (mismatch : cell.type ≠ place.rootType) :
    writeResolvedPlace plan state place modify =
      .fault (.typeMismatch place.rootType (some cell.type)) state := by
  simp [writeResolvedPlace, found, mismatch]

/-- A successful structural write maintains the shallow annotation invariant;
the check against the current cell type is essential for this implication. -/
private theorem writeResolvedPlace_done_preserves_shallow_types
    (plan : Plan) (state finalState : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value) (updated : Value)
    (typing : state.HasShallowTypes plan)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    finalState.HasShallowTypes plan := by
  unfold writeResolvedPlace at done
  cases found : state.read? place.location with
  | none => simp [found] at done
  | some cell =>
      simp only [found] at done
      by_cases sameType : cell.type = place.rootType
      · have noMismatch : (cell.type != place.rootType) = false := by
          simp [sameType]
        rw [noMismatch] at done
        simp only [Bool.false_eq_true, ↓reduceIte] at done
        cases updateResult : updateResolvedValue plan place.valueType modify
            (initialRootValue cell) place.projections with
        | error error => simp [updateResult] at done
        | ok next =>
            simp only [updateResult] at done
            by_cases nextType : next.type? plan = some place.rootType
            · simp [nextType] at done
              cases written : state.write? place.location (some next) with
              | none => simp [written] at done
              | some nextState =>
                  simp [written] at done
                  rcases done with ⟨rfl, rfl⟩
                  apply typing.write? found _ written
                  intro value equal
                  cases equal
                  simpa [sameType] using nextType
            · simp [nextType] at done
      · simp [sameType] at done

private def finishFunctionFlow (plan : Plan) (expected : Ty) :
    FlowOutcome → RunResult
  | .returned value state =>
      if value.type? plan = some expected then .done value state
      else .fault (.resultTypeMismatch expected (value.type? plan)) state
  | .fallthrough _ state =>
      if expected = Ty.unit then .done .unit state
      else .fault (.functionFellThrough expected) state
  | .breaking _ state
  | .continuing _ state => .fault .controlEscapedFunction state
  | .outOfFuel state => .outOfFuel state
  | .fault error state => .fault error state

private theorem finishFunctionFlow_done_type
    (plan : Plan) (expected : Ty) (flow : FlowOutcome)
    (value : Value) (finalState : RuntimeState)
    (done : finishFunctionFlow plan expected flow =
      .done value finalState) :
    value.type? plan = some expected := by
  cases flow with
  | returned returnedValue returnedState =>
      simp only [finishFunctionFlow] at done
      split at done
      · next hasType =>
        cases done
        exact hasType
      · contradiction
  | fallthrough environment returnedState =>
      simp only [finishFunctionFlow] at done
      split at done
      · next isUnit =>
        cases done
        simp [Value.type?, isUnit]
      · contradiction
  | breaking environment returnedState =>
      simp only [finishFunctionFlow] at done
      cases done
  | continuing environment returnedState =>
      simp only [finishFunctionFlow] at done
      cases done
  | outOfFuel returnedState =>
      simp only [finishFunctionFlow] at done
      cases done
  | fault error returnedState =>
      simp only [finishFunctionFlow] at done
      cases done

private def expressionOfRunResult : RunResult → ExpressionResult
  | .done value state => .done value state
  | .outOfFuel state => .outOfFuel state
  | .fault error state => .fault error state

private def modifyLeafForAssignment (plan : Plan) (expected : Ty)
    (operator : Syntax.ValueAssignOp) (right : Value) :
    Option Value → Except RuntimeError Value
  | current =>
      if right.type? plan != some expected then
        throw (.typeMismatch expected (right.type? plan))
      else
        match operator, current with
        | .equal, _ => pure right
        | operator, some left =>
            match assignmentBinary? operator with
            | some binary =>
                match applyBinary plan binary left right with
                | .ok value => pure value
                | .error _ => throw (.invalidAssignmentOperands operator
                    (left.type? plan) (right.type? plan))
            | none => pure right
        | operator, none =>
            throw (.invalidAssignmentOperands operator none (right.type? plan))

private def modifyLeafBitNot (plan : Plan) :
    Option Value → Except RuntimeError Value
  | some (.word value) => pure (.word value.bitNot)
  | some actual => throw (.invalidUnaryOperand .bitNot (actual.type? plan))
  | none => throw (.invalidUnaryOperand .bitNot none)

/-- Produce a concrete occurrence view without rewriting the principal value
stored in the heap.  The occurrence must be closed and every quantified
variable must have been determined by matching the scheme body. -/
private def instantiateDirectLambdaLet? (plan : Plan) (owner : Key)
    (source : TypedSource) (id : Resolved.LocalId) (node : ExpressionNode)
    (value : Value) : Except RuntimeError (Option Value) := do
  let some binder := directLambdaLetBinder? source id
    | pure none
  if value.type? plan != some binder.scheme.body then
    throw (.localSchemeInstanceMismatch owner node.id binder.id
      binder.scheme.body (Option.getD (value.type? plan) Ty.error))
  let caller ← exactSpecialization plan owner
  let owned ← match ordinaryOwnedRequirements? node with
    | some requirements => pure requirements
    | none => throw (.unsupportedRequirements node.requirements)
  let node := { node with requirements := owned, coercions := [] }
  let (substitution, requirements) ←
    localRequirementWitnesses caller binder node
  match value with
  | .closure _ _ _ _ _ _ _ =>
      pure (some (.instantiated substitution requirements value))
  | _ => pure none

private def rewriteLocalRequirement
    (requirements : List LocalRequirementWitness)
    (requirement : RequirementId) : RequirementId :=
  match requirements.find? fun witness =>
      witness.templateRequirement == requirement with
  | some witness => witness.actualRequirement
  | none => requirement

private def rewriteExpressionLocalRequirements
    (requirements : List LocalRequirementWitness)
    (node : ExpressionNode) : ExpressionNode := {
  node with
  requirements := node.requirements.map
    (rewriteLocalRequirement requirements)
}

private def rewriteNodeLocalRequirements
    (requirements : List LocalRequirementWitness) : Node → Node
  | .expression node =>
      .expression (rewriteExpressionLocalRequirements requirements node)
  | node => node

/-- Rewrite only the expression-level requirement ledger.  The qualified
local runtime profile validates that owned template requirements occur solely
on supported direct declaration calls before constructing this view. -/
private def rewriteLocalRequirements
    (requirements : List LocalRequirementWitness)
    (source : TypedSource) : TypedSource := {
  source with
  nodes := source.nodes.map (rewriteNodeLocalRequirements requirements)
}

mutual

  /-- Execute an evidence-selected coercion method in the same heap as the
  enclosing expression.  The selected checked method is installed in a
  temporary runtime plan so its ordinary source body, including allocations
  and mutations, is interpreted by this evaluator rather than reinterpreted
  as a builtin cast. -/
  private def executeCoercionPath (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key) (evidence : RuntimeEvidenceEnvironment)
      (node : ExpressionNode) (target : Ty) (steps : List CoercionStep)
      (value : Value) (state : RuntimeState) : ExpressionResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match steps with
      | [] =>
          if value.type? plan = some target then .done value state
          else .fault (.typeMismatch target (value.type? plan)) state
      | step :: rest =>
          if value.type? plan != some step.source then
            .fault (.typeMismatch step.source (value.type? plan)) state
          else
            match exactSpecialization plan owner with
            | .error error => .fault error state
            | .ok caller =>
                match checkedCoercionMethod program caller node evidence step with
                | .error error => .fault error state
                | .ok method =>
                    match coercionMethodRuntimeEvidence program caller node step
                        method with
                    | .error error => .fault error state
                    | .ok methodEvidence =>
                        let methodKey := method.specialized.key
                        let methodPlan : Plan := {
                          plan with
                          specializations := method.specialized ::
                            (plan.specializations.filter fun specialized =>
                              specialized.key != methodKey)
                          callEdges := {
                            caller := owner
                            occurrence := node.id
                            callee := methodKey
                          } :: plan.callEdges
                        }
                        match invokeDirectSpecialization fuel program methodPlan
                            methodKey methodEvidence [value] state with
                        | .done coerced nextState =>
                            if coerced.type? methodPlan != some step.target then
                              .fault (.typeMismatch step.target
                                (coerced.type? methodPlan)) nextState
                            else
                              executeCoercionPath fuel program plan owner evidence
                                node target rest coerced nextState
                        | .outOfFuel finalState => .outOfFuel finalState
                        | .fault error finalState => .fault error finalState

  private def evaluate (fuel : Nat) (program : CheckedProgram) (plan : Plan)
      (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (id : ExpressionId) : ExpressionResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactExpression source id with
      | .error error => .fault error state
      | .ok node =>
        let descend := evaluate fuel program plan owner evidence source environment
        let raw : ExpressionResult :=
          match node.form with
          | .literal literal =>
              match numericLiteralValue? literal with
              | some value => .done (.word (Core.Word.ofNatModulo value)) state
              | none => .fault (.malformedLiteral id) state
          | .integerLiteral literal resolution =>
              match numericLiteralValue? literal with
              | some value =>
                  if value != resolution.rawValue then
                    .fault (.literalMetadataMismatch id) state
                  else
                    match resolution.targetType with
                    | .constructor (.builtin .word) =>
                        .done (.word (Core.Word.ofNatModulo value)) state
                    | .constructor (.builtin .integer) =>
                        .done (.integer (Int.ofNat value)) state
                    | other => .fault (.typeMismatch other none) state
              | none => .fault (.malformedLiteral id) state
          | .reference _ (.local binder) =>
              match lookupLocation? environment binder with
              | none => .fault (.unboundLocal binder) state
              | some location =>
                  match state.read? location with
                  | none => .fault (.danglingLocation location) state
                  | some { type := .mapping key value, value := none } =>
                      match state.write? location
                          (some (.mapping key value [])) with
                      | some finalState =>
                          .done (.mapping key value []) finalState
                      | none => .fault (.danglingLocation location) state
                  | some { value := none, .. } =>
                      .fault (.uninitializedLocal binder) state
                  | some { value := some value, .. } =>
                      match instantiateDirectLambdaLet? plan owner source binder
                          node value with
                      | .ok (some instantiated) => .done instantiated state
                      | .ok none => .done value state
                      | .error error => .fault error state
          | .reference _ (.builtinBoolean value) =>
              .done (.bool value) state
          | .reference _ (.builtinFunction function) =>
              .done (.builtin function) state
          | .reference _ (.declaration instantiation) =>
              match exactInstantiationKey plan instantiation with
              | .error error => .fault error state
              | .ok target =>
                  match exactReferenceKey plan owner id target with
                  | .ok key => .done (.global key) state
                  | .error error => .fault error state
          | .group inner => descend state inner
          | .tuple elements =>
              match evaluateList descend state elements with
              | .done values finalState =>
                  .done (packValues values) finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .unary operator operand =>
              match descend state operand with
              | .done value finalState =>
                  match applyUnary plan operator value with
                  | .ok result => .done result finalState
                  | .error error => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .binary left operator right =>
              match descend state left with
              | .done leftValue rightState =>
                  match operator, leftValue with
                  | .logicalAnd, .bool false => .done (.bool false) rightState
                  | .logicalOr, .bool true => .done (.bool true) rightState
                  | _, _ =>
                      match descend rightState right with
                      | .done rightValue finalState =>
                          match applyBinary plan operator leftValue rightValue with
                          | .ok result => .done result finalState
                          | .error error => .fault error finalState
                      | .outOfFuel finalState => .outOfFuel finalState
                      | .fault error finalState => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .conditional condition thenBranch elseBranch =>
              match descend state condition with
              | .done (.bool true) branchState => descend branchState thenBranch
              | .done (.bool false) branchState => descend branchState elseBranch
              | .done actual finalState =>
                  .fault (.expectedBool (actual.type? plan)) finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .lambda parameters resultType body =>
              .done (.closure parameters resultType body source owner environment
                evidence) state
          | .call callee arguments (.declaration instantiation) =>
              match evaluateList descend state arguments with
              | .done values finalState =>
                  match validateDirectDeclarationCallee source id callee
                      instantiation with
                  | .error error => .fault error finalState
                  | .ok () =>
                      match exactInstantiationKey plan instantiation with
                      | .error error => .fault error finalState
                      | .ok target =>
                          match exactCallKey plan owner id target with
                          | .ok key =>
                              match exactSpecialization plan owner with
                              | .error error => .fault error finalState
                              | .ok caller =>
                                  match exactDirectCallRuntimeEvidence caller node
                                      evidence instantiation with
                                  | .error error => .fault error finalState
                                  | .ok calleeEvidence =>
                                      expressionOfRunResult
                                        (invokeDirectSpecialization fuel program
                                          plan key calleeEvidence values finalState)
                          | .error error => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .call _ arguments (.builtinFunction function) =>
              match evaluateList descend state arguments with
              | .done values finalState =>
                  applyCallable fuel program plan (.builtin function) values
                    finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .call callee arguments (.indirect metadata) =>
              match descend state callee with
              | .done functionValue argumentState =>
                  match evaluateList descend argumentState arguments with
                  | .done values finalState =>
                      let packed := packValues values
                      if packed.type? plan !=
                          some metadata.argumentTypeBeforeCoercion then
                        .fault (.typeMismatch metadata.argumentTypeBeforeCoercion
                          (packed.type? plan)) finalState
                      else
                        let coerced := if metadata.argumentCoercions.isEmpty then
                          .done packed finalState
                        else
                          executeCoercionPath fuel program plan owner evidence node
                            metadata.argumentTypeAfterCoercion
                            metadata.argumentCoercions packed finalState
                        match coerced with
                        | .done argumentBundle coercedState =>
                            match unpackValues metadata.argumentCount
                                argumentBundle with
                            | some appliedArguments =>
                                applyCallable fuel program plan functionValue
                                  appliedArguments coercedState
                            | none => .fault
                                (.argumentArityMismatch metadata.argumentCount 0)
                                coercedState
                        | .outOfFuel coercedState => .outOfFuel coercedState
                        | .fault error coercedState => .fault error coercedState
                  | .outOfFuel finalState => .outOfFuel finalState
                  | .fault error finalState => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .constructor instantiation arguments =>
              match evaluateList descend state arguments with
              | .done values finalState =>
                  let candidate := Value.constructed instantiation values
                  if candidate.type? plan = some instantiation.resultType then
                    .done candidate finalState
                  else
                    .fault (.typeMismatch instantiation.resultType
                      (candidate.type? plan)) finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .member base name index =>
              match descend state base with
              | .done value finalState =>
                  match value with
                  | .constructed _ arguments =>
                      match arguments[index]? with
                      | some member => .done member finalState
                      | none => .fault
                          (.invalidMember name index (value.type? plan)) finalState
                  | _ => .fault
                      (.invalidMember name index (value.type? plan)) finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .proxy inner => .done (.proxy inner) state
          | .index base index =>
              match descend state base with
              | .done baseValue indexState =>
                  match descend indexState index with
                  | .done key finalState =>
                      match baseValue with
                      | .mapping keyType valueType entries =>
                          if key.type? plan != some keyType then
                            .fault (.typeMismatch keyType (key.type? plan))
                              finalState
                          else
                            match mappingLookup? key entries with
                            | some value => .done value finalState
                            | none =>
                                match defaultValue? (valueType.size + 1) valueType with
                                | some value => .done value finalState
                                | none => .fault (.typeMismatch valueType none)
                                    finalState
                      | actual => .fault
                          (.expectedMapping (actual.type? plan)) finalState
                  | .outOfFuel finalState => .outOfFuel finalState
                  | .fault error finalState => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
        match raw with
        | .done value finalState =>
            if node.coercions.isEmpty then
              finishExpression plan node raw
            else
              executeCoercionPath fuel program plan owner evidence node
                node.type node.coercions value finalState
        | .outOfFuel finalState => .outOfFuel finalState
        | .fault error finalState => .fault error finalState

  private def applyCallable (fuel : Nat) (program : CheckedProgram) (plan : Plan)
      (function : Value)
      (arguments : List Value) (state : RuntimeState) : ExpressionResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match function with
      | .builtin builtin =>
          match applyBuiltin builtin arguments with
          | .ok value => .done value state
          | .error error => .fault error state
      | .global key =>
          expressionOfRunResult
            (invokeSpecialization fuel program plan key arguments state)
      | .closure parameters expected body source owner captured evidence =>
          if parameters.length != arguments.length then
            .fault (.argumentArityMismatch parameters.length arguments.length) state
          else
            match bindValues plan captured state (List.zip parameters arguments) with
            | .error error => .fault error state
            | .ok (environment, bodyState) =>
                let flow := executeFunctionSequence fuel program plan owner evidence
                  source environment bodyState body
                expressionOfRunResult (finishFunctionFlow plan expected flow)
      | .instantiated substitution requirements
          (.closure parameters expected body source owner captured evidence) =>
          let parameters := parameters.map
            (TypedBinder.applySubstitution substitution)
          let expected := substitution.apply expected
          let source := rewriteLocalRequirements requirements
            (source.applySubstitution substitution)
          if parameters.length != arguments.length then
            .fault (.argumentArityMismatch parameters.length arguments.length) state
          else
            match bindValues plan captured state (List.zip parameters arguments) with
            | .error error => .fault error state
            | .ok (environment, bodyState) =>
                let flow := executeFunctionSequence fuel program plan owner evidence
                  source environment bodyState body
                expressionOfRunResult (finishFunctionFlow plan expected flow)
      | actual => .fault (.expectedFunction (actual.type? plan)) state

  private def invokeSpecialization (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (key : Key)
      (arguments : List Value) (state : RuntimeState) : RunResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactSpecialization plan key with
      | .error error => .fault error state
      | .ok specialized =>
          let function := specialized.function
          match validateSpecializationMetadata specialized with
          | .error error => .fault error state
          | .ok () =>
              let expected := function.inferredBodyType
              let parameters := function.typedBody.inputs
              if parameters.length != arguments.length then
                .fault (.argumentArityMismatch parameters.length
                  arguments.length) state
              else
                match bindValues plan [] state
                    (List.zip parameters arguments) with
                | .error error => .fault error state
                | .ok (environment, bodyState) =>
                    match statementIds function.typedBody.roots with
                    | .error error => .fault error bodyState
                    | .ok roots =>
                        let flow := executeFunctionSequence fuel program plan key []
                          function.typedBody environment bodyState roots
                        finishFunctionFlow plan expected flow

  /-- Enter a specialization whose where-predicates were discharged by the
  immediately enclosing, validated direct declaration call.  This entry point
  is deliberately absent from `Value.global`, roots, and indirect calls. -/
  private def invokeDirectSpecialization (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (key : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (arguments : List Value) (state : RuntimeState) : RunResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactSpecialization plan key with
      | .error error => .fault error state
      | .ok specialized =>
          let function := specialized.function
          match validateSpecializationMetadataWith
              (allowsDirectAssumptionInvocation plan key) specialized with
          | .error error => .fault error state
          | .ok () =>
              match validateRuntimeEvidence key specialized.assumptions
                  evidence with
              | .error error => .fault error state
              | .ok () =>
                  let expected := function.inferredBodyType
                  let parameters := function.typedBody.inputs
                  if parameters.length != arguments.length then
                    .fault (.argumentArityMismatch parameters.length
                      arguments.length) state
                  else
                    match bindValues plan [] state
                        (List.zip parameters arguments) with
                    | .error error => .fault error state
                    | .ok (environment, bodyState) =>
                        match statementIds function.typedBody.roots with
                        | .error error => .fault error bodyState
                        | .ok roots =>
                            let flow := executeFunctionSequence fuel program plan key
                              evidence function.typedBody environment bodyState
                              roots
                            finishFunctionFlow plan expected flow

  private def executeStatement (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (id : StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactStatement source id with
      | .error error => .fault error state
      | .ok node =>
        let descend := evaluate fuel program plan owner evidence source environment
        match node.form with
        | .letDecl binder initializer =>
            match initializer with
            | none =>
                let (location, nextState) :=
                  state.allocate binder.scheme.body none
                .fallthrough ((binder.id, location) :: environment) nextState
            | some expression =>
                match descend state expression with
                | .done value finalState =>
                    if value.type? plan != some binder.scheme.body then
                      .fault (.typeMismatch binder.scheme.body (value.type? plan))
                        finalState
                    else
                      let (location, nextState) :=
                        finalState.allocate binder.scheme.body (some value)
                      .fallthrough ((binder.id, location) :: environment) nextState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState
        | .returnStmt value =>
            match value with
            | none => .returned .unit state
            | some expression =>
                match descend state expression with
                | .done value finalState => .returned value finalState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState
        | .expression expression _ =>
            match descend state expression with
            | .done _ finalState => .fallthrough environment finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .assignValue assignment operator value =>
            match resolvePlace plan descend environment state assignment.target with
            | .done place rightState =>
                match descend rightState value with
                | .done right finalState =>
                    let modify := modifyLeafForAssignment plan
                      assignment.target.type operator right
                    let modify := if operator == .equal then modify
                      else fun _ => modify place.selected
                    match writeResolvedPlace plan finalState place modify with
                    | .done _ nextState => .fallthrough environment nextState
                    | .outOfFuel nextState => .outOfFuel nextState
                    | .fault error nextState => .fault error nextState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .assignBitNot assignment =>
            match resolvePlace plan descend environment state assignment.target with
            | .done place targetState =>
                match writeResolvedPlace plan targetState place
                    (fun _ => modifyLeafBitNot plan place.selected) with
                | .done _ nextState => .fallthrough environment nextState
                | .outOfFuel nextState => .outOfFuel nextState
                | .fault error nextState => .fault error nextState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .ifThen condition thenBody elseBody =>
            match descend state condition with
            | .done (.bool true) branchState =>
                restoreScope environment <| executeSequence
                  (executeStatement fuel program plan owner evidence source)
                  environment branchState thenBody
            | .done (.bool false) branchState =>
                match elseBody with
                | none => .fallthrough environment branchState
                | some body => restoreScope environment <| executeSequence
                    (executeStatement fuel program plan owner evidence source)
                    environment branchState body
            | .done actual finalState =>
                .fault (.expectedBool (actual.type? plan)) finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .block body => restoreScope environment <| executeSequence
            (executeStatement fuel program plan owner evidence source)
              environment state
              body
        | .matchWith resolution =>
            match descend state resolution.scrutinee with
            | .done scrutinee matchState =>
                let scrutineeType := (scrutinee.type? plan).getD Ty.error
                let (hidden, hiddenState) := matchState.allocate
                  scrutineeType (some scrutinee)
                let matchEnvironment :=
                  (resolution.hiddenScrutinee, hidden) :: environment
                restoreScope environment <| executeMatchCases fuel program plan owner
                  evidence source matchEnvironment hiddenState scrutinee
                  resolution.cases resolution.defaultBody
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .forLoop initializer condition post body =>
            match executeForItems fuel program plan owner evidence source environment
                state initializer with
            | .fallthrough loopEnvironment loopState =>
                restoreScope environment <| executeForIterations fuel program plan owner
                  evidence source loopEnvironment loopState condition post body
            | .returned value finalState => .returned value finalState
            | .breaking _ finalState
            | .continuing _ finalState =>
                .fault .controlEscapedFunction finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .whileLoop condition body =>
            restoreScope environment <| executeWhile fuel program plan owner evidence
              source environment state condition body
        | .breakStmt => .breaking environment state
        | .continueStmt => .continuing environment state

  private def executeWhile (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (condition : ExpressionId)
      (body : List StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match evaluate fuel program plan owner evidence source environment state
          condition with
      | .done (.bool false) finalState =>
          .fallthrough environment finalState
      | .done (.bool true) bodyState =>
          let outcome := restoreScope environment <| executeSequence
            (executeStatement fuel program plan owner evidence source)
            environment bodyState body
          match outcome with
          | .fallthrough nextEnvironment nextState
          | .continuing nextEnvironment nextState =>
              executeWhile fuel program plan owner evidence source nextEnvironment
                nextState condition body
          | .breaking _ finalState => .fallthrough environment finalState
          | .returned value finalState => .returned value finalState
          | .outOfFuel finalState => .outOfFuel finalState
          | .fault error finalState => .fault error finalState
      | .done actual finalState =>
          .fault (.expectedBool (actual.type? plan)) finalState
      | .outOfFuel finalState => .outOfFuel finalState
      | .fault error finalState => .fault error finalState

  private def executeForIterations (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (condition : ExpressionId)
      (post : List ForItemForm) (body : List StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match evaluate fuel program plan owner evidence source environment state
          condition with
      | .done (.bool false) finalState =>
          .fallthrough environment finalState
      | .done (.bool true) bodyState =>
          let outcome := restoreScope environment <| executeSequence
            (executeStatement fuel program plan owner evidence source)
            environment bodyState body
          match outcome with
          | .breaking _ finalState => .fallthrough environment finalState
          | .returned value finalState => .returned value finalState
          | .outOfFuel finalState => .outOfFuel finalState
          | .fault error finalState => .fault error finalState
          | .fallthrough postEnvironment postState
          | .continuing postEnvironment postState =>
              match executeForItems fuel program plan owner evidence source
                  postEnvironment postState post with
              | .fallthrough _ nextState =>
                  executeForIterations fuel program plan owner evidence source
                    environment nextState condition post body
              | .returned value finalState => .returned value finalState
              | .breaking _ finalState
              | .continuing _ finalState =>
                  .fault .controlEscapedFunction finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
      | .done actual finalState =>
          .fault (.expectedBool (actual.type? plan)) finalState
      | .outOfFuel finalState => .outOfFuel finalState
      | .fault error finalState => .fault error finalState

  private def executeForItems (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (items : List ForItemForm) : FlowOutcome :=
    match items with
    | [] => .fallthrough environment state
    | item :: rest =>
      match fuel with
      | 0 => .outOfFuel state
      | fuel + 1 =>
        let descend := evaluate fuel program plan owner evidence source environment
        let next (nextEnvironment : Environment) (nextState : RuntimeState) :=
          executeForItems fuel program plan owner evidence source nextEnvironment
            nextState rest
        match item with
        | .letDecl binder initializer =>
            match initializer with
            | none =>
                let (location, nextState) :=
                  state.allocate binder.scheme.body none
                next ((binder.id, location) :: environment) nextState
            | some expression =>
                match descend state expression with
                | .done value finalState =>
                    if value.type? plan != some binder.scheme.body then
                      .fault (.typeMismatch binder.scheme.body
                        (value.type? plan)) finalState
                    else
                      let (location, nextState) :=
                        finalState.allocate binder.scheme.body (some value)
                      next ((binder.id, location) :: environment) nextState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState
        | .expression expression =>
            match descend state expression with
            | .done _ finalState => next environment finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .assignValue assignment operator value =>
            match resolvePlace plan descend environment state assignment.target with
            | .done place rightState =>
                match descend rightState value with
                | .done right finalState =>
                    let modify := modifyLeafForAssignment plan
                      assignment.target.type operator right
                    let modify := if operator == .equal then modify
                      else fun _ => modify place.selected
                    match writeResolvedPlace plan finalState place modify with
                    | .done _ nextState => next environment nextState
                    | .outOfFuel nextState => .outOfFuel nextState
                    | .fault error nextState => .fault error nextState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .assignBitNot assignment =>
            match resolvePlace plan descend environment state assignment.target with
            | .done place targetState =>
                match writeResolvedPlace plan targetState place
                    (fun _ => modifyLeafBitNot plan place.selected) with
                | .done _ nextState => next environment nextState
                | .outOfFuel nextState => .outOfFuel nextState
                | .fault error nextState => .fault error nextState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState

  private def executeMatchCases (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (scrutinee : Value)
      (cases : List TypedMatchCase)
      (defaultBody : Option (List StatementId)) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match cases with
      | [] =>
          match defaultBody with
          | none => .fallthrough environment state
          | some body => restoreScope environment <| executeSequence
              (executeStatement fuel program plan owner evidence source) environment
                state body
      | arm :: rest =>
          match matchPattern arm.pattern scrutinee with
          | .malformed => .fault .malformedPattern state
          | .noMatch => executeMatchCases fuel program plan owner evidence source
              environment state scrutinee rest defaultBody
          | .matched bindings =>
              match bindValues plan environment state bindings with
              | .error error => .fault error state
              | .ok (armEnvironment, armState) =>
                  restoreScope environment <| executeSequence
                    (executeStatement fuel program plan owner evidence source)
                    armEnvironment armState arm.body

  /-- Execute a function or closure body with the source language's implicit
  return convention.  Only a semicolon-free expression which is the final
  top-level statement yields the function result.  Earlier expression values,
  and expression values inside nested statement bodies, remain ordinary
  fallthrough effects. -/
  private def executeFunctionSequence (fuel : Nat) (program : CheckedProgram)
      (plan : Plan) (owner : Key)
      (evidence : RuntimeEvidenceEnvironment)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) : List StatementId → FlowOutcome
    | [] => .fallthrough environment state
    | statement :: rest =>
        match fuel with
        | 0 => .outOfFuel state
        | fuel + 1 =>
            match rest with
            | [] =>
                match exactStatement source statement with
                | .error error => .fault error state
                | .ok node =>
                    match node.form with
                    | .expression expression false =>
                        match evaluate fuel program plan owner evidence source environment
                            state expression with
                        | .done value finalState => .returned value finalState
                        | .outOfFuel finalState => .outOfFuel finalState
                        | .fault error finalState => .fault error finalState
                    | _ => executeStatement fuel program plan owner evidence source
                        environment state statement
            | _ =>
                match executeStatement fuel program plan owner evidence source
                    environment state statement with
                | .fallthrough nextEnvironment nextState =>
                    executeFunctionSequence fuel program plan owner evidence source
                      nextEnvironment nextState rest
                | .returned value finalState => .returned value finalState
                | .breaking finalEnvironment finalState =>
                    .breaking finalEnvironment finalState
                | .continuing finalEnvironment finalState =>
                    .continuing finalEnvironment finalState
                | .outOfFuel finalState => .outOfFuel finalState
                | .fault error finalState => .fault error finalState

end

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
  exhaustion. -/
  def Value.validateTypeFuel :
      Nat → ProgramSignatures → Plan → Ty → Value → TypeValidation
    | 0, _, _, _, _ => .outOfFuel
    | fuel + 1, signatures, plan, expected, actual =>
        match expected, actual with
        | .constructor (.builtin .unit), .unit => .valid
        | .constructor (.builtin .bool), .bool _ => .valid
        | .constructor (.builtin .word), .word _ => .valid
        | .constructor (.builtin .integer), .integer _ => .valid
        | .product leftType rightType, .product left right =>
            combineValidation
              (Value.validateTypeFuel fuel signatures plan leftType left)
              (Value.validateTypeFuel fuel signatures plan rightType right)
        | .proxy inner, .proxy actualInner =>
            if inner = actualInner then .valid else .invalid
        | .mapping keyType valueType, .mapping actualKey actualValue entries =>
            if decide (keyType = actualKey) &&
                decide (valueType = actualValue) then
              mappingEntriesValidateFuel fuel signatures plan keyType valueType
                entries
            else
              .invalid
        | _, .constructed instantiation arguments =>
            if decide (expected = instantiation.resultType) &&
                validConstructorInstantiation signatures instantiation then
              if instantiation.payloadTypes.any typeContainsStaged then
                .unsupportedStaged
              else
                valuesValidateFuel fuel signatures plan
                  instantiation.payloadTypes arguments
            else
              .invalid
        | .function _ _, .global key =>
            match exactSpecialization plan key with
            | .ok specialized =>
                if specialized.function.type = expected then .valid else .invalid
            | .error _ => .invalid
        | .function _ _, .builtin function =>
            if function.type = expected then .valid else .invalid
        | .comptime inner, value =>
            Value.validateTypeFuel fuel signatures plan inner value
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

/-- Step-indexed *structural heap* typing of a runtime value.  At depth zero
no structure is inspected; each successor step validates the outer type and
one layer of products, mappings, nominal payloads, and captured closure
locations.  The index permits cyclic closure heaps.

This is deliberately not semantic closure typing: it does not certify a
closure's `body`, `source`, `owner`, or captured evidence against the typed
plan.  A whole-language type-preservation theorem needs those separate static
closure/frame certificates and an evaluator induction in addition to this heap
invariant. -/
def Value.HasDeepTypeFuel :
    Nat → ProgramSignatures → Plan → RuntimeState → Ty → Value → Prop
  | 0, _, _, _, _, _ => True
  | fuel + 1, signatures, plan, state, expected, value =>
      value.type? plan = some expected ∧
        match value with
        | .product left right =>
            match expected with
            | .product leftType rightType =>
                left.HasDeepTypeFuel fuel signatures plan state leftType ∧
                  right.HasDeepTypeFuel fuel signatures plan state rightType
            | _ => False
        | .mapping actualKey actualValue entries =>
            match expected with
            | .mapping keyType valueType =>
                actualKey = keyType ∧ actualValue = valueType ∧
                  ∀ entry, entry ∈ entries →
                    entry.1.HasDeepTypeFuel fuel signatures plan state keyType ∧
                      entry.2.HasDeepTypeFuel fuel signatures plan state valueType
            | _ => False
        | .constructed instantiation arguments =>
            instantiation.resultType = expected ∧
              validConstructorInstantiation signatures instantiation = true ∧
              instantiation.payloadTypes.length = arguments.length ∧
              ∀ pair, pair ∈ List.zip instantiation.payloadTypes arguments →
                pair.2.HasDeepTypeFuel fuel signatures plan state pair.1
        | .closure parameters resultType _ _ _ captured _ =>
            expected = .function
              (Ty.productMany (parameters.map (·.scheme.body))) resultType ∧
              ∀ binding, binding ∈ captured →
                ∃ cell, state.read? binding.2 = some cell ∧
                  ∀ capturedValue, cell.value = some capturedValue →
                    capturedValue.HasDeepTypeFuel fuel signatures plan state cell.type
        | .instantiated _ _ principal =>
            match principal.type? plan with
            | some principalType =>
                principal.HasDeepTypeFuel fuel signatures plan state principalType
            | none => False
        | .global key =>
            ∃ specialized, exactSpecialization plan key = .ok specialized ∧
              specialized.function.type = expected
        | _ => True

/-- All finite structural-heap observations of one value; this still does not
certify closure code or the runtime evaluator. -/
def Value.HasDeepType (value : Value) (signatures : ProgramSignatures)
    (plan : Plan) (state : RuntimeState) (expected : Ty) : Prop :=
  ∀ fuel, value.HasDeepTypeFuel fuel signatures plan state expected

/-- A concrete occurrence wrapper preserves the principal value's structural
heap typing while exposing the substituted outer type. -/
theorem Value.HasDeepType.instantiated
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {principalType : Ty} {principal : Value}
    (substitution : Substitution)
    (principalShape : principal.type? plan = some principalType)
    (typed : principal.HasDeepType signatures plan state principalType)
    (requirements : List LocalRequirementWitness := []) :
    (Value.instantiated substitution requirements principal).HasDeepType signatures plan
      state (substitution.apply principalType) := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      change (Value.instantiated substitution requirements principal).type? plan =
          some (substitution.apply principalType) ∧
        (match principal.type? plan with
        | some innerType => principal.HasDeepTypeFuel fuel signatures plan
            state innerType
        | none => False)
      constructor
      · simp [Value.type?, principalShape]
      · rw [principalShape]
        exact typed fuel

/-- Type substitution changes an expression node's annotations, but preserves
its stable occurrence identity and its position in the typed-source table. -/
theorem TypedSource.lookupExpression?_applySubstitution
    (source : TypedSource) (substitution : Substitution)
    (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node) :
    (source.applySubstitution substitution).lookupExpression? id =
      some (node.applySubstitution substitution) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found ⊢
  simp only [TypedSource.applySubstitution, List.find?_map]
  have samePredicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        Node.applySubstitution substitution) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases selected : List.find?
      (fun candidate => decide (candidate.occurrenceId = id.occurrence))
      source.nodes with
  | none => simp [selected] at found
  | some candidate =>
      cases candidate with
      | expression selectedNode =>
          simp [selected] at found ⊢
          cases found
          rfl
      | statement selectedNode => simp [selected] at found

/-- Requirement-handle rewriting preserves expression occurrence identity and
returns the pointwise rewritten node at the same table position. -/
theorem TypedSource.lookupExpression?_rewriteLocalRequirements
    (source : TypedSource) (requirements : List LocalRequirementWitness)
    (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node) :
    (rewriteLocalRequirements requirements source).lookupExpression? id =
      some (rewriteExpressionLocalRequirements requirements node) := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found ⊢
  simp only [rewriteLocalRequirements, List.find?_map]
  have samePredicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        rewriteNodeLocalRequirements requirements) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases selected : List.find?
      (fun candidate => decide (candidate.occurrenceId = id.occurrence))
      source.nodes with
  | none => simp [selected] at found
  | some candidate =>
      cases candidate with
      | expression selectedNode =>
          simp [selected] at found ⊢
          cases found
          rfl
      | statement selectedNode => simp [selected] at found

/-- Provenance for the concrete source graph executed by an instantiated
closure.  Besides retaining the principal closure's checked-plan origin, this
relation records that the lambda occurrence survives in the exact
type-substituted and requirement-handle-rewritten image used by
`applyCallable`, with the parameters and result type transformed by the same
substitution. -/
def Value.HasInstantiatedPlanCode (principal : Value)
    (substitution : Substitution) (plan : Plan)
    (requirements : List LocalRequirementWitness := []) : Prop :=
  match principal with
  | .closure parameters resultType body source owner _ _ =>
      validateExecutablePlan plan = .ok () ∧
        ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
          specialized.function.typedBody = source ∧
          ∃ id node, source.lookupExpression? id = some node ∧
            node.form = .lambda parameters resultType body ∧
            node.type = .function
              (Ty.productMany (parameters.map (·.scheme.body))) resultType ∧
            (rewriteLocalRequirements requirements
              (source.applySubstitution substitution)).lookupExpression? id =
              some (rewriteExpressionLocalRequirements requirements
                (node.applySubstitution substitution)) ∧
            (node.applySubstitution substitution).form = .lambda
              (parameters.map (TypedBinder.applySubstitution substitution))
              (substitution.apply resultType) body
  | _ => False

/-- Static provenance of executable code carried by a value.  A closure must
point at a lambda node in the unique checked specialization for its owner;
a global must resolve to a unique specialization.  This relation is separate
from structural heap typing and deliberately does not authenticate a closure's
captured runtime evidence.  Safe entry validation authenticates those evidence
trees; a future whole-evaluator preservation invariant must retain that fact in
addition to this code-only certificate. -/
def Value.HasPlanCodeFuel : Nat → Plan → Value → Prop
  | 0, _, _ => True
  | fuel + 1, plan, value =>
      match value with
      | .product left right =>
          left.HasPlanCodeFuel fuel plan ∧ right.HasPlanCodeFuel fuel plan
      | .constructed _ arguments =>
          ∀ argument, argument ∈ arguments → argument.HasPlanCodeFuel fuel plan
      | .mapping _ _ entries =>
          ∀ entry, entry ∈ entries →
            entry.1.HasPlanCodeFuel fuel plan ∧
              entry.2.HasPlanCodeFuel fuel plan
      | .closure parameters resultType body source owner _ _ =>
          validateExecutablePlan plan = .ok () ∧
            ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
              specialized.function.typedBody = source ∧
              ∃ id node, source.lookupExpression? id = some node ∧
                node.form = .lambda parameters resultType body ∧
                node.type = .function
                  (Ty.productMany (parameters.map (·.scheme.body))) resultType
      | .instantiated substitution requirements principal =>
          principal.HasPlanCodeFuel fuel plan ∧
            principal.HasInstantiatedPlanCode substitution plan requirements
      | .global key =>
          validateExecutablePlan plan = .ok () ∧
            ∃ specialized, exactSpecialization plan key = .ok specialized
      | _ => True

def Value.HasPlanCode (value : Value) (plan : Plan) : Prop :=
  ∀ fuel, value.HasPlanCodeFuel fuel plan

/-- Runtime occurrence instantiation preserves the principal closure's
checked-code provenance and explicitly relates the source graph executed by
`applyCallable` to its type-substituted, requirement-rewritten image. -/
theorem Value.HasPlanCode.instantiated
    {plan : Plan} {parameters : List TypedBinder} {resultType : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {captured : Environment} {evidence : RuntimeEvidenceEnvironment}
    (substitution : Substitution)
    (code : (Value.closure parameters resultType body source owner
      captured evidence).HasPlanCode plan)
    (requirements : List LocalRequirementWitness := []) :
    (Value.instantiated substitution requirements
      (.closure parameters resultType body source owner captured evidence)).HasPlanCode
        plan := by
  have origin := code 1
  change validateExecutablePlan plan = .ok () ∧
    ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
      specialized.function.typedBody = source ∧
      ∃ id node, source.lookupExpression? id = some node ∧
        node.form = .lambda parameters resultType body ∧
        node.type = .function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType at origin
  rcases origin with
    ⟨validated, specialized, specializedAt, sameSource,
      id, node, found, shape, nodeType⟩
  have instantiatedOrigin :
      (Value.closure parameters resultType body source owner captured
        evidence).HasInstantiatedPlanCode substitution plan requirements := by
    exact ⟨validated, specialized, specializedAt, sameSource,
      id, node, found, shape, nodeType,
      TypedSource.lookupExpression?_rewriteLocalRequirements
        (source.applySubstitution substitution) requirements id
        (node.applySubstitution substitution)
        (TypedSource.lookupExpression?_applySubstitution source substitution id
          node found),
      by simp [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
        shape]⟩
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel => exact ⟨code fuel, instantiatedOrigin⟩

/-- Positive instantiated-code provenance exposes both the checked principal
closure and the exact substituted source/lambda relation used by execution. -/
theorem Value.HasPlanCode.instantiated_origin
    {plan : Plan} {substitution : Substitution} {principal : Value}
    {requirements : List LocalRequirementWitness}
    (code : (Value.instantiated substitution requirements principal).HasPlanCode plan) :
    principal.HasPlanCode plan ∧
      principal.HasInstantiatedPlanCode substitution plan requirements := by
  constructor
  · intro fuel
    cases fuel with
    | zero => trivial
    | succ fuel => exact (code (fuel + 2)).1
  · exact (code 1).2

namespace RuntimeState

/-- All initialized heap values carry code provenance to the given plan.
This is independent of structural heap typing and must be preserved alongside
it in a full evaluator proof. -/
def HasPlanCodes (state : RuntimeState) (plan : Plan) : Prop :=
  ∀ cell, cell ∈ state.heap →
    ∀ value, cell.value = some value → value.HasPlanCode plan

end RuntimeState

/-- A no-coercion lambda node evaluates to the closure carrying its checked
source and owner.  This is one concrete evaluator transition linking dynamic
code values to the plan-provenance predicate. -/
theorem evaluate_lambda_hasPlanCode
    (fuel : Nat) (program : CheckedProgram) (plan : Plan) (owner : Key)
    (source : TypedSource)
    (evidence : RuntimeEvidenceEnvironment)
    (environment : Environment) (state : RuntimeState)
    (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId)
    (specialized : SourceSpecialization.SpecializedFunction)
    (validated : validateExecutablePlan plan = .ok ())
    (specializedAt : exactSpecialization plan owner = .ok specialized)
    (sameSource : specialized.function.typedBody = source)
    (found : source.lookupExpression? id = some node)
    (shape : node.form = .lambda parameters resultType body)
    (noCoercions : node.coercions = [])
    (nodeType : node.type = .function
      (Ty.productMany (parameters.map (·.scheme.body))) resultType) :
    evaluate (fuel + 1) program plan owner evidence source environment state id =
      .done (.closure parameters resultType body source owner environment
        evidence) state ∧
    (Value.closure parameters resultType body source owner environment
      evidence).HasPlanCode plan := by
  constructor
  · rw [evaluate.eq_2]
    unfold exactExpression
    rw [found]
    simp [shape, noCoercions, finishExpression, nodeType,
      applyCoercions]
    change (if Value.type? plan
        (.closure parameters resultType body source owner environment evidence) =
        some (Ty.function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType) then
        ExpressionResult.done
          (.closure parameters resultType body source owner environment evidence)
          state
      else
        ExpressionResult.fault (.typeMismatch
          (Ty.function (Ty.productMany (parameters.map (·.scheme.body)))
            resultType)
          (Value.type? plan
            (.closure parameters resultType body source owner environment
              evidence)))
          state) = _
    simp [Value.type?]
  · intro depth
    cases depth with
    | zero => trivial
    | succ depth =>
        exact ⟨validated, specialized, specializedAt, sameSource,
          id, node, found, shape, nodeType⟩

namespace Cell

/-- A cell is deeply typed at the specified approximation depth. -/
def HasDeepTypeFuel (cell : Cell) (fuel : Nat)
    (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState) : Prop :=
  ∀ value, cell.value = some value →
    value.HasDeepTypeFuel fuel signatures plan state cell.type

end Cell

namespace Location

/-- A location names a cell of the expected type whose value is deeply typed
in the same heap world. -/
def HasDeepTypeFuel (location : Location) (fuel : Nat)
    (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState)
    (expected : Ty) : Prop :=
  ∃ cell, state.read? location = some cell ∧ cell.type = expected ∧
    cell.HasDeepTypeFuel fuel signatures plan state

end Location

namespace RuntimeState

/-- All cells are deeply typed relative to a heap world.  Taking the world to
be `state` yields the self-consistent heap invariant below. -/
def HasDeepTypesAtFuel (state world : RuntimeState) (fuel : Nat)
    (signatures : ProgramSignatures) (plan : Plan) : Prop :=
  ∀ cell, cell ∈ state.heap →
    cell.HasDeepTypeFuel fuel signatures plan world

def HasDeepTypesFuel (state : RuntimeState) (fuel : Nat)
    (signatures : ProgramSignatures) (plan : Plan) : Prop :=
  state.HasDeepTypesAtFuel state fuel signatures plan

/-- Every finite *structural heap* observation depth is valid.  Cyclic heaps
are allowed; closure code itself is not checked by this relation. -/
def HasDeepTypes (state : RuntimeState)
    (signatures : ProgramSignatures) (plan : Plan) : Prop :=
  ∀ fuel, state.HasDeepTypesFuel fuel signatures plan

end RuntimeState

private def validateInputs (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) : List Ty → List Value → Option RuntimeError
  | [], [] => none
  | expected :: expectedRest, actual :: actualRest =>
      match actual.validateTypeFuel fuel signatures plan expected with
      | .valid => validateInputs signatures plan fuel expectedRest actualRest
      | .invalid => some (.typeMismatch expected (actual.type? plan))
      | .unsupportedStaged => some (.unsupportedStagedInput expected)
      | .outOfFuel => some (.inputValidationFuelExhausted expected fuel)
  | expected, actual => some (.argumentArityMismatch expected.length actual.length)

/-- Execute a plan whose inputs and embedded nominal metadata have already
been trusted by the caller.  Public boundaries should normally use `run`. -/
def runTrusted (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value)
    (fuel : Nat) (state : RuntimeState := {}) : RunResult :=
  invokeSpecialization fuel program plan entry arguments state

/-- A successful trusted run preserves the inferred result type carried by
the unique specialization selected for its entry key. -/
theorem runTrusted_done_has_inferredBodyType
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : runTrusted program plan entry arguments fuel initial =
      .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  unfold runTrusted at done
  cases fuel with
  | zero =>
      simp [invokeSpecialization] at done
  | succ fuel =>
      rw [invokeSpecialization.eq_2] at done
      unfold exactSpecialization at done
      rw [exact] at done
      simp only at done
      split at done
      · cases done
      · split at done
        · cases done
        · split at done
          · cases done
          · split at done
            · cases done
            · exact finishFunctionFlow_done_type _ _ _ _ _ done

/-- Safe typed-source execution with independent bounds for recursive input
validation and runtime execution.  Constructor inputs are checked against
`ProgramSignatures`, not merely against self-described runtime metadata. -/
def runWithValidationFuel (program : CheckedProgram) (plan : Plan)
    (entry : Key) (arguments : List Value) (validationFuel executionFuel : Nat)
    (state : RuntimeState := {}) : RunResult :=
  match exactSpecialization plan entry with
  | .error error => .fault error state
  | .ok specialized =>
      let expected := specialized.function.typedBody.inputs.map
        (·.scheme.body)
      match validateInputs program.signatures plan validationFuel expected
          arguments with
      | some error => .fault error state
      | none =>
          match validateExecutablePlanEvidence program plan with
          | .error error => .fault error state
          | .ok () => runTrusted program plan entry arguments executionFuel state

/-- Successful safe-boundary execution has the same inferred-result guarantee
as the trusted evaluator reached after input validation. -/
theorem runWithValidationFuel_done_has_inferredBodyType
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (validationFuel executionFuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : runWithValidationFuel program plan entry arguments
      validationFuel executionFuel initial = .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  unfold runWithValidationFuel exactSpecialization at done
  rw [exact] at done
  simp only at done
  split at done
  · cases done
  · split at done
    · cases done
    · exact runTrusted_done_has_inferredBodyType program plan entry arguments
        executionFuel initial finalState value specialized exact done

/-- Compatibility boundary using the same structural fuel for validation and
execution.  New compiler clients can use `runWithValidationFuel` to keep the
two resource policies independent. -/
def run (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (state : RuntimeState := {}) : RunResult :=
  runWithValidationFuel program plan entry arguments fuel fuel state

/-- Convenience projection for clients which only need successful values. -/
def run? (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (state : RuntimeState := {}) : Option (Value × RuntimeState) :=
  match run program plan entry arguments fuel state with
  | .done value finalState => some (value, finalState)
  | .outOfFuel _
  | .fault _ _ => none

/-- A zero validation-depth budget rejects the first expected argument before
allocating a parameter cell or entering the runtime evaluator.  The original
state is therefore preserved exactly. -/
theorem runWithValidationFuel_zero_of_nonempty
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (first : Ty) (expectedRest : List Ty) (value : Value)
    (argumentsRest : List Value) (executionFuel : Nat)
    (state : RuntimeState)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (expected : specialized.function.typedBody.inputs.map
      (·.scheme.body) = first :: expectedRest) :
    runWithValidationFuel program plan entry (value :: argumentsRest)
        0 executionFuel state =
      .fault (.inputValidationFuelExhausted first 0) state := by
  unfold runWithValidationFuel exactSpecialization
  rw [exact]
  simp [expected, validateInputs, Value.validateTypeFuel]


end Solcore.Frontend.SourceTypedRuntime

/-!
## Consolidated module: `Solcore.Frontend.SourceTypedRuntimeProperties`
-/

/-!
Small executable contracts for the phase-7 typed-source runtime.

The phase intentionally prioritizes a complete running language slice over a
large metatheory.  These lemmas nevertheless pin down the public fuel boundary,
the successful-result projection, and representative deep-value validation
rules used at the safe input boundary.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem

@[simp] theorem Cell.hasShallowType_none (plan : Plan) (type : Ty) :
    ({ type, value := none } : Cell).HasShallowType plan := by
  intro value impossible
  cases impossible

theorem Cell.hasShallowType_some
    (plan : Plan) (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    ({ type, value := some value } : Cell).HasShallowType plan := by
  intro selected equal
  cases equal
  exact typed

@[simp] theorem RuntimeState.hasShallowTypes_empty (plan : Plan) :
    ({} : RuntimeState).HasShallowTypes plan := by
  intro cell member
  simp at member

theorem RuntimeState.HasShallowTypes.read
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell}
    (found : state.read? location = some cell) :
    cell.HasShallowType plan := by
  apply typing cell
  exact List.mem_of_getElem? (by
    simpa [RuntimeState.read?] using found)

/-- Reading an initialized cell from a shallow-typed heap yields a value with
the cell's declared type. -/
theorem RuntimeState.HasShallowTypes.read_value
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.type? plan = some cell.type :=
  (typing.read found) value initialized

theorem RuntimeState.HasShallowTypes.allocate
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Option Value)
    (fresh : ({ type, value } : Cell).HasShallowType plan) :
    (state.allocate type value).2.HasShallowTypes plan := by
  intro selected member
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | appended
  · exact typing selected old
  · simp only [List.mem_singleton] at appended
    subst selected
    exact fresh

theorem RuntimeState.HasShallowTypes.allocate_none
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) :
    (state.allocate type none).2.HasShallowTypes plan :=
  typing.allocate type none (Cell.hasShallowType_none plan type)

theorem RuntimeState.HasShallowTypes.allocate_some
    {plan : Plan} {state : RuntimeState} (typing : state.HasShallowTypes plan)
    (type : Ty) (value : Value)
    (typed : value.type? plan = some type) :
    (state.allocate type (some value)).2.HasShallowTypes plan :=
  typing.allocate type (some value)
    (Cell.hasShallowType_some plan type value typed)

theorem RuntimeState.HasShallowTypes.write?_none
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell}
    (found : state.read? location = some previous)
    (written : state.write? location none = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro value impossible
  cases impossible

theorem RuntimeState.HasShallowTypes.write?_some
    {plan : Plan} {state updated : RuntimeState} (typing : state.HasShallowTypes plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (typed : value.type? plan = some previous.type)
    (written : state.write? location (some value) = some updated) :
    updated.HasShallowTypes plan := by
  apply typing.write? found _ written
  intro selected equal
  cases equal
  exact typed

/-- Any positive deep observation includes the outer runtime type tag. -/
theorem Value.HasDeepTypeFuel.shallow
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {expected : Ty} {value : Value}
    (typed : value.HasDeepTypeFuel (fuel + 1) signatures plan state expected) :
    value.type? plan = some expected :=
  typed.1

/-- Deep heap typing refines the existing shallow heap invariant. -/
theorem RuntimeState.HasDeepTypesFuel.shallow
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel (fuel + 1) signatures plan) :
    state.HasShallowTypes plan := by
  intro cell member value initialized
  exact (typing cell member value initialized).shallow

theorem RuntimeState.HasDeepTypes.shallow
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (typing : state.HasDeepTypes signatures plan) :
    state.HasShallowTypes plan :=
  (typing 1).shallow

@[simp] theorem RuntimeState.hasDeepTypes_empty
    (signatures : ProgramSignatures) (plan : Plan) :
    ({} : RuntimeState).HasDeepTypes signatures plan := by
  intro fuel cell member
  simp at member

theorem RuntimeState.HasDeepTypes.read_value
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypes signatures plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.HasDeepType signatures plan state cell.type := by
  intro fuel
  apply typing fuel cell
  · exact List.mem_of_getElem? (by
      simpa [RuntimeState.read?] using found)
  · exact initialized

/-- Deep typing excludes self-consistent but unauthorized nominal constructor
metadata, in addition to checking each paired payload recursively. -/
theorem Value.HasDeepTypeFuel.constructed_authorized
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {expected : Ty}
    {instantiation : DataConstructorInstantiation} {arguments : List Value}
    (typed : (Value.constructed instantiation arguments).HasDeepTypeFuel
      (fuel + 1) signatures plan state expected) :
    validConstructorInstantiation signatures instantiation = true :=
  typed.2.2.1

theorem Value.HasDeepTypeFuel.mapping_entry
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {keyType valueType : Ty}
    {entries : List (Value × Value)} {entry : Value × Value}
    (typed : (Value.mapping keyType valueType entries).HasDeepTypeFuel
      (fuel + 1) signatures plan state (.mapping keyType valueType))
    (member : entry ∈ entries) :
    entry.1.HasDeepTypeFuel fuel signatures plan state keyType ∧
      entry.2.HasDeepTypeFuel fuel signatures plan state valueType :=
  typed.2.2.2 entry member

theorem Value.HasDeepTypeFuel.closure_captured
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {parameters : List TypedBinder}
    {resultType : Ty} {body : List StatementId} {source : TypedSource}
    {owner : Key} {captured : Environment}
    {evidence : RuntimeEvidenceEnvironment}
    {binding : Resolved.LocalId × Location}
    (typed : (Value.closure parameters resultType body source owner captured
      evidence).HasDeepTypeFuel (fuel + 1) signatures plan state
        (.function (Ty.productMany (parameters.map (·.scheme.body))) resultType))
    (member : binding ∈ captured) :
    ∃ cell, state.read? binding.2 = some cell ∧
      cell.HasDeepTypeFuel fuel signatures plan state :=
  typed.2.2 binding member

/-- Inspecting one fewer layer never invalidates deep typing. -/
theorem Value.HasDeepTypeFuel.down
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState} :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      value.HasDeepTypeFuel (fuel + 1) signatures plan state expected →
        value.HasDeepTypeFuel fuel signatures plan state expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value _
      trivial
  | succ fuel inductionHypothesis =>
      intro expected value typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left typed.2.1,
              inductionHypothesis rightType right typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨cell, found, cellTyped⟩ := typed.2.2 binding member
              exact ⟨cell, found,
                fun capturedValue initialized =>
                  inductionHypothesis cell.type capturedValue
                    (cellTyped capturedValue initialized)⟩⟩
      | instantiated substitution _ principal =>
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel (fuel + 1)
                signatures plan state principalType
            | none => False) at typed
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel fuel
                signatures plan state principalType
            | none => False)
          cases h : principal.type? plan with
          | none => rw [h] at typed; exact False.elim typed.2
          | some principalType =>
              rw [h] at typed
              exact ⟨typed.1,
                inductionHypothesis principalType principal typed.2⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

theorem RuntimeState.HasDeepTypesFuel.down
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel (fuel + 1) signatures plan) :
    state.HasDeepTypesFuel fuel signatures plan := by
  intro cell member value initialized
  exact Value.HasDeepTypeFuel.down fuel cell.type value
    (typing cell member value initialized)

/-- A readable initialized cell inherits deep typing from the heap world. -/
theorem RuntimeState.HasDeepTypesFuel.read_value
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (typing : state.HasDeepTypesFuel fuel signatures plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (initialized : cell.value = some value) :
    value.HasDeepTypeFuel fuel signatures plan state cell.type := by
  apply typing cell
  · exact List.mem_of_getElem? (by
      simpa [RuntimeState.read?] using found)
  · exact initialized

/-- Deep values remain typed when every location they can observe continues
to read the same cell.  This forward form handles heap extension, including
closures that capture locations in the old prefix. -/
theorem Value.HasDeepTypeFuel.transport_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState}
    (preserved : ∀ location cell,
      oldWorld.read? location = some cell →
        newWorld.read? location = some cell) :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      value.HasDeepTypeFuel fuel signatures plan oldWorld expected →
        value.HasDeepTypeFuel fuel signatures plan newWorld expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value _
      trivial
  | succ fuel inductionHypothesis =>
      intro expected value typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left typed.2.1,
              inductionHypothesis rightType right typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨cell, found, cellTyped⟩ := typed.2.2 binding member
              exact ⟨cell, preserved binding.2 cell found,
                fun capturedValue initialized =>
                  inductionHypothesis cell.type capturedValue
                    (cellTyped capturedValue initialized)⟩⟩
      | instantiated substitution _ principal =>
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel fuel
                signatures plan oldWorld principalType
            | none => False) at typed
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel fuel
                signatures plan newWorld principalType
            | none => False)
          cases h : principal.type? plan with
          | none => rw [h] at typed; exact False.elim typed.2
          | some principalType =>
              rw [h] at typed
              exact ⟨typed.1,
                inductionHypothesis principalType principal typed.2⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

theorem Value.HasDeepType.transport_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState} {expected : Ty} {value : Value}
    (preserved : ∀ location cell,
      oldWorld.read? location = some cell →
        newWorld.read? location = some cell)
    (typed : value.HasDeepType signatures plan oldWorld expected) :
    value.HasDeepType signatures plan newWorld expected := by
  intro fuel
  exact Value.HasDeepTypeFuel.transport_world preserved fuel expected value
    (typed fuel)

/-- An old value remains deep in a new well-typed world when each location it
could have captured still exists with the same declared type.  At closure
nodes, the new heap invariant supplies the captured cell's new contents. -/
theorem Value.HasDeepTypeFuel.transport_typed_world
    {signatures : ProgramSignatures} {plan : Plan}
    {oldWorld newWorld : RuntimeState}
    (preservedTypes : ∀ location oldCell,
      oldWorld.read? location = some oldCell →
        ∃ newCell, newWorld.read? location = some newCell ∧
          newCell.type = oldCell.type) :
    ∀ (fuel : Nat) (expected : Ty) (value : Value),
      newWorld.HasDeepTypesFuel fuel signatures plan →
      value.HasDeepTypeFuel (fuel + 1) signatures plan oldWorld expected →
        value.HasDeepTypeFuel (fuel + 1) signatures plan newWorld expected := by
  intro fuel
  induction fuel with
  | zero =>
      intro expected value newTyping typed
      cases value with
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨oldCell, found, _⟩ := typed.2.2 binding member
              obtain ⟨newCell, newFound, _⟩ :=
                preservedTypes binding.2 oldCell found
              exact ⟨newCell, newFound, fun _ _ => trivial⟩⟩
      | instantiated _ _ _ => exact typed
      | product _ _ => exact typed
      | mapping _ _ _ => exact typed
      | constructed _ _ => exact typed
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed
  | succ fuel inductionHypothesis =>
      intro expected value newTyping typed
      cases value with
      | product left right =>
          cases expected <;> try exact False.elim typed.2
          case product leftType rightType =>
            exact ⟨typed.1,
              inductionHypothesis leftType left newTyping.down typed.2.1,
              inductionHypothesis rightType right newTyping.down typed.2.2⟩
      | mapping actualKey actualValue entries =>
          cases expected <;> try exact False.elim typed.2
          case mapping keyType valueType =>
            exact ⟨typed.1, typed.2.1, typed.2.2.1,
              fun entry member =>
                ⟨inductionHypothesis keyType entry.1 newTyping.down
                    (typed.2.2.2 entry member).1,
                  inductionHypothesis valueType entry.2 newTyping.down
                    (typed.2.2.2 entry member).2⟩⟩
      | constructed instantiation arguments =>
          exact ⟨typed.1, typed.2.1, typed.2.2.1, typed.2.2.2.1,
            fun pair member =>
              inductionHypothesis pair.1 pair.2 newTyping.down
                (typed.2.2.2.2 pair member)⟩
      | closure parameters resultType body source owner captured =>
          exact ⟨typed.1, typed.2.1,
            fun binding member => by
              obtain ⟨oldCell, found, _⟩ := typed.2.2 binding member
              obtain ⟨newCell, newFound, sameType⟩ :=
                preservedTypes binding.2 oldCell found
              exact ⟨newCell, newFound, fun capturedValue initialized => by
                have typedNew : capturedValue.HasDeepTypeFuel (fuel + 1)
                    signatures plan newWorld newCell.type :=
                  newTyping.read_value newFound initialized
                exact sameType ▸ typedNew⟩⟩
      | instantiated substitution _ principal =>
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel (fuel + 1)
                signatures plan oldWorld principalType
            | none => False) at typed
          change _ ∧ (match principal.type? plan with
            | some principalType => principal.HasDeepTypeFuel (fuel + 1)
                signatures plan newWorld principalType
            | none => False)
          cases h : principal.type? plan with
          | none => rw [h] at typed; exact False.elim typed.2
          | some principalType =>
              rw [h] at typed
              exact ⟨typed.1,
                inductionHypothesis principalType principal newTyping.down
                  typed.2⟩
      | unit => exact typed
      | bool _ => exact typed
      | word _ => exact typed
      | integer _ => exact typed
      | proxy _ => exact typed
      | global _ => exact typed
      | builtin _ => exact typed

/-- Appending a fresh cell does not alter reads of already allocated cells. -/
theorem RuntimeState.read?_allocate_old
    (state : RuntimeState) (type : Ty) (value : Option Value)
    (location : Location) (cell : Cell)
    (found : state.read? location = some cell) :
    (state.allocate type value).2.read? location = some cell := by
  by_cases indexValid : location.index < state.heap.length
  · simpa [RuntimeState.read?, RuntimeState.allocate, List.getElem?_append,
      indexValid] using found
  ·
    have empty : state.heap[location.index]? = none := by
      simp [Nat.le_of_not_lt indexValid]
    simp [RuntimeState.read?, empty] at found

/-- Allocation preserves the self-consistent deep heap invariant when the new
value is deeply typed in the old heap.  Captured closure locations remain
valid because allocation only extends the heap. -/
theorem RuntimeState.HasDeepTypes.allocate_some
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} (typing : state.HasDeepTypes signatures plan)
    (type : Ty) (value : Value)
    (deep : value.HasDeepType signatures plan state type) :
    (state.allocate type (some value)).2.HasDeepTypes signatures plan := by
  intro fuel selected member actual initialized
  have preserved : ∀ location cell,
      state.read? location = some cell →
        (state.allocate type (some value)).2.read? location = some cell := by
    intro location cell found
    exact RuntimeState.read?_allocate_old state type (some value)
      location cell found
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact Value.HasDeepTypeFuel.transport_world preserved fuel selected.type
      actual (typing fuel selected old actual initialized)
  · simp only [List.mem_singleton] at fresh
    subst selected
    cases initialized
    exact Value.HasDeepTypeFuel.transport_world preserved fuel type value
      (deep fuel)

theorem RuntimeState.HasDeepTypes.allocate_none
    {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} (typing : state.HasDeepTypes signatures plan)
    (type : Ty) :
    (state.allocate type none).2.HasDeepTypes signatures plan := by
  intro fuel selected member actual initialized
  have preserved : ∀ location cell,
      state.read? location = some cell →
        (state.allocate type none).2.read? location = some cell := by
    intro location cell found
    exact RuntimeState.read?_allocate_old state type none location cell found
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact Value.HasDeepTypeFuel.transport_world preserved fuel selected.type
      actual (typing fuel selected old actual initialized)
  · simp only [List.mem_singleton] at fresh
    subst selected
    cases initialized

/-- Parameter and pattern binding in the actual evaluator preserves deep heap
typing, provided every supplied value is deeply typed in the entry state.
Heap extension transports the remaining values' captured locations. -/
theorem bindValues_ok_preserves_deep_types
    (signatures : ProgramSignatures) (plan : Plan)
    (bindings : List (TypedBinder × Value))
    (environment finalEnvironment : Environment)
    (state finalState : RuntimeState)
    (typing : state.HasDeepTypes signatures plan)
    (inputs : ∀ binding, binding ∈ bindings →
      binding.2.HasDeepType signatures plan state binding.1.scheme.body)
    (bound : bindValues plan environment state bindings =
      .ok (finalEnvironment, finalState)) :
    finalState.HasDeepTypes signatures plan := by
  induction bindings generalizing environment state with
  | nil =>
      simp [bindValues] at bound
      obtain ⟨rfl, rfl⟩ := bound
      exact typing
  | cons binding rest inductionHypothesis =>
      obtain ⟨binder, value⟩ := binding
      have valueDeep : value.HasDeepType signatures plan state binder.scheme.body :=
        inputs (binder, value) (List.Mem.head rest)
      have valueType : value.type? plan = some binder.scheme.body :=
        (valueDeep 1).shallow
      simp [bindValues, valueType, bne] at bound
      let nextState := (state.allocate binder.scheme.body (some value)).2
      have nextTyping : nextState.HasDeepTypes signatures plan :=
        typing.allocate_some binder.scheme.body value valueDeep
      have nextInputs : ∀ pair, pair ∈ rest →
          pair.2.HasDeepType signatures plan nextState pair.1.scheme.body := by
        intro pair member
        apply Value.HasDeepType.transport_world
        · intro location cell found
          exact RuntimeState.read?_allocate_old state binder.scheme.body
            (some value) location cell found
        · exact inputs pair (List.Mem.tail (binder, value) member)
      exact inductionHypothesis _ _ nextTyping nextInputs bound

/-- Writing a deeply typed cell preserves heap typing relative to a fixed
reference world.  Moving that world to the updated heap additionally requires
the world-transport theorem proved below. -/
theorem RuntimeState.HasDeepTypesAtFuel.write?_some
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state updated world : RuntimeState}
    (typing : state.HasDeepTypesAtFuel world fuel signatures plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (deep : value.HasDeepTypeFuel fuel signatures plan world previous.type)
    (written : state.write? location (some value) = some updated) :
    updated.HasDeepTypesAtFuel world fuel signatures plan := by
  unfold RuntimeState.write? at written
  rw [found] at written
  cases written
  intro selected member
  rcases RuntimeState.mem_replaceCell location.index
      { previous with value := some value } selected state.heap member with
    replaced | old
  · subst selected
    intro actual initialized
    cases initialized
    exact deep
  · exact typing selected old

/-- Every previously readable location remains readable with the same cell
annotation after a successful write.  The optional value may change. -/
theorem RuntimeState.write?_preserves_read_types
    {state updated : RuntimeState} {target : Location}
    {value : Option Value}
    (written : state.write? target value = some updated) :
    ∀ location oldCell,
      state.read? location = some oldCell →
        ∃ newCell, updated.read? location = some newCell ∧
          newCell.type = oldCell.type := by
  intro location oldCell found
  have sameTypes := RuntimeState.write?_typeVector_eq state updated target value
    written
  have oldType : (state.heap.map Cell.type)[location.index]? =
      some oldCell.type := by
    simpa [RuntimeState.read?] using congrArg (Option.map Cell.type) found
  rw [← sameTypes] at oldType
  cases newRead : updated.read? location with
  | none =>
      have noType : (updated.heap.map Cell.type)[location.index]? = none := by
        simpa [RuntimeState.read?] using
          congrArg (Option.map Cell.type) newRead
      rw [noType] at oldType
      cases oldType
  | some newCell =>
      have newType : (updated.heap.map Cell.type)[location.index]? =
          some newCell.type := by
        simpa [RuntimeState.read?] using
          congrArg (Option.map Cell.type) newRead
      rw [newType] at oldType
      exact ⟨newCell, rfl, Option.some.inj oldType⟩

/-- A same-annotation write preserves deep *structural heap* typing when the
replacement is deeply typed in the resulting heap world.  The induction on
observation depth accounts for closures that capture the changed location. -/
theorem RuntimeState.HasDeepTypes.write?_some
    {signatures : ProgramSignatures} {plan : Plan}
    {state updated : RuntimeState}
    (typing : state.HasDeepTypes signatures plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (written : state.write? location (some value) = some updated)
    (deep : value.HasDeepType signatures plan updated previous.type) :
    updated.HasDeepTypes signatures plan := by
  intro fuel
  induction fuel with
  | zero =>
      intro cell member actual initialized
      trivial
  | succ fuel inductionHypothesis =>
      have oldAtNewWorld : state.HasDeepTypesAtFuel updated (fuel + 1)
          signatures plan := by
        intro cell member actual initialized
        exact Value.HasDeepTypeFuel.transport_typed_world
          (RuntimeState.write?_preserves_read_types written)
          fuel cell.type actual inductionHypothesis
          (typing (fuel + 1) cell member actual initialized)
      exact oldAtNewWorld.write?_some found (deep (fuel + 1)) written

@[simp] theorem RuntimeState.hasPlanCodes_empty (plan : Plan) :
    ({} : RuntimeState).HasPlanCodes plan := by
  intro cell member
  simp at member

theorem RuntimeState.HasPlanCodes.allocate_none
    {plan : Plan} {state : RuntimeState}
    (typing : state.HasPlanCodes plan) (type : Ty) :
    (state.allocate type none).2.HasPlanCodes plan := by
  intro cell member value initialized
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact typing cell old value initialized
  · simp only [List.mem_singleton] at fresh
    subst cell
    cases initialized

theorem RuntimeState.HasPlanCodes.allocate_some
    {plan : Plan} {state : RuntimeState}
    (typing : state.HasPlanCodes plan) (type : Ty) (value : Value)
    (code : value.HasPlanCode plan) :
    (state.allocate type (some value)).2.HasPlanCodes plan := by
  intro cell member actual initialized
  simp only [RuntimeState.allocate] at member
  rw [List.mem_append] at member
  rcases member with old | fresh
  · exact typing cell old actual initialized
  · simp only [List.mem_singleton] at fresh
    subst cell
    cases initialized
    exact code

theorem RuntimeState.HasPlanCodes.write?_some
    {plan : Plan} {state updated : RuntimeState}
    (typing : state.HasPlanCodes plan)
    {location : Location} {previous : Cell} {value : Value}
    (found : state.read? location = some previous)
    (code : value.HasPlanCode plan)
    (written : state.write? location (some value) = some updated) :
    updated.HasPlanCodes plan := by
  unfold RuntimeState.write? at written
  rw [found] at written
  cases written
  intro selected member actual initialized
  rcases RuntimeState.mem_replaceCell location.index
      { previous with value := some value } selected state.heap member with
    replaced | old
  · subst selected
    cases initialized
    exact code
  · exact typing selected old actual initialized

/-- The exact structural-update obligation required for a successful place
write.  The leaf `modify` callback alone does not imply this contract: the
recursive updater must also preserve deep typing and code provenance of every
unmodified mapping entry or constructor field. -/
def ResolvedPlace.UpdatePreservesDeepAndCode
    (signatures : ProgramSignatures) (plan : Plan) (state : RuntimeState)
    (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value) : Prop :=
  ∀ cell updated finalState,
    state.read? place.location = some cell →
    cell.type = place.rootType →
    updateResolvedValue plan place.valueType modify
      (initialRootValue cell) place.projections = .ok updated →
    updated.type? plan = some place.rootType →
    state.write? place.location (some updated) = some finalState →
    updated.HasDeepType signatures plan finalState place.rootType ∧
      updated.HasPlanCode plan

/-- A present mapping-key projection reconstructs exactly one mapping after
the recursive child update. -/
theorem updateResolvedValue_index_present_eq
    (plan : Plan) (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child : Value) (entries : List (Value × Value))
    (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child) :
    updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
      .ok (.mapping keyType valueType
        (mappingInsert key child entries)) := by
  simp [updateResolvedValue, keyTyped, bne, found, recursive]
  rfl

/-- When a missing mapping key has a runtime default, that default is the
recursive child; the same mapping frame is reconstructed afterward. -/
theorem updateResolvedValue_index_default_eq
    (plan : Plan) (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child : Value) (entries : List (Value × Value))
    (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child) :
    updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
      .ok (.mapping keyType valueType
        (mappingInsert key child entries)) := by
  simp [updateResolvedValue, keyTyped, bne, missing, defaulted, recursive]
  rfl

/-- A constructor member projection replaces exactly the selected payload
slot after the recursive child update. -/
theorem updateResolvedValue_member_eq
    (plan : Plan) (expected : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat) (selected child : Value)
    (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced) :
    updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) =
      .ok (.constructed instantiation replaced) := by
  simp [updateResolvedValue, found, recursive]
  change (match replaceValueAt index child arguments with
    | some arguments => Except.ok (Value.constructed instantiation arguments)
    | none => Except.error (RuntimeError.invalidMember name index
        ((Value.constructed instantiation arguments).type? plan))) =
      Except.ok (Value.constructed instantiation replaced)
  rw [replacement]

/-- Mapping projection preserves the deep structural and code-provenance
properties when the recursive child and the local mapping frame do. -/
theorem updateResolvedValue_index_present_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacement,
      replacement.HasDeepType signatures plan world valueType →
      replacement.HasPlanCode plan →
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasDeepType
          signatures plan world (.mapping keyType valueType) ∧
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_index_present_eq plan expected keyType valueType
    modify key selected child entries rest keyTyped found recursive] at done
  cases done
  exact frame child childDeep childCode

theorem updateResolvedValue_index_default_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacement,
      replacement.HasDeepType signatures plan world valueType →
      replacement.HasPlanCode plan →
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasDeepType
          signatures plan world (.mapping keyType valueType) ∧
      (Value.mapping keyType valueType
        (mappingInsert key replacement entries)).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_index_default_eq plan expected keyType valueType
    modify key selected child entries rest keyTyped missing defaulted recursive]
    at done
  cases done
  exact frame child childDeep childCode

/-- Mapping insertion is a genuine deep structural frame operation: old
entries keep their typing and code provenance, while the new entry uses the
explicit key and replacement witnesses. -/
theorem Value.mappingInsert_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (keyType valueType : Ty) (entries : List (Value × Value))
    (key replacement : Value)
    (old : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (replacementDeep : replacement.HasDeepType signatures plan world valueType) :
    (Value.mapping keyType valueType
      (mappingInsert key replacement entries)).HasDeepType
        signatures plan world (.mapping keyType valueType) := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro entry member
      rcases mappingInsert_member key replacement entries entry member with
        fresh | retained
      · subst entry
        exact ⟨keyDeep fuel, replacementDeep fuel⟩
      · exact (old (fuel + 1)).2.2.2 entry retained

theorem Value.mappingInsert_hasPlanCode
    (plan : Plan) (keyType valueType : Ty)
    (entries : List (Value × Value)) (key replacement : Value)
    (old : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyCode : key.HasPlanCode plan)
    (replacementCode : replacement.HasPlanCode plan) :
    (Value.mapping keyType valueType
      (mappingInsert key replacement entries)).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro entry member
      rcases mappingInsert_member key replacement entries entry member with
        fresh | retained
      · subst entry
        exact ⟨keyCode fuel, replacementCode fuel⟩
      · exact old (fuel + 1) entry retained

/-- The mapping default constructed for an uninitialized mapping or a fresh
mapping-typed slot has both structural and code-provenance witnesses. -/
theorem Value.emptyMapping_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (keyType valueType : Ty) :
    (Value.mapping keyType valueType []).HasDeepType signatures plan world
      (.mapping keyType valueType) := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro entry member
      cases member

theorem Value.emptyMapping_hasPlanCode
    (plan : Plan) (keyType valueType : Ty) :
    (Value.mapping keyType valueType []).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro entry member
      cases member

/-- The present-key path needs no abstract mapping frame premise once its
existing mapping, key, and updated child are deeply typed. -/
theorem updateResolvedValue_index_present_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (found : mappingLookup? key entries = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (oldDeep : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (oldCode : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (keyCode : key.HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_index_present_preserves signatures plan world
    expected keyType valueType modify key selected child updated entries rest
    keyTyped found recursive childDeep childCode
  · intro replacement replacementDeep replacementCode
    exact ⟨Value.mappingInsert_hasDeepType signatures plan world keyType
        valueType entries key replacement oldDeep keyDeep replacementDeep,
      Value.mappingInsert_hasPlanCode plan keyType valueType entries key
        replacement oldCode keyCode replacementCode⟩
  · exact done

theorem updateResolvedValue_index_default_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected keyType valueType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (key selected child updated : Value)
    (entries : List (Value × Value)) (rest : List RuntimeProjection)
    (keyTyped : key.type? plan = some keyType)
    (missing : mappingLookup? key entries = none)
    (defaulted : defaultValue? (valueType.size + 1) valueType = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (oldDeep : (Value.mapping keyType valueType entries).HasDeepType
      signatures plan world (.mapping keyType valueType))
    (oldCode : (Value.mapping keyType valueType entries).HasPlanCode plan)
    (keyDeep : key.HasDeepType signatures plan world keyType)
    (keyCode : key.HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world valueType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.mapping keyType valueType entries)) (.index key :: rest) =
        .ok updated) :
    updated.HasDeepType signatures plan world (.mapping keyType valueType) ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_index_default_preserves signatures plan world
    expected keyType valueType modify key selected child updated entries rest
    keyTyped missing defaulted recursive childDeep childCode
  · intro replacement replacementDeep replacementCode
    exact ⟨Value.mappingInsert_hasDeepType signatures plan world keyType
        valueType entries key replacement oldDeep keyDeep replacementDeep,
      Value.mappingInsert_hasPlanCode plan keyType valueType entries key
        replacement oldCode keyCode replacementCode⟩
  · exact done

/-- A constructor member projection preserves the invariants when replacing
the chosen payload field is a valid local frame operation. -/
theorem updateResolvedValue_member_preserves
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected fieldType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat)
    (selected child updated : Value) (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced)
    (childDeep : child.HasDeepType signatures plan world fieldType)
    (childCode : child.HasPlanCode plan)
    (frame : ∀ replacementValue replacementArguments,
      replaceValueAt index replacementValue arguments = some
        replacementArguments →
      replacementValue.HasDeepType signatures plan world fieldType →
      replacementValue.HasPlanCode plan →
      (Value.constructed instantiation replacementArguments).HasDeepType
        signatures plan world instantiation.resultType ∧
      (Value.constructed instantiation replacementArguments).HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) = .ok updated) :
    updated.HasDeepType signatures plan world instantiation.resultType ∧
      updated.HasPlanCode plan := by
  rw [updateResolvedValue_member_eq plan expected modify instantiation
    arguments replaced name index selected child rest found recursive replacement]
    at done
  cases done
  exact frame child replaced replacement childDeep childCode

/-- Replacing one payload preserves a pointwise type relation on every
type/value pair in the constructor's zipped payload vector. -/
private theorem replaceValueAt_preserves_zip
    (relation : Ty → Value → Prop) :
    ∀ (index : Nat) (types : List Ty) (arguments replaced : List Value)
      (fieldType : Ty) (replacement : Value),
      types.length = arguments.length →
      (∀ pair, pair ∈ List.zip types arguments → relation pair.1 pair.2) →
      types[index]? = some fieldType →
      relation fieldType replacement →
      replaceValueAt index replacement arguments = some replaced →
      types.length = replaced.length ∧
        ∀ pair, pair ∈ List.zip types replaced → relation pair.1 pair.2 := by
  intro index
  induction index with
  | zero =>
      intro types arguments replaced fieldType replacement lengths old slot
        replacementTyped written
      cases types with
      | nil => simp at slot
      | cons first restTypes =>
          cases arguments with
          | nil => simp [replaceValueAt] at written
          | cons firstValue restValues =>
              simp only [List.getElem?_cons_zero] at slot
              cases slot
              simp [replaceValueAt] at written
              cases written
              have tailLengths : restTypes.length = restValues.length := by
                simpa using lengths
              constructor
              · simpa using tailLengths
              · intro pair member
                simp only [List.zip, List.zipWith, List.mem_cons] at member
                rcases member with head | tail
                · cases head
                  exact replacementTyped
                · exact old pair (by simp [List.zip, List.zipWith, tail])
  | succ index inductionHypothesis =>
      intro types arguments replaced fieldType replacement lengths old slot
        replacementTyped written
      cases types with
      | nil => simp at slot
      | cons first restTypes =>
          cases arguments with
          | nil => simp [replaceValueAt] at written
          | cons firstValue restValues =>
              simp only [List.getElem?_cons_succ] at slot
              have tailLengths : restTypes.length = restValues.length := by
                simpa using lengths
              have oldTail : ∀ pair,
                  pair ∈ List.zip restTypes restValues →
                    relation pair.1 pair.2 := by
                intro pair member
                exact old pair (by
                  simp only [List.zip, List.zipWith, List.mem_cons]
                  exact Or.inr member)
              cases tailWrite : replaceValueAt index replacement restValues with
              | none =>
                  simp [replaceValueAt, tailWrite] at written
              | some replacedTail =>
                  simp [replaceValueAt, tailWrite] at written
                  cases written
                  obtain ⟨newLengths, newTail⟩ :=
                    inductionHypothesis restTypes restValues replacedTail
                      fieldType replacement tailLengths oldTail slot
                      replacementTyped tailWrite
                  constructor
                  · simpa using newLengths
                  · intro pair member
                    simp only [List.zip, List.zipWith, List.mem_cons] at member
                    rcases member with head | tail
                    · cases head
                      exact old (first, firstValue) (by simp [List.zip, List.zipWith])
                    · exact newTail pair tail

private theorem valueTypes?_of_zip
    (plan : Plan) :
    ∀ (types : List Ty) (arguments : List Value),
      types.length = arguments.length →
      (∀ pair, pair ∈ List.zip types arguments →
        pair.2.type? plan = some pair.1) →
      valueTypes? plan arguments = some types := by
  intro types
  induction types with
  | nil =>
      intro arguments lengths typed
      cases arguments with
      | nil => rfl
      | cons _ _ => cases lengths
  | cons first restTypes inductionHypothesis =>
      intro arguments lengths typed
      cases arguments with
      | nil => cases lengths
      | cons firstValue restValues =>
          have headTyped : firstValue.type? plan = some first :=
            typed (first, firstValue) (by simp [List.zip, List.zipWith])
          have tailLengths : restTypes.length = restValues.length := by
            simpa using lengths
          have tailTyped : ∀ pair,
              pair ∈ List.zip restTypes restValues →
                pair.2.type? plan = some pair.1 := by
            intro pair member
            exact typed pair (by
              simp only [List.zip, List.zipWith, List.mem_cons]
              exact Or.inr member)
          have restTyped := inductionHypothesis restValues tailLengths tailTyped
          simp [valueTypes?, headTyped, restTyped]

/-- Replacing one constructor payload with a value of the declared slot type
preserves the authoritative constructor metadata and every payload's deep
structural typing. -/
theorem Value.constructed_replace_hasDeepType
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (index : Nat) (fieldType : Ty) (replacement : Value)
    (old : (Value.constructed instantiation arguments).HasDeepType
      signatures plan world instantiation.resultType)
    (slot : instantiation.payloadTypes[index]? = some fieldType)
    (replacementDeep : replacement.HasDeepType signatures plan world fieldType)
    (written : replaceValueAt index replacement arguments = some replaced) :
    (Value.constructed instantiation replaced).HasDeepType signatures plan
      world instantiation.resultType := by
  have oldLength : instantiation.payloadTypes.length = arguments.length :=
    (old 1).2.2.2.1
  have oldShallow : ∀ pair,
      pair ∈ List.zip instantiation.payloadTypes arguments →
        pair.2.type? plan = some pair.1 := by
    intro pair member
    exact ((old 2).2.2.2.2 pair member).shallow
  obtain ⟨newLength, newShallow⟩ :=
    replaceValueAt_preserves_zip
      (fun type value => value.type? plan = some type) index
      instantiation.payloadTypes arguments replaced fieldType replacement
      oldLength oldShallow slot (replacementDeep 1).shallow written
  have newTypes : valueTypes? plan replaced =
      some instantiation.payloadTypes :=
    valueTypes?_of_zip plan instantiation.payloadTypes replaced newLength
      newShallow
  have outer : (Value.constructed instantiation replaced).type? plan =
      some instantiation.resultType := by
    simp [Value.type?, newTypes]
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      have oldPayloads : ∀ pair,
          pair ∈ List.zip instantiation.payloadTypes arguments →
            pair.2.HasDeepTypeFuel fuel signatures plan world pair.1 :=
        (old (fuel + 1)).2.2.2.2
      obtain ⟨payloadLength, payloads⟩ :=
        replaceValueAt_preserves_zip
          (fun type value =>
            value.HasDeepTypeFuel fuel signatures plan world type)
          index instantiation.payloadTypes arguments replaced fieldType
          replacement oldLength oldPayloads slot (replacementDeep fuel) written
      exact ⟨outer, rfl, (old 1).2.2.1, payloadLength, payloads⟩

theorem Value.constructed_replace_hasPlanCode
    (plan : Plan) (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (index : Nat) (replacement : Value)
    (old : (Value.constructed instantiation arguments).HasPlanCode plan)
    (replacementCode : replacement.HasPlanCode plan)
    (written : replaceValueAt index replacement arguments = some replaced) :
    (Value.constructed instantiation replaced).HasPlanCode plan := by
  intro fuel
  cases fuel with
  | zero => trivial
  | succ fuel =>
      intro selected member
      rcases replaceValueAt_member index replacement arguments replaced
          selected written member with fresh | retained
      · subst selected
        exact replacementCode fuel
      · exact old (fuel + 1) selected retained

/-- The member-projection update no longer needs an abstract frame premise:
the payload slot type and the old constructor's invariants suffice. -/
theorem updateResolvedValue_member_preserves_from_parts
    (signatures : ProgramSignatures) (plan : Plan) (world : RuntimeState)
    (expected fieldType : Ty)
    (modify : Option Value → Except RuntimeError Value)
    (instantiation : DataConstructorInstantiation)
    (arguments replaced : List Value)
    (name : String) (index : Nat)
    (selected child updated : Value) (rest : List RuntimeProjection)
    (found : arguments[index]? = some selected)
    (slot : instantiation.payloadTypes[index]? = some fieldType)
    (recursive : updateResolvedValue plan expected modify (some selected)
      rest = .ok child)
    (replacement : replaceValueAt index child arguments = some replaced)
    (oldDeep : (Value.constructed instantiation arguments).HasDeepType
      signatures plan world instantiation.resultType)
    (oldCode : (Value.constructed instantiation arguments).HasPlanCode plan)
    (childDeep : child.HasDeepType signatures plan world fieldType)
    (childCode : child.HasPlanCode plan)
    (done : updateResolvedValue plan expected modify
      (some (.constructed instantiation arguments))
      (.member name index :: rest) = .ok updated) :
    updated.HasDeepType signatures plan world instantiation.resultType ∧
      updated.HasPlanCode plan := by
  apply updateResolvedValue_member_preserves signatures plan world expected
    fieldType modify instantiation arguments replaced name index selected child
    updated rest found recursive replacement childDeep childCode
  · intro replacementValue replacementArguments replacedAt deep code
    exact ⟨Value.constructed_replace_hasDeepType signatures plan world
        instantiation arguments replacementArguments index fieldType
        replacementValue oldDeep slot deep replacedAt,
      Value.constructed_replace_hasPlanCode plan instantiation arguments
        replacementArguments index replacementValue oldCode code replacedAt⟩
  · exact done

/-- A successful place write decomposes into a matching root cell, a
successful recursive structural update, and a concrete heap write. -/
theorem writeResolvedPlace_done_components
    (plan : Plan) (state finalState : RuntimeState)
    (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    ∃ cell,
      state.read? place.location = some cell ∧
      cell.type = place.rootType ∧
      updateResolvedValue plan place.valueType modify
        (initialRootValue cell) place.projections = .ok updated ∧
      updated.type? plan = some place.rootType ∧
      state.write? place.location (some updated) = some finalState := by
  unfold writeResolvedPlace at done
  cases found : state.read? place.location with
  | none => simp [found] at done
  | some cell =>
      simp only [found] at done
      by_cases sameType : cell.type = place.rootType
      · have noMismatch : (cell.type != place.rootType) = false := by
          simp [sameType]
        rw [noMismatch] at done
        simp only [Bool.false_eq_true, ↓reduceIte] at done
        cases updateResult : updateResolvedValue plan place.valueType modify
            (initialRootValue cell) place.projections with
        | error error =>
            rw [updateResult] at done
            cases done
        | ok next =>
            rw [updateResult] at done
            by_cases nextType : next.type? plan = some place.rootType
            · simp [nextType] at done
              cases written : state.write? place.location (some next) with
              | none => simp [written] at done
              | some nextState =>
                  simp [written] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact ⟨cell, rfl, sameType, updateResult, nextType,
                    written⟩
            · simp [nextType] at done
      · simp [sameType] at done

/-- The assignment's final structural write preserves both established
runtime invariants under the precise update contract above. -/
theorem writeResolvedPlace_done_preserves_deep_and_code
    (signatures : ProgramSignatures) (plan : Plan)
    (state finalState : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (deepHeap : state.HasDeepTypes signatures plan)
    (codeHeap : state.HasPlanCodes plan)
    (updatePreserves : place.UpdatePreservesDeepAndCode signatures plan state
      modify)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    finalState.HasDeepTypes signatures plan ∧
      finalState.HasPlanCodes plan := by
  obtain ⟨cell, found, sameType, updatedByPath, updatedType, written⟩ :=
    writeResolvedPlace_done_components plan state finalState place modify
      updated done
  obtain ⟨updatedDeep, updatedCode⟩ :=
    updatePreserves cell updated finalState found sameType updatedByPath
      updatedType written
  constructor
  · apply deepHeap.write?_some found written
    simpa [sameType] using updatedDeep
  · exact codeHeap.write?_some found updatedCode written

/-- For a root assignment with no projections, the structural-update
contract reduces to the leaf modifier's successful-result contract. -/
theorem ResolvedPlace.updatePreservesDeepAndCode_root
    (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (root : place.projections = [])
    (modifyPreserves : ∀ cell candidate finalState,
      state.read? place.location = some cell →
      cell.type = place.rootType →
      modify (initialRootValue cell) = .ok candidate →
      candidate.type? plan = some place.valueType →
      candidate.type? plan = some place.rootType →
      state.write? place.location (some candidate) = some finalState →
      candidate.HasDeepType signatures plan finalState place.rootType ∧
        candidate.HasPlanCode plan) :
    place.UpdatePreservesDeepAndCode signatures plan state modify := by
  intro cell candidate finalState found sameType updatedByPath rootType written
  rw [root] at updatedByPath
  simp only [updateResolvedValue] at updatedByPath
  cases modified : modify (initialRootValue cell) with
  | error error =>
      rw [modified] at updatedByPath
      change Except.error error = Except.ok candidate at updatedByPath
      cases updatedByPath
  | ok modifiedValue =>
      by_cases valueType : modifiedValue.type? plan = some place.valueType
      · rw [modified] at updatedByPath
        change (if modifiedValue.type? plan = some place.valueType then
            Except.ok modifiedValue else
            Except.error (RuntimeError.typeMismatch place.valueType
              (modifiedValue.type? plan))) = .ok candidate at updatedByPath
        simp [valueType] at updatedByPath
        cases updatedByPath
        exact modifyPreserves cell candidate finalState found sameType
          modified valueType rootType written
      · rw [modified] at updatedByPath
        change (if modifiedValue.type? plan = some place.valueType then
            Except.ok modifiedValue else
            Except.error (RuntimeError.typeMismatch place.valueType
              (modifiedValue.type? plan))) = .ok candidate at updatedByPath
        simp [valueType] at updatedByPath

/-- Executing a root assignment preserves both invariants under a contract
on the leaf callback alone.  Projected assignments use the general theorem
and still need an inductive proof for `updateResolvedValue`. -/
theorem writeResolvedPlace_done_preserves_root_deep_and_code
    (signatures : ProgramSignatures) (plan : Plan)
    (state finalState : RuntimeState) (place : ResolvedPlace)
    (modify : Option Value → Except RuntimeError Value)
    (updated : Value)
    (deepHeap : state.HasDeepTypes signatures plan)
    (codeHeap : state.HasPlanCodes plan)
    (root : place.projections = [])
    (modifyPreserves : ∀ cell candidate nextState,
      state.read? place.location = some cell →
      cell.type = place.rootType →
      modify (initialRootValue cell) = .ok candidate →
      candidate.type? plan = some place.valueType →
      candidate.type? plan = some place.rootType →
      state.write? place.location (some candidate) = some nextState →
      candidate.HasDeepType signatures plan nextState place.rootType ∧
        candidate.HasPlanCode plan)
    (done : writeResolvedPlace plan state place modify =
      .done updated finalState) :
    finalState.HasDeepTypes signatures plan ∧
      finalState.HasPlanCodes plan := by
  apply writeResolvedPlace_done_preserves_deep_and_code signatures plan
    state finalState place modify updated deepHeap codeHeap
  · exact place.updatePreservesDeepAndCode_root signatures plan state modify
      root modifyPreserves
  · exact done

/-- The evaluator's parameter/pattern binding helper keeps static code
provenance in the heap when the supplied values have that provenance. -/
theorem bindValues_ok_preserves_plan_codes
    (plan : Plan) (bindings : List (TypedBinder × Value))
    (environment finalEnvironment : Environment)
    (state finalState : RuntimeState)
    (typing : state.HasPlanCodes plan)
    (inputs : ∀ binding, binding ∈ bindings → binding.2.HasPlanCode plan)
    (bound : bindValues plan environment state bindings =
      .ok (finalEnvironment, finalState)) :
    finalState.HasPlanCodes plan := by
  induction bindings generalizing environment state with
  | nil =>
      simp [bindValues] at bound
      obtain ⟨rfl, rfl⟩ := bound
      exact typing
  | cons binding rest inductionHypothesis =>
      obtain ⟨binder, value⟩ := binding
      have valueCode : value.HasPlanCode plan :=
        inputs (binder, value) (List.Mem.head rest)
      by_cases typed : value.type? plan = some binder.scheme.body
      · simp [bindValues, typed, bne] at bound
        have restInputs : ∀ pair, pair ∈ rest →
            pair.2.HasPlanCode plan := by
          intro pair member
          exact inputs pair (List.Mem.tail (binder, value) member)
        exact inductionHypothesis _ _
          (typing.allocate_some binder.scheme.body value valueCode)
          restInputs bound
      · simp [bindValues, typed, bne] at bound
        change Except.error _ = Except.ok (finalEnvironment, finalState) at bound
        cases bound

theorem unit_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) :
    Value.hasType signatures plan (fuel + 1) .unit .unit = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.unit, Nat.add_one]
  rw [Value.validateTypeFuel.eq_2]
  rfl

theorem bool_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Bool) :
    Value.hasType signatures plan (fuel + 1) .bool (.bool value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.bool, Nat.add_one]
  rw [Value.validateTypeFuel.eq_3]
  rfl

theorem word_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (value : Core.Word) :
    Value.hasType signatures plan (fuel + 1) .word (.word value) = true := by
  unfold Value.hasType Value.hasTypeFuel
  simp only [Ty.word, Nat.add_one]
  rw [Value.validateTypeFuel.eq_4]
  rfl

theorem proxy_hasType (signatures : ProgramSignatures) (plan : Plan)
    (fuel : Nat) (inner : Ty) :
    Value.hasType signatures plan (fuel + 1) (.proxy inner) (.proxy inner) =
      true := by
  unfold Value.hasType Value.hasTypeFuel
  rw [Nat.add_one, Value.validateTypeFuel.eq_7]
  split
  · change true = true
    rfl
  · contradiction

theorem zero_fuel_validateType (signatures : ProgramSignatures) (plan : Plan)
    (expected : Ty) (value : Value) :
    value.validateTypeFuel 0 signatures plan expected = .outOfFuel := by
  rw [Value.validateTypeFuel.eq_1]

theorem zero_fuel_runTrusted (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (state : RuntimeState) :
    runTrusted program plan entry arguments 0 state = .outOfFuel state := by
  rfl

theorem run_eq_runWithValidationFuel (program : CheckedProgram)
    (plan : Plan) (entry : Key) (arguments : List Value) (fuel : Nat)
    (state : RuntimeState) :
    run program plan entry arguments fuel state =
      runWithValidationFuel program plan entry arguments fuel fuel state := by
  rfl

theorem run_done_has_inferredBodyType
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : run program plan entry arguments fuel initial =
      .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  exact runWithValidationFuel_done_has_inferredBodyType program plan entry
    arguments fuel fuel initial finalState value specialized exact done

theorem run?_some_iff (program : CheckedProgram) (plan : Plan)
    (entry : Key) (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value) :
    run? program plan entry arguments fuel initial =
        some (value, finalState) ↔
      run program plan entry arguments fuel initial =
        .done value finalState := by
  unfold run?
  split <;> simp_all

theorem run?_some_has_inferredBodyType
    (program : CheckedProgram) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (success : run? program plan entry arguments fuel initial =
      some (value, finalState)) :
    value.type? plan = some specialized.function.inferredBodyType := by
  apply run_done_has_inferredBodyType program plan entry arguments fuel
    initial finalState value specialized exact
  exact (run?_some_iff program plan entry arguments fuel initial finalState
    value).mp success

end Solcore.Frontend.SourceTypedRuntime
