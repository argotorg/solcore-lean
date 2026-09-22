import Solcore.Core.Primitive
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
    | .closure parameters resultType _ _ _ _ =>
        some (.function (Ty.productMany (parameters.map (·.scheme.body))) resultType)
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
  | invalidFunctionType (key : Key) (type : Ty)
  | inferredResultTypeMismatch (key : Key) (declared inferred : Ty)
  | unresolvedAssumptions (key : Key) (predicates : List ProgramPredicate)
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
  | duplicateReferenceEdge (caller : Key) (id : ExpressionId) (count : Nat)
  | missingReferenceEdge (caller : Key) (id : ExpressionId)
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

private def exactCallKey (plan : Plan) (caller : Key) (id : ExpressionId) :
    Except RuntimeError Key :=
  match plan.callEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) with
  | [] => .error (.missingCallEdge caller id)
  | [edge] => .ok edge.callee
  | edges => .error (.duplicateCallEdge caller id edges.length)

private def exactReferenceKey (plan : Plan) (caller : Key)
    (id : ExpressionId) : Except RuntimeError Key :=
  match plan.referenceEdges.filter fun edge =>
      decide (edge.caller = caller) && decide (edge.occurrence = id) with
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

private def exactSolvedRequirement? (function : CheckedFunction)
    (id : RequirementId) : Option SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.id == id with
  | [solved] => some solved
  | _ => none

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

private def validateExpressionMetadata (function : CheckedFunction)
    (node : ExpressionNode) : Except RuntimeError Unit := do
  unless node.coercions.isEmpty do
    throw (.unsupportedExpressionCoercions node.id)
  match node.form with
  | .integerLiteral source resolution =>
      unless node.requirements = [resolution.requirement] do
        throw (.unsupportedRequirements node.requirements)
      validateLiteralResolution function source resolution
  | .call _ _ (.indirect metadata) =>
      unless metadata.argumentCoercions.isEmpty do
        throw (.unsupportedIndirectCoercions node.id)
      unless node.requirements.isEmpty do
        throw (.unsupportedRequirements node.requirements)
  | _ =>
      unless node.requirements.isEmpty do
        throw (.unsupportedRequirements node.requirements)

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
private def validateExecutableMetadata (function : CheckedFunction) :
    Except RuntimeError Unit :=
  for node in function.typedBody.nodes do
    match node with
    | .expression expression => validateExpressionMetadata function expression
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

private def validateSpecializationMetadata
    (specialized : SourceSpecialization.SpecializedFunction) :
    Except RuntimeError Unit := do
  unless specialized.assumptions.isEmpty do
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
  validateExecutableMetadata specialized.function
  let declaredResult ← match resultType? specialized.function with
    | some result => pure result
    | none => throw (.invalidFunctionType specialized.key
        specialized.function.type)
  unless declaredResult = specialized.function.inferredBodyType do
    throw (.inferredResultTypeMismatch specialized.key declaredResult
      specialized.function.inferredBodyType)

/-- Preflight every reachable specialization before selecting this runtime as
an executable backend.  The canonical worklist has already fixed the finite
call graph; this pass rejects metadata which the typed runtime deliberately
does not dispatch instead of postponing that rejection until a call happens. -/
def validateExecutablePlan (plan : Plan) : Except RuntimeError Unit := do
  for specialized in plan.specializations do
    validateSpecializationMetadata specialized

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

mutual

  private def evaluate (fuel : Nat) (plan : Plan) (owner : Key)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (id : ExpressionId) : ExpressionResult :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactExpression source id with
      | .error error => .fault error state
      | .ok node =>
        let descend := evaluate fuel plan owner source environment
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
                  | some { value := some value, .. } => .done value state
          | .reference _ (.builtinBoolean value) =>
              .done (.bool value) state
          | .reference _ (.builtinFunction function) =>
              .done (.builtin function) state
          | .reference _ (.declaration _) =>
              match exactReferenceKey plan owner id with
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
              .done (.closure parameters resultType body source owner environment)
                state
          | .call _ arguments (.declaration _) =>
              match evaluateList descend state arguments with
              | .done values finalState =>
                  match exactCallKey plan owner id with
                  | .ok key => applyCallable fuel plan (.global key) values finalState
                  | .error error => .fault error finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .call _ arguments (.builtinFunction function) =>
              match evaluateList descend state arguments with
              | .done values finalState =>
                  applyCallable fuel plan (.builtin function) values finalState
              | .outOfFuel finalState => .outOfFuel finalState
              | .fault error finalState => .fault error finalState
          | .call callee arguments (.indirect _) =>
              match descend state callee with
              | .done functionValue argumentState =>
                  match evaluateList descend argumentState arguments with
                  | .done values finalState =>
                      applyCallable fuel plan functionValue values finalState
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
        finishExpression plan node raw

  private def applyCallable (fuel : Nat) (plan : Plan) (function : Value)
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
          expressionOfRunResult (invokeSpecialization fuel plan key arguments state)
      | .closure parameters expected body source owner captured =>
          if parameters.length != arguments.length then
            .fault (.argumentArityMismatch parameters.length arguments.length) state
          else
            match bindValues plan captured state (List.zip parameters arguments) with
            | .error error => .fault error state
            | .ok (environment, bodyState) =>
                let flow := executeSequence
                  (executeStatement fuel plan owner source) environment bodyState body
                expressionOfRunResult (finishFunctionFlow plan expected flow)
      | actual => .fault (.expectedFunction (actual.type? plan)) state

  private def invokeSpecialization (fuel : Nat) (plan : Plan) (key : Key)
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
                        let flow := executeSequence
                          (executeStatement fuel plan key function.typedBody)
                          environment bodyState roots
                        finishFunctionFlow plan expected flow

  private def executeStatement (fuel : Nat) (plan : Plan) (owner : Key)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (id : StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match exactStatement source id with
      | .error error => .fault error state
      | .ok node =>
        let descend := evaluate fuel plan owner source environment
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
                  (executeStatement fuel plan owner source)
                  environment branchState thenBody
            | .done (.bool false) branchState =>
                match elseBody with
                | none => .fallthrough environment branchState
                | some body => restoreScope environment <| executeSequence
                    (executeStatement fuel plan owner source)
                    environment branchState body
            | .done actual finalState =>
                .fault (.expectedBool (actual.type? plan)) finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .block body => restoreScope environment <| executeSequence
            (executeStatement fuel plan owner source) environment state body
        | .matchWith resolution =>
            match descend state resolution.scrutinee with
            | .done scrutinee matchState =>
                let scrutineeType := (scrutinee.type? plan).getD Ty.error
                let (hidden, hiddenState) := matchState.allocate
                  scrutineeType (some scrutinee)
                let matchEnvironment :=
                  (resolution.hiddenScrutinee, hidden) :: environment
                restoreScope environment <| executeMatchCases fuel plan owner
                  source matchEnvironment hiddenState scrutinee
                  resolution.cases resolution.defaultBody
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .forLoop initializer condition post body =>
            match executeForItems fuel plan owner source environment state
                initializer with
            | .fallthrough loopEnvironment loopState =>
                restoreScope environment <| executeForIterations fuel plan owner
                  source loopEnvironment loopState condition post body
            | .returned value finalState => .returned value finalState
            | .breaking _ finalState
            | .continuing _ finalState =>
                .fault .controlEscapedFunction finalState
            | .outOfFuel finalState => .outOfFuel finalState
            | .fault error finalState => .fault error finalState
        | .whileLoop condition body =>
            restoreScope environment <| executeWhile fuel plan owner source
              environment state condition body
        | .breakStmt => .breaking environment state
        | .continueStmt => .continuing environment state

  private def executeWhile (fuel : Nat) (plan : Plan) (owner : Key)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (condition : ExpressionId)
      (body : List StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match evaluate fuel plan owner source environment state condition with
      | .done (.bool false) finalState =>
          .fallthrough environment finalState
      | .done (.bool true) bodyState =>
          let outcome := restoreScope environment <| executeSequence
            (executeStatement fuel plan owner source)
            environment bodyState body
          match outcome with
          | .fallthrough nextEnvironment nextState
          | .continuing nextEnvironment nextState =>
              executeWhile fuel plan owner source nextEnvironment nextState
                condition body
          | .breaking _ finalState => .fallthrough environment finalState
          | .returned value finalState => .returned value finalState
          | .outOfFuel finalState => .outOfFuel finalState
          | .fault error finalState => .fault error finalState
      | .done actual finalState =>
          .fault (.expectedBool (actual.type? plan)) finalState
      | .outOfFuel finalState => .outOfFuel finalState
      | .fault error finalState => .fault error finalState

  private def executeForIterations (fuel : Nat) (plan : Plan) (owner : Key)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (condition : ExpressionId)
      (post : List ForItemForm) (body : List StatementId) : FlowOutcome :=
    match fuel with
    | 0 => .outOfFuel state
    | fuel + 1 =>
      match evaluate fuel plan owner source environment state condition with
      | .done (.bool false) finalState =>
          .fallthrough environment finalState
      | .done (.bool true) bodyState =>
          let outcome := restoreScope environment <| executeSequence
            (executeStatement fuel plan owner source)
            environment bodyState body
          match outcome with
          | .breaking _ finalState => .fallthrough environment finalState
          | .returned value finalState => .returned value finalState
          | .outOfFuel finalState => .outOfFuel finalState
          | .fault error finalState => .fault error finalState
          | .fallthrough postEnvironment postState
          | .continuing postEnvironment postState =>
              match executeForItems fuel plan owner source postEnvironment
                  postState post with
              | .fallthrough nextEnvironment nextState =>
                  executeForIterations fuel plan owner source nextEnvironment
                    nextState condition post body
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

  private def executeForItems (fuel : Nat) (plan : Plan) (owner : Key)
      (source : TypedSource) (environment : Environment)
      (state : RuntimeState) (items : List ForItemForm) : FlowOutcome :=
    match items with
    | [] => .fallthrough environment state
    | item :: rest =>
      match fuel with
      | 0 => .outOfFuel state
      | fuel + 1 =>
        let descend := evaluate fuel plan owner source environment
        let next (nextEnvironment : Environment) (nextState : RuntimeState) :=
          executeForItems fuel plan owner source nextEnvironment nextState rest
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

  private def executeMatchCases (fuel : Nat) (plan : Plan) (owner : Key)
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
              (executeStatement fuel plan owner source) environment state body
      | arm :: rest =>
          match matchPattern arm.pattern scrutinee with
          | .malformed => .fault .malformedPattern state
          | .noMatch => executeMatchCases fuel plan owner source environment
              state scrutinee rest defaultBody
          | .matched bindings =>
              match bindValues plan environment state bindings with
              | .error error => .fault error state
              | .ok (armEnvironment, armState) =>
                  restoreScope environment <| executeSequence
                    (executeStatement fuel plan owner source)
                    armEnvironment armState arm.body

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
closure's `body`, `source`, or `owner` against the typed plan.  A whole-language
type-preservation theorem needs that separate static closure certificate and
an evaluator induction in addition to this heap invariant. -/
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
        | .closure parameters resultType _ _ _ captured =>
            expected = .function
              (Ty.productMany (parameters.map (·.scheme.body))) resultType ∧
              ∀ binding, binding ∈ captured →
                ∃ cell, state.read? binding.2 = some cell ∧
                  ∀ capturedValue, cell.value = some capturedValue →
                    capturedValue.HasDeepTypeFuel fuel signatures plan state cell.type
        | .global key =>
            ∃ specialized, exactSpecialization plan key = .ok specialized ∧
              specialized.function.type = expected
        | _ => True

/-- All finite structural-heap observations of one value; this still does not
certify closure code or the runtime evaluator. -/
def Value.HasDeepType (value : Value) (signatures : ProgramSignatures)
    (plan : Plan) (state : RuntimeState) (expected : Ty) : Prop :=
  ∀ fuel, value.HasDeepTypeFuel fuel signatures plan state expected

/-- Static provenance of executable code carried by a value.  A closure must
point at a lambda node in the unique checked specialization for its owner;
a global must resolve to a unique specialization.  This relation is separate
from structural heap typing, and does not by itself prove the checked IR's
semantic type-soundness. -/
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
      | .closure parameters resultType body source owner _ =>
          validateExecutablePlan plan = .ok () ∧
            ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
              specialized.function.typedBody = source ∧
              ∃ id node, source.lookupExpression? id = some node ∧
                node.form = .lambda parameters resultType body ∧
                node.type = .function
                  (Ty.productMany (parameters.map (·.scheme.body))) resultType
      | .global key =>
          validateExecutablePlan plan = .ok () ∧
            ∃ specialized, exactSpecialization plan key = .ok specialized
      | _ => True

def Value.HasPlanCode (value : Value) (plan : Plan) : Prop :=
  ∀ fuel, value.HasPlanCodeFuel fuel plan

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
    (fuel : Nat) (plan : Plan) (owner : Key) (source : TypedSource)
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
    evaluate (fuel + 1) plan owner source environment state id =
      .done (.closure parameters resultType body source owner environment)
        state ∧
    (Value.closure parameters resultType body source owner environment).HasPlanCode
      plan := by
  constructor
  · rw [evaluate.eq_2]
    unfold exactExpression
    rw [found]
    simp [shape, noCoercions, finishExpression, nodeType,
      applyCoercions]
    change (if Value.type? plan
        (.closure parameters resultType body source owner environment) =
        some (Ty.function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType) then
        ExpressionResult.done
          (.closure parameters resultType body source owner environment)
          state
      else
        ExpressionResult.fault (.typeMismatch
          (Ty.function (Ty.productMany (parameters.map (·.scheme.body)))
            resultType)
          (Value.type? plan
            (.closure parameters resultType body source owner environment)))
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
def runTrusted (plan : Plan) (entry : Key) (arguments : List Value)
    (fuel : Nat) (state : RuntimeState := {}) : RunResult :=
  invokeSpecialization fuel plan entry arguments state

/-- A successful trusted run preserves the inferred result type carried by
the unique specialization selected for its entry key. -/
theorem runTrusted_done_has_inferredBodyType
    (plan : Plan) (entry : Key) (arguments : List Value) (fuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : runTrusted plan entry arguments fuel initial =
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
def runWithValidationFuel (signatures : ProgramSignatures) (plan : Plan)
    (entry : Key) (arguments : List Value) (validationFuel executionFuel : Nat)
    (state : RuntimeState := {}) : RunResult :=
  match exactSpecialization plan entry with
  | .error error => .fault error state
  | .ok specialized =>
      let expected := specialized.function.typedBody.inputs.map
        (·.scheme.body)
      match validateInputs signatures plan validationFuel expected arguments with
      | some error => .fault error state
      | none => runTrusted plan entry arguments executionFuel state

/-- Successful safe-boundary execution has the same inferred-result guarantee
as the trusted evaluator reached after input validation. -/
theorem runWithValidationFuel_done_has_inferredBodyType
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (validationFuel executionFuel : Nat)
    (initial finalState : RuntimeState) (value : Value)
    (specialized : SourceSpecialization.SpecializedFunction)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (done : runWithValidationFuel signatures plan entry arguments
      validationFuel executionFuel initial = .done value finalState) :
    value.type? plan = some specialized.function.inferredBodyType := by
  unfold runWithValidationFuel exactSpecialization at done
  rw [exact] at done
  simp only at done
  split at done
  · cases done
  · exact runTrusted_done_has_inferredBodyType plan entry arguments
      executionFuel initial finalState value specialized exact done

/-- Compatibility boundary using the same structural fuel for validation and
execution.  New compiler clients can use `runWithValidationFuel` to keep the
two resource policies independent. -/
def run (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (state : RuntimeState := {}) : RunResult :=
  runWithValidationFuel signatures plan entry arguments fuel fuel state

/-- Convenience projection for clients which only need successful values. -/
def run? (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (arguments : List Value) (fuel : Nat)
    (state : RuntimeState := {}) : Option (Value × RuntimeState) :=
  match run signatures plan entry arguments fuel state with
  | .done value finalState => some (value, finalState)
  | .outOfFuel _
  | .fault _ _ => none

/-- A zero validation-depth budget rejects the first expected argument before
allocating a parameter cell or entering the runtime evaluator.  The original
state is therefore preserved exactly. -/
theorem runWithValidationFuel_zero_of_nonempty
    (signatures : ProgramSignatures) (plan : Plan) (entry : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (first : Ty) (expectedRest : List Ty) (value : Value)
    (argumentsRest : List Value) (executionFuel : Nat)
    (state : RuntimeState)
    (exact : plan.specializations.filter (fun candidate =>
      decide (candidate.key = entry)) = [specialized])
    (expected : specialized.function.typedBody.inputs.map
      (·.scheme.body) = first :: expectedRest) :
    runWithValidationFuel signatures plan entry (value :: argumentsRest)
        0 executionFuel state =
      .fault (.inputValidationFuelExhausted first 0) state := by
  unfold runWithValidationFuel exactSpecialization
  rw [exact]
  simp [expected, validateInputs, Value.validateTypeFuel]


end Solcore.Frontend.SourceTypedRuntime
