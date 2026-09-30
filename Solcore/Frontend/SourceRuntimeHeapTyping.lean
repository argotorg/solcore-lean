import Solcore.Frontend.SourceRuntimeValidation

/-! Pure source heap typing and checked-code provenance shared with Core
adapters. Structural typing admits cycles through finite observations; code
provenance records original source tables and exact local substitutions.
No expression, statement, or callable evaluator is imported or defined here. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceTypedRuntime
open SourceInference TypeSystem SourceCompilationPlan

namespace Cell

/-- Shallow agreement between a heap cell's declared type and its initialized
value.  This deliberately follows `Value.type?`: it does not validate mapping
entries, closure bodies or captures, constructor catalog authenticity, or the
heap reachable through captured locations.  Uninitialized cells are valid. -/
def HasShallowType (cell : Cell) (plan : Plan) : Prop :=
  ∀ value, cell.value = some value →
    value.type? plan = some (runtimeType cell.type)

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
    (typed : value.type? plan = some (runtimeType type)) :
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

def rewriteLocalRequirement
    (requirements : List LocalRequirementWitness)
    (requirement : RequirementId) : RequirementId :=
  match requirements.find? fun witness =>
      witness.templateRequirement == requirement with
  | some witness => witness.actualRequirement
  | none => requirement

def rewriteExpressionLocalRequirements
    (requirements : List LocalRequirementWitness)
    (node : ExpressionNode) : ExpressionNode := {
  node with
  requirements := node.requirements.map
    (rewriteLocalRequirement requirements)
}

def rewriteNodeLocalRequirements
    (requirements : List LocalRequirementWitness) : Node → Node
  | .expression node =>
      .expression (rewriteExpressionLocalRequirements requirements node)
  | node => node

/-- Rewrite only the expression-level requirement ledger.  The qualified
local runtime profile validates that owned template requirements occur solely
on supported direct declaration calls before constructing this view. -/
def rewriteLocalRequirements
    (requirements : List LocalRequirementWitness)
    (source : TypedSource) : TypedSource := {
  source with
  nodes := source.nodes.map (rewriteNodeLocalRequirements requirements)
}


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
      value.type? plan = some (runtimeType expected) ∧
        match value with
        | .product left right =>
            match runtimeType expected with
            | .product leftType rightType =>
                left.HasDeepTypeFuel fuel signatures plan state leftType ∧
                  right.HasDeepTypeFuel fuel signatures plan state rightType
            | _ => False
        | .mapping actualKey actualValue entries =>
            match runtimeType expected with
            | .mapping keyType valueType =>
                runtimeType actualKey = keyType ∧
                  runtimeType actualValue = valueType ∧
                  ∀ entry, entry ∈ entries →
                    entry.1.HasDeepTypeFuel fuel signatures plan state keyType ∧
                      entry.2.HasDeepTypeFuel fuel signatures plan state valueType
            | _ => False
        | .constructed instantiation arguments =>
            runtimeType instantiation.resultType = runtimeType expected ∧
              validConstructorInstantiation signatures instantiation = true ∧
              instantiation.payloadTypes.length = arguments.length ∧
              ∀ pair, pair ∈ List.zip instantiation.payloadTypes arguments →
                pair.2.HasDeepTypeFuel fuel signatures plan state pair.1
        | .closure parameters resultType _ _ _ captured _ =>
            runtimeType expected = runtimeType (.function
              (Ty.productMany (parameters.map (·.scheme.body))) resultType) ∧
              ∀ binding, binding ∈ captured →
                ∃ cell, state.read? binding.2 = some cell ∧
                  ∀ capturedValue, cell.value = some capturedValue →
                    capturedValue.HasDeepTypeFuel fuel signatures plan state cell.type
        | .instantiated _ _ principal =>
            match principal.type? plan with
            | some principalType =>
                principal.HasDeepTypeFuel fuel signatures plan state principalType
            | none => False
        | .global key evidence =>
            ∃ specialized, exactSpecialization plan key = .ok specialized ∧
              runtimeType specialized.function.type = runtimeType expected ∧
              validateAuthenticatedRuntimeEvidence signatures key
                specialized.assumptions evidence = .ok ()
        | _ => True

/-- Deep structural typing depends only on the runtime representation of the
expected source type. -/
@[simp] theorem Value.hasDeepTypeFuel_runtimeType
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) (expected : Ty) (value : Value) :
    value.HasDeepTypeFuel fuel signatures plan state (runtimeType expected) ↔
      value.HasDeepTypeFuel fuel signatures plan state expected := by
  cases fuel with
  | zero => simp [Value.HasDeepTypeFuel]
  | succ fuel => simp [Value.HasDeepTypeFuel]

@[simp] theorem Value.hasDeepTypeFuel_comptime
    (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) (expected : Ty) (value : Value) :
    value.HasDeepTypeFuel fuel signatures plan state (.comptime expected) ↔
      value.HasDeepTypeFuel fuel signatures plan state expected := by
  exact (Value.hasDeepTypeFuel_runtimeType fuel signatures plan state
    (.comptime expected) value).symm.trans
      (Value.hasDeepTypeFuel_runtimeType fuel signatures plan state
        expected value)

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
          some (runtimeType (substitution.apply principalType)) ∧
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
      | .global key evidence =>
          validateExecutablePlan plan = .ok () ∧
            ∃ specialized, exactSpecialization plan key = .ok specialized ∧
              validateRuntimeEvidence key specialized.assumptions evidence =
                .ok ()
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

end Solcore.Frontend.SourceTypedRuntime
