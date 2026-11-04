import Solcore.Frontend.Internal.RuntimeValues

/-!
# Deep validation

Source heap typing, deep validation of values and heaps, and static lookup provenance.
-/

section
-- leanmerge: from Solcore.Frontend.SourceRuntimeHeapTyping
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
end

section
-- leanmerge: from Solcore.Frontend.SourceRuntimeDeepValidation
/-!
# Pure deep-safety validation for source values and heaps

The ordinary typed-source boundary validates argument representations and the
outer result type.  This module adds an executable, finite graph check for the
stronger invariant needed at the compiler facade: initialized heap cells and
public values are deeply typed, every captured location is readable, and every
closure/global carries checked-plan code provenance and authenticated runtime
evidence.

The validators below are deliberately `Bool`-valued.  In particular, the
runner never asks Lean to synthesize a classical decision procedure for an
inductive proposition.  A caller-controlled validation budget bounds nested
value/list traversal; returning `true` has an unconditional soundness theorem.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem SourceCompilationPlan

/-- Every location retained by a closure is present in the heap whose cells
are certified separately by `RuntimeState.DeeplySafe`. -/
def CapturesReadable (state : RuntimeState) (captured : Environment) : Prop :=
  ∀ binding, binding ∈ captured → ∃ cell, state.read? binding.2 = some cell

private theorem boolAndTrue {left right : Bool}
    (checked : (left && right) = true) : left = true ∧ right = true := by
  cases left <;> cases right <;> simp_all

/-!
Runtime local-polymorphic calls execute a type-substituted view of the checked
owner source.  A lambda created inside that view therefore does not carry the
byte-for-byte source stored in the plan, even though its graph and every
non-requirement annotation are exactly a substitution instance of it.  The
following finite reconstruction records that provenance without trusting an
arbitrary source supplied by a caller.
-/

private def sourceBinderConstraints? :
    List TypedBinder → List TypedBinder → Option (List Constraint)
  | [], [] => some []
  | left :: leftRest, right :: rightRest => do
      let rest ← sourceBinderConstraints? leftRest rightRest
      pure ({ left := left.scheme.body, right := right.scheme.body } :: rest)
  | _, _ => none

private def sourceNodeConstraints? :
    List Node → List Node → Option (List Constraint)
  | [], [] => some []
  | .expression left :: leftRest, .expression right :: rightRest => do
      let rest ← sourceNodeConstraints? leftRest rightRest
      pure ({ left := left.type, right := right.type } :: rest)
  | .statement left :: leftRest, .statement right :: rightRest => do
      let rest ← sourceNodeConstraints? leftRest rightRest
      pure ({ left := left.type, right := right.type } :: rest)
  | _, _ => none

private def runtimeSourceSubstitution? (checked runtime : TypedSource) :
    Option Substitution := do
  let inputConstraints ← sourceBinderConstraints? checked.inputs runtime.inputs
  let nodeConstraints ← sourceNodeConstraints? checked.nodes runtime.nodes
  match Unification.unify (inputConstraints ++ nodeConstraints) with
  | .ok substitution => some substitution
  | .error _ => none

def eraseRuntimeRequirementIdsExpression
    (node : ExpressionNode) : ExpressionNode :=
  { node with requirements := node.requirements.map fun _ => ⟨0⟩ }

def eraseRuntimeRequirementIdsNode : Node → Node
  | .expression node => .expression (eraseRuntimeRequirementIdsExpression node)
  | .statement node => .statement node

def eraseRuntimeRequirementIdsSource
    (source : TypedSource) : TypedSource :=
  { source with nodes := source.nodes.map eraseRuntimeRequirementIdsNode }

private def deepExactSolvedRequirement?
    (function : CheckedFunction) (id : RequirementId) : Option SolvedRequirement :=
  match function.solvedRequirements.filter fun solved => solved.id == id with
  | [solved] => some solved
  | _ => none

private def substitutionIsClosed (substitution : Substitution) : Bool :=
  substitution.all fun entry => entry.2.freeVariables.isEmpty

/-- One runtime requirement handle is a semantic image of the checked handle:
both ledgers are unique and self-consistent, and the runtime predicate is the
same checked predicate under the reconstructed type substitution. -/
private def runtimeRequirementImage (function : CheckedFunction)
    (substitution : Substitution) (checked runtime : RequirementId) : Bool :=
  match deepExactSolvedRequirement? function checked,
      deepExactSolvedRequirement? function runtime with
  | some checkedSolved, some runtimeSolved =>
      decide (checkedSolved.evidence.goal = checkedSolved.predicate) &&
        decide (runtimeSolved.evidence.goal = runtimeSolved.predicate) &&
        decide (TypedTraitResolution.applySubstitution substitution
          checkedSolved.predicate = runtimeSolved.predicate)
  | _, _ => false

private def runtimeRequirementListImage (function : CheckedFunction)
    (substitution : Substitution) : List RequirementId → List RequirementId → Bool
  | [], [] => true
  | checked :: checkedRest, runtime :: runtimeRest =>
      runtimeRequirementImage function substitution checked runtime &&
        runtimeRequirementListImage function substitution checkedRest runtimeRest
  | _, _ => false

private def runtimeSourceRequirementImage (function : CheckedFunction)
    (substitution : Substitution) : List Node → List Node → Bool
  | [], [] => true
  | .expression checked :: checkedRest,
      .expression runtime :: runtimeRest =>
      runtimeRequirementListImage function substitution checked.requirements
          runtime.requirements &&
        runtimeSourceRequirementImage function substitution checkedRest runtimeRest
  | .statement _ :: checkedRest, .statement _ :: runtimeRest =>
      runtimeSourceRequirementImage function substitution checkedRest runtimeRest
  | _, _ => false

/-- A runtime source is a checked source image when first-order unification of
the corresponding input/node annotations reconstructs a substitution whose
application yields the same graph.  Runtime-local requirement identifiers are
erased for this equality because their authenticated witnesses deliberately
rename template IDs while preserving the checked graph and predicates. -/
def RuntimeSourceImage (runtime : TypedSource) (function : CheckedFunction) : Prop :=
  ∃ substitution,
    runtimeSourceSubstitution? function.typedBody runtime = some substitution ∧
      substitutionIsClosed substitution = true ∧
      eraseRuntimeRequirementIdsSource
          (function.typedBody.applySubstitution substitution) =
        eraseRuntimeRequirementIdsSource runtime ∧
      runtimeSourceRequirementImage function substitution
        function.typedBody.nodes runtime.nodes = true

def runtimeSourceImageCheck (runtime : TypedSource)
    (function : CheckedFunction) : Bool :=
  match runtimeSourceSubstitution? function.typedBody runtime with
  | none => false
  | some substitution =>
      substitutionIsClosed substitution &&
        decide (eraseRuntimeRequirementIdsSource
            (function.typedBody.applySubstitution substitution) =
          eraseRuntimeRequirementIdsSource runtime) &&
        runtimeSourceRequirementImage function substitution
          function.typedBody.nodes runtime.nodes

theorem runtimeSourceImageCheck_sound
    {runtime : TypedSource} {function : CheckedFunction}
    (accepted : runtimeSourceImageCheck runtime function = true) :
    RuntimeSourceImage runtime function := by
  unfold runtimeSourceImageCheck at accepted
  cases recovered : runtimeSourceSubstitution? function.typedBody runtime with
  | none => simp [recovered] at accepted
  | some substitution =>
      rw [recovered] at accepted
      have requirements := (boolAndTrue accepted).2
      have prefixCheck := (boolAndTrue accepted).1
      exact ⟨substitution, recovered, (boolAndTrue prefixCheck).1,
        of_decide_eq_true (boolAndTrue prefixCheck).2, requirements⟩

/-- Finite structural typing which stops at closure-to-heap edges.  The
companion heap invariant certifies the target of every such edge. -/
inductive Value.HasLocalType (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) : Value → Ty → Prop where
  | unit {expected : Ty}
      (outer_type : Value.unit.type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = .unit) :
      Value.unit.HasLocalType signatures plan state expected
  | bool {expected : Ty} (value : Bool)
      (outer_type : (Value.bool value).type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = .bool) :
      (Value.bool value).HasLocalType signatures plan state expected
  | word {expected : Ty} (value : Core.Word)
      (outer_type : (Value.word value).type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = .word) :
      (Value.word value).HasLocalType signatures plan state expected
  | integer {expected : Ty} (value : Int)
      (outer_type : (Value.integer value).type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = .integer) :
      (Value.integer value).HasLocalType signatures plan state expected
  | product {expected leftType rightType : Ty} {left right : Value}
      (outer_type : (Value.product left right).type? plan =
        some (runtimeType expected))
      (expected_type : runtimeType expected = .product leftType rightType)
      (left_typed : left.HasLocalType signatures plan state leftType)
      (right_typed : right.HasLocalType signatures plan state rightType) :
      (Value.product left right).HasLocalType signatures plan state expected
  | proxy {expected inner : Ty}
      (outer_type : (Value.proxy inner).type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = .proxy (runtimeType inner)) :
      (Value.proxy inner).HasLocalType signatures plan state expected
  | constructed {expected : Ty}
      {instantiation : DataConstructorInstantiation} {arguments : List Value}
      (outer_type : (Value.constructed instantiation arguments).type? plan =
        some (runtimeType expected))
      (expected_type : runtimeType expected =
        runtimeType instantiation.resultType)
      (valid : validConstructorInstantiation signatures instantiation = true)
      (length_eq : instantiation.payloadTypes.length = arguments.length)
      (arguments_typed : ∀ pair,
        pair ∈ List.zip instantiation.payloadTypes arguments →
          pair.2.HasLocalType signatures plan state pair.1) :
      (Value.constructed instantiation arguments).HasLocalType signatures plan
        state expected
  | mapping {expected keyType valueType : Ty}
      {entries : List (Value × Value)}
      (outer_type : (Value.mapping keyType valueType entries).type? plan =
        some (runtimeType expected))
      (expected_type : runtimeType expected = .mapping
        (runtimeType keyType) (runtimeType valueType))
      (keys_typed : ∀ entry, entry ∈ entries →
        entry.1.HasLocalType signatures plan state (runtimeType keyType))
      (values_typed : ∀ entry, entry ∈ entries →
        entry.2.HasLocalType signatures plan state (runtimeType valueType)) :
      (Value.mapping keyType valueType entries).HasLocalType signatures plan
        state expected
  | closure {expected : Ty} {parameters : List TypedBinder}
      {resultType : Ty} {body : List StatementId} {source : TypedSource}
      {owner : Key} {captured : Environment}
      {evidence : RuntimeEvidenceEnvironment}
      (outer_type : (Value.closure parameters resultType body source owner
        captured evidence).type? plan = some (runtimeType expected))
      (expected_type : runtimeType expected = runtimeType (.function
        (Ty.productMany (parameters.map (·.scheme.body))) resultType))
      (captures : CapturesReadable state captured) :
      (Value.closure parameters resultType body source owner captured
        evidence).HasLocalType signatures plan state expected
  | instantiated {expected principalType : Ty}
      {substitution : Substitution} {requirements : List LocalRequirementWitness}
      {principal : Value}
      (outer_type : (Value.instantiated substitution requirements principal).type?
        plan = some (runtimeType expected))
      (principal_type : principal.type? plan = some principalType)
      (expected_type : runtimeType expected =
        runtimeType (substitution.apply principalType))
      (principal_typed : principal.HasLocalType signatures plan state
        principalType) :
      (Value.instantiated substitution requirements principal).HasLocalType
        signatures plan state expected
  | global {expected : Ty} {key : Key}
      {evidence : RuntimeEvidenceEnvironment}
      {specialized : SourceSpecialization.SpecializedFunction}
      (outer_type : (Value.global key evidence).type? plan =
        some (runtimeType expected))
      (selected : exactSpecialization plan key = .ok specialized)
      (expected_type : runtimeType expected =
        runtimeType specialized.function.type)
      (authenticated : validateAuthenticatedRuntimeEvidence signatures key
        specialized.assumptions evidence = .ok ()) :
      (Value.global key evidence).HasLocalType signatures plan state expected
  | builtin {expected : Ty} (function : BuiltinFunctionId)
      (outer_type : (Value.builtin function).type? plan =
        some (runtimeType expected))
      (expected_type : runtimeType expected = runtimeType function.type) :
      (Value.builtin function).HasLocalType signatures plan state expected

/-- Exact executable closure-code and dictionary certificate. -/
def ClosureCodeAndEvidenceValid (signatures : ProgramSignatures) (plan : Plan)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (evidence : RuntimeEvidenceEnvironment) : Prop :=
  validateExecutablePlan plan = .ok () ∧
    ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
      RuntimeSourceImage source specialized.function ∧
      validateAuthenticatedRuntimeEvidence signatures owner
        specialized.assumptions evidence = .ok () ∧
      ∃ node, source.lookupExpression? node.id = some node ∧
        node.form = .lambda parameters resultType body ∧
        node.type = .function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType

/-- Exact executable global-code and dictionary certificate. -/
def GlobalCodeAndEvidenceValid (signatures : ProgramSignatures) (plan : Plan)
    (key : Key) (evidence : RuntimeEvidenceEnvironment) : Prop :=
  validateExecutablePlan plan = .ok () ∧
    ∃ specialized, exactSpecialization plan key = .ok specialized ∧
      validateAuthenticatedRuntimeEvidence signatures key
        specialized.assumptions evidence = .ok ()

private def deepCoercionRequirementIds (steps : List CoercionStep) :
    List RequirementId :=
  steps.flatMap (fun step => step.requirements)

private def deepOrdinaryOwnedRequirements?
    (node : ExpressionNode) : Option (List RequirementId) :=
  let coercions := deepCoercionRequirementIds node.coercions
  if node.requirements.length < coercions.length then
    none
  else
    let owned := node.requirements.take
      (node.requirements.length - coercions.length)
    if node.requirements = owned ++ coercions then some owned else none

/-- Authenticate one local-polymorphic witness against both requirement
ledgers and the authoritative trait resolver. -/
private def localRequirementWitnessValid (signatures : ProgramSignatures)
    (function : CheckedFunction) (substitution : Substitution)
    (template : LocalSchemeRequirement) (actual : RequirementId)
    (witness : LocalRequirementWitness) : Bool :=
  match deepExactSolvedRequirement? function template.templateRequirement,
      deepExactSolvedRequirement? function actual with
  | some templateSolved, some actualSolved =>
      let predicate := TypedTraitResolution.applySubstitution substitution
        template.predicate
      decide (witness.templateRequirement = template.templateRequirement) &&
        decide (witness.actualRequirement = actual) &&
        decide (templateSolved.evidence.goal = templateSolved.predicate) &&
        decide (witness.predicate = predicate) &&
        decide (actualSolved.predicate = predicate) &&
        decide (actualSolved.evidence.goal = predicate) &&
        decide (runtimeEvidenceGoal witness.evidence = predicate) &&
        match (TypedTraitResolution.resolve signatures.resolutionRules 32
            predicate).outcome with
        | .success selected => selected == witness.evidence
        | .noSolution | .inconclusive _ => false
  | _, _ => false

private def localRequirementWitnessesValid (signatures : ProgramSignatures)
    (function : CheckedFunction) (substitution : Substitution) :
    List LocalSchemeRequirement → List RequirementId →
      List LocalRequirementWitness → Bool
  | [], [], [] => true
  | template :: templates, actual :: actuals, witness :: witnesses =>
      localRequirementWitnessValid signatures function substitution template
          actual witness &&
        localRequirementWitnessesValid signatures function substitution
          templates actuals witnesses
  | _, _, _ => false

/-- A supplied local-polymorphic occurrence must be reproducible from one
qualified direct-lambda let and one checked local reference in the canonical
owner source.  This rules out forged substitutions, missing/reordered
witnesses, and dictionaries not selected by the whole-program resolver. -/
private def instantiatedLocalOriginValid (signatures : ProgramSignatures)
    (plan : Plan) (substitution : Substitution)
    (requirements : List LocalRequirementWitness)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key) : Bool :=
  substitutionIsClosed substitution &&
    match exactSpecialization plan owner with
    | .error _ => false
    | .ok specialized =>
        source.nodes.any fun candidate =>
          match candidate with
          | .expression _ => false
          | .statement { form := .letDecl binder (some initializer), .. } =>
              !binder.scheme.quantified.isEmpty &&
                match source.lookupExpression? initializer with
                | none => false
                | some lambda =>
                    decide (lambda.form = .lambda parameters resultType body) &&
                      decide (lambda.type = binder.scheme.body) &&
                      source.nodes.any fun referenceCandidate =>
                        match referenceCandidate with
                        | .statement _ => false
                        | .expression reference =>
                            match reference.form with
                            | .reference _ (.local binderId) =>
                                decide (binderId = binder.id) &&
                                  match SourceSpecialization.matchClosedSchemeInstance?
                                      binder.scheme reference.rawType,
                                      deepOrdinaryOwnedRequirements? reference with
                                  | some recovered, some actuals =>
                                      decide (recovered = substitution) &&
                                        localRequirementWitnessesValid signatures
                                          specialized.function substitution
                                          binder.schemeRequirements actuals
                                          requirements
                                  | _, _ => false
                            | _ => false
          | .statement _ => false

/-- Public proposition carried by an instantiated value certificate.  Its
executable witness reconstructs a checked local-reference origin and verifies
the substitution and every local dictionary witness. -/
def InstantiatedLocalEvidenceValid (signatures : ProgramSignatures)
    (plan : Plan) (substitution : Substitution)
    (requirements : List LocalRequirementWitness)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key) : Prop :=
  instantiatedLocalOriginValid signatures plan substitution requirements
    parameters resultType body source owner = true

/-- Finite code provenance and authenticated runtime evidence throughout a
value tree. -/
inductive Value.HasValidCodeAndEvidence (signatures : ProgramSignatures)
    (plan : Plan) : Value → Prop where
  | unit : Value.unit.HasValidCodeAndEvidence signatures plan
  | bool (value : Bool) :
      (Value.bool value).HasValidCodeAndEvidence signatures plan
  | word (value : Core.Word) :
      (Value.word value).HasValidCodeAndEvidence signatures plan
  | integer (value : Int) :
      (Value.integer value).HasValidCodeAndEvidence signatures plan
  | product {left right : Value}
      (left_valid : left.HasValidCodeAndEvidence signatures plan)
      (right_valid : right.HasValidCodeAndEvidence signatures plan) :
      (Value.product left right).HasValidCodeAndEvidence signatures plan
  | proxy (inner : Ty) :
      (Value.proxy inner).HasValidCodeAndEvidence signatures plan
  | constructed {instantiation : DataConstructorInstantiation}
      {arguments : List Value}
      (arguments_valid : ∀ argument, argument ∈ arguments →
        argument.HasValidCodeAndEvidence signatures plan) :
      (Value.constructed instantiation arguments).HasValidCodeAndEvidence
        signatures plan
  | mapping {keyType valueType : Ty} {entries : List (Value × Value)}
      (keys_valid : ∀ entry, entry ∈ entries →
        entry.1.HasValidCodeAndEvidence signatures plan)
      (values_valid : ∀ entry, entry ∈ entries →
        entry.2.HasValidCodeAndEvidence signatures plan) :
      (Value.mapping keyType valueType entries).HasValidCodeAndEvidence
        signatures plan
  | closure {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId} {source : TypedSource} {owner : Key}
      {captured : Environment} {evidence : RuntimeEvidenceEnvironment}
      (valid : ClosureCodeAndEvidenceValid signatures plan parameters
        resultType body source owner evidence) :
      (Value.closure parameters resultType body source owner captured
        evidence).HasValidCodeAndEvidence signatures plan
  | instantiated {substitution : Substitution}
      {requirements : List LocalRequirementWitness}
      {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId} {source : TypedSource} {owner : Key}
      {captured : Environment} {evidence : RuntimeEvidenceEnvironment}
      (principal_valid : (Value.closure parameters resultType body source owner
        captured evidence).HasValidCodeAndEvidence signatures plan)
      (instance_valid : InstantiatedLocalEvidenceValid signatures plan
        substitution requirements parameters resultType body source owner) :
      (Value.instantiated substitution requirements
        (.closure parameters resultType body source owner captured evidence)
          ).HasValidCodeAndEvidence signatures plan
  | global {key : Key} {evidence : RuntimeEvidenceEnvironment}
      (valid : GlobalCodeAndEvidenceValid signatures plan key evidence) :
      (Value.global key evidence).HasValidCodeAndEvidence signatures plan
  | builtin (function : BuiltinFunctionId) :
      (Value.builtin function).HasValidCodeAndEvidence signatures plan

/-- One value is ready to cross the public runtime boundary at its complete
source type. -/
structure Value.DeeplySafe (value : Value) (signatures : ProgramSignatures)
    (plan : Plan) (state : RuntimeState) (expected : Ty) : Prop where
  typed : value.HasLocalType signatures plan state expected
  code_and_evidence : value.HasValidCodeAndEvidence signatures plan

/-- Every initialized cell is deeply safe at its immutable declared type. -/
def RuntimeState.DeeplySafe (state : RuntimeState)
    (signatures : ProgramSignatures) (plan : Plan) : Prop :=
  ∀ cell, cell ∈ state.heap → ∀ value, cell.value = some value →
    value.DeeplySafe signatures plan state cell.type

/-- Execution may append cells and update values, but every pre-existing
location keeps its declared type.  Prefix equality also implies that the
final heap is at least as long as the initial heap. -/
def RuntimeState.TypeLayoutExtends (initial finalState : RuntimeState) : Prop :=
  (finalState.heap.take initial.heap.length).map (·.type) =
    initial.heap.map (·.type)

/-- Pointwise public-input safety. -/
inductive ValuesDeeplySafe (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) : List Value → List Ty → Prop where
  | nil : ValuesDeeplySafe signatures plan state [] []
  | cons {value : Value} {values : List Value} {type : Ty} {types : List Ty}
      (head : value.DeeplySafe signatures plan state type)
      (tail : ValuesDeeplySafe signatures plan state values types) :
      ValuesDeeplySafe signatures plan state (value :: values) (type :: types)

private def exceptUnitOk {ε : Type} : Except ε Unit → Bool
  | .ok () => true
  | .error _ => false

private theorem boolOfNotNotTrue {value : Bool}
    (accepted : ¬ (!value) = true) : value = true := by
  cases value <;> simp_all

/-- Executable captured-location check. -/
def capturesReadable (state : RuntimeState) (captured : Environment) : Bool :=
  captured.all fun binding => (state.read? binding.2).isSome

/-- Executable closure-code/evidence check. -/
def closureCodeAndEvidenceValid (signatures : ProgramSignatures) (plan : Plan)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId) (source : TypedSource) (owner : Key)
    (evidence : RuntimeEvidenceEnvironment) : Bool :=
  exceptUnitOk (validateExecutablePlan plan) &&
    match exactSpecialization plan owner with
    | .error _ => false
    | .ok specialized =>
        runtimeSourceImageCheck source specialized.function &&
        exceptUnitOk (validateAuthenticatedRuntimeEvidence signatures owner
          specialized.assumptions evidence) &&
        source.nodes.any fun candidate =>
          match candidate with
          | .statement _ => false
          | .expression node =>
              decide (source.lookupExpression? node.id = some node) &&
              decide (node.form = .lambda parameters resultType body) &&
              decide (node.type = .function
                (Ty.productMany (parameters.map (·.scheme.body))) resultType)

/-- Executable global-code/evidence check. -/
def globalCodeAndEvidenceValid (signatures : ProgramSignatures) (plan : Plan)
    (key : Key) (evidence : RuntimeEvidenceEnvironment) : Bool :=
  exceptUnitOk (validateExecutablePlan plan) &&
    match exactSpecialization plan key with
    | .error _ => false
    | .ok specialized =>
        exceptUnitOk (validateAuthenticatedRuntimeEvidence signatures key
          specialized.assumptions evidence)

/-- Bounded executable local-typing check.  Recursive value descent consumes
fuel; every element at a given list layer is checked at the resulting smaller
budget, so budget exhaustion rejects instead of trusting an incomplete traversal. -/
def Value.hasLocalTypeFuel : Nat → ProgramSignatures → Plan → RuntimeState →
    Value → Ty → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, signatures, plan, state, value, expected =>
      decide (value.type? plan = some (runtimeType expected)) &&
      match value with
      | .unit => decide (runtimeType expected = .unit)
      | .bool _ => decide (runtimeType expected = .bool)
      | .word _ => decide (runtimeType expected = .word)
      | .integer _ => decide (runtimeType expected = .integer)
      | .product left right =>
          match left.type? plan, right.type? plan with
          | some leftType, some rightType =>
              decide (runtimeType expected = .product leftType rightType) &&
                left.hasLocalTypeFuel fuel signatures plan state leftType &&
                right.hasLocalTypeFuel fuel signatures plan state rightType
          | _, _ => false
      | .proxy inner =>
          decide (runtimeType expected = .proxy (runtimeType inner))
      | .constructed instantiation arguments =>
          decide (runtimeType expected =
              runtimeType instantiation.resultType) &&
            validConstructorInstantiation signatures instantiation &&
            decide (instantiation.payloadTypes.length = arguments.length) &&
            (List.zip instantiation.payloadTypes arguments).all fun pair =>
              pair.2.hasLocalTypeFuel fuel signatures plan state pair.1
      | .mapping keyType valueType entries =>
          decide (runtimeType expected = .mapping
              (runtimeType keyType) (runtimeType valueType)) &&
            entries.all fun entry =>
              entry.1.hasLocalTypeFuel fuel signatures plan state
                  (runtimeType keyType) &&
                entry.2.hasLocalTypeFuel fuel signatures plan state
                  (runtimeType valueType)
      | .closure parameters resultType _ _ _ captured _ =>
          decide (runtimeType expected = runtimeType (.function
              (Ty.productMany (parameters.map (·.scheme.body))) resultType)) &&
            capturesReadable state captured
      | .instantiated substitution _ principal =>
          match principal.type? plan with
          | none => false
          | some principalType =>
              decide (runtimeType expected =
                runtimeType (substitution.apply principalType)) &&
              principal.hasLocalTypeFuel fuel signatures plan state principalType
      | .global key evidence =>
          match exactSpecialization plan key with
          | .error _ => false
          | .ok specialized =>
              decide (runtimeType expected =
                  runtimeType specialized.function.type) &&
                exceptUnitOk (validateAuthenticatedRuntimeEvidence signatures
                  key specialized.assumptions evidence)
      | .builtin function =>
          decide (runtimeType expected = runtimeType function.type)

/-- Bounded executable code-provenance/evidence check. -/
def Value.hasValidCodeAndEvidenceFuel : Nat → ProgramSignatures → Plan →
    Value → Bool
  | 0, _, _, _ => false
  | fuel + 1, signatures, plan, value =>
      match value with
      | .unit | .bool _ | .word _ | .integer _ | .proxy _ | .builtin _ => true
      | .product left right =>
          left.hasValidCodeAndEvidenceFuel fuel signatures plan &&
            right.hasValidCodeAndEvidenceFuel fuel signatures plan
      | .constructed _ arguments =>
          arguments.all fun argument =>
            argument.hasValidCodeAndEvidenceFuel fuel signatures plan
      | .mapping _ _ entries =>
          entries.all fun entry =>
            entry.1.hasValidCodeAndEvidenceFuel fuel signatures plan &&
              entry.2.hasValidCodeAndEvidenceFuel fuel signatures plan
      | .closure parameters resultType body source owner _ evidence =>
          closureCodeAndEvidenceValid signatures plan parameters resultType
            body source owner evidence
      | .instantiated substitution requirements principal =>
          match principal with
          | .closure parameters resultType body source owner _ evidence =>
              closureCodeAndEvidenceValid signatures plan parameters resultType
                  body source owner evidence &&
                instantiatedLocalOriginValid signatures plan substitution
                  requirements parameters resultType body source owner
          | _ => false
      | .global key evidence =>
          globalCodeAndEvidenceValid signatures plan key evidence

/-- Executable combined value check. -/
def Value.isDeeplySafe (fuel : Nat) (signatures : ProgramSignatures)
    (plan : Plan) (state : RuntimeState) (expected : Ty) (value : Value) : Bool :=
  value.hasLocalTypeFuel fuel signatures plan state expected &&
    value.hasValidCodeAndEvidenceFuel fuel signatures plan

/-- Executable whole-heap check. -/
def RuntimeState.isDeeplySafe (fuel : Nat) (signatures : ProgramSignatures)
    (plan : Plan) (state : RuntimeState) : Bool :=
  state.heap.all fun cell =>
    match cell.value with
    | none => true
    | some value => value.isDeeplySafe fuel signatures plan state cell.type

/-- Executable type-layout extension check used at the stateful boundary. -/
def RuntimeState.typeLayoutExtends (initial finalState : RuntimeState) : Bool :=
  decide ((finalState.heap.take initial.heap.length).map (·.type) =
    initial.heap.map (·.type))

/-- Executable pointwise public-input check. -/
def valuesDeeplySafe (fuel : Nat) (signatures : ProgramSignatures) (plan : Plan)
    (state : RuntimeState) : List Value → List Ty → Bool
  | [], [] => true
  | value :: values, type :: types =>
      value.isDeeplySafe fuel signatures plan state type &&
        valuesDeeplySafe fuel signatures plan state values types
  | _, _ => false

private theorem exceptUnitOk_sound {ε : Type} {result : Except ε Unit}
    (checked : exceptUnitOk result = true) : result = .ok () := by
  cases result with
  | error error => simp [exceptUnitOk] at checked
  | ok value => cases value; rfl

theorem capturesReadable_sound
    {state : RuntimeState} {captured : Environment}
    (checked : capturesReadable state captured = true) :
    CapturesReadable state captured := by
  intro binding member
  have readable := List.all_eq_true.mp checked binding member
  exact Option.isSome_iff_exists.mp readable

theorem closureCodeAndEvidenceValid_sound
    {signatures : ProgramSignatures} {plan : Plan}
    {parameters : List TypedBinder} {resultType : Ty}
    {body : List StatementId} {source : TypedSource} {owner : Key}
    {evidence : RuntimeEvidenceEnvironment}
    (checked : closureCodeAndEvidenceValid signatures plan parameters
      resultType body source owner evidence = true) :
    ClosureCodeAndEvidenceValid signatures plan parameters resultType body
      source owner evidence := by
  unfold closureCodeAndEvidenceValid at checked
  have planValid : validateExecutablePlan plan = .ok () :=
    exceptUnitOk_sound (boolAndTrue checked).1
  rw [planValid] at checked
  simp only [exceptUnitOk, Bool.true_and] at checked
  cases selected : exactSpecialization plan owner with
  | error error => simp [selected] at checked
  | ok specialized =>
      simp only [selected] at checked
      have occurrence := (boolAndTrue checked).2
      have prefixCheck := (boolAndTrue checked).1
      have sameSource := runtimeSourceImageCheck_sound
        (boolAndTrue prefixCheck).1
      have authenticated := exceptUnitOk_sound (boolAndTrue prefixCheck).2
      obtain ⟨candidate, candidateMember, candidateValid⟩ :=
        List.any_eq_true.mp occurrence
      cases candidate with
      | statement statement => contradiction
      | expression node =>
          simp only at candidateValid
          have nodeType := of_decide_eq_true (boolAndTrue candidateValid).2
          have prefixCheck := (boolAndTrue candidateValid).1
          have found := of_decide_eq_true (boolAndTrue prefixCheck).1
          have shape := of_decide_eq_true (boolAndTrue prefixCheck).2
          exact ⟨planValid, specialized, selected, sameSource, authenticated,
            node, found, shape, nodeType⟩

theorem globalCodeAndEvidenceValid_sound
    {signatures : ProgramSignatures} {plan : Plan} {key : Key}
    {evidence : RuntimeEvidenceEnvironment}
    (checked : globalCodeAndEvidenceValid signatures plan key evidence = true) :
    GlobalCodeAndEvidenceValid signatures plan key evidence := by
  unfold globalCodeAndEvidenceValid at checked
  have planValid : validateExecutablePlan plan = .ok () :=
    exceptUnitOk_sound (boolAndTrue checked).1
  rw [planValid] at checked
  simp only [exceptUnitOk, Bool.true_and] at checked
  cases selected : exactSpecialization plan key with
  | error error => simp [selected] at checked
  | ok specialized =>
      simp only [selected] at checked
      exact ⟨planValid, specialized, selected, exceptUnitOk_sound checked⟩

theorem Value.hasLocalTypeFuel_sound
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {value : Value} {expected : Ty}
    (checked : value.hasLocalTypeFuel fuel signatures plan state expected = true) :
    value.HasLocalType signatures plan state expected := by
  induction fuel generalizing value expected with
  | zero => simp [Value.hasLocalTypeFuel] at checked
  | succ fuel induction =>
      have outer := (boolAndTrue checked).1
      have inner := (boolAndTrue checked).2
      have outerType := of_decide_eq_true outer
      cases value with
      | unit =>
          exact .unit outerType (of_decide_eq_true inner)
      | bool value =>
          exact .bool value outerType (of_decide_eq_true inner)
      | word value =>
          exact .word value outerType (of_decide_eq_true inner)
      | integer value =>
          exact .integer value outerType (of_decide_eq_true inner)
      | product left right =>
          cases leftTypeEq : left.type? plan with
          | none => simp_all only [Bool.false_eq_true]
          | some leftType =>
              cases rightTypeEq : right.type? plan with
              | none => simp_all only [Bool.false_eq_true]
              | some rightType =>
                  simp only [leftTypeEq, rightTypeEq] at inner
                  have rightChecked := (boolAndTrue inner).2
                  have prefixCheck := (boolAndTrue inner).1
                  exact .product outerType
                    (of_decide_eq_true (boolAndTrue prefixCheck).1)
                    (induction (boolAndTrue prefixCheck).2)
                    (induction rightChecked)
      | proxy innerType =>
          exact .proxy outerType (of_decide_eq_true inner)
      | constructed instantiation arguments =>
          have argumentsChecked := (boolAndTrue inner).2
          have prefix₂ := (boolAndTrue inner).1
          have sameLength := of_decide_eq_true (boolAndTrue prefix₂).2
          have prefix₁ := (boolAndTrue prefix₂).1
          have expectedType := of_decide_eq_true (boolAndTrue prefix₁).1
          have valid := (boolAndTrue prefix₁).2
          apply Value.HasLocalType.constructed outerType expectedType valid
            sameLength
          intro pair member
          exact induction (List.all_eq_true.mp argumentsChecked pair member)
      | mapping keyType valueType entries =>
          have expectedType := of_decide_eq_true (boolAndTrue inner).1
          have entriesChecked := (boolAndTrue inner).2
          apply Value.HasLocalType.mapping outerType expectedType
          · intro entry member
            exact induction (boolAndTrue
              (List.all_eq_true.mp entriesChecked entry member)).1
          · intro entry member
            exact induction (boolAndTrue
              (List.all_eq_true.mp entriesChecked entry member)).2
      | closure parameters resultType body source owner captured evidence =>
          exact .closure outerType
            (of_decide_eq_true (boolAndTrue inner).1)
            (capturesReadable_sound (boolAndTrue inner).2)
      | instantiated substitution requirements principal =>
          cases principalTypeEq : principal.type? plan with
          | none => simp_all only [Bool.false_eq_true]
          | some principalType =>
              simp only [principalTypeEq] at inner
              have expectedType := of_decide_eq_true
                (boolAndTrue inner).1
              exact .instantiated outerType principalTypeEq expectedType
                (induction (boolAndTrue inner).2)
      | global key evidence =>
          cases selected : exactSpecialization plan key with
          | error error => simp_all only [Bool.false_eq_true]
          | ok specialized =>
              simp only [selected] at inner
              exact .global outerType selected
                (of_decide_eq_true (boolAndTrue inner).1)
                (exceptUnitOk_sound (boolAndTrue inner).2)
      | builtin function =>
          exact .builtin function outerType (of_decide_eq_true inner)

theorem Value.hasValidCodeAndEvidenceFuel_sound
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan} {value : Value}
    (checked : value.hasValidCodeAndEvidenceFuel fuel signatures plan = true) :
    value.HasValidCodeAndEvidence signatures plan := by
  induction fuel generalizing value with
  | zero => simp [Value.hasValidCodeAndEvidenceFuel] at checked
  | succ fuel induction =>
      cases value with
      | unit => exact .unit
      | bool value => exact .bool value
      | word value => exact .word value
      | integer value => exact .integer value
      | product left right =>
          exact .product
            (induction (boolAndTrue checked).1)
            (induction (boolAndTrue checked).2)
      | proxy inner => exact .proxy inner
      | constructed instantiation arguments =>
          apply Value.HasValidCodeAndEvidence.constructed
          intro argument member
          exact induction (List.all_eq_true.mp checked argument member)
      | mapping keyType valueType entries =>
          apply Value.HasValidCodeAndEvidence.mapping
          · intro entry member
            exact induction (boolAndTrue
              (List.all_eq_true.mp checked entry member)).1
          · intro entry member
            exact induction (boolAndTrue
              (List.all_eq_true.mp checked entry member)).2
      | closure parameters resultType body source owner captured evidence =>
          exact .closure (closureCodeAndEvidenceValid_sound checked)
      | instantiated substitution requirements principal =>
          cases principal with
          | closure parameters resultType body source owner captured evidence =>
              exact .instantiated (.closure
                (closureCodeAndEvidenceValid_sound (boolAndTrue checked).1))
                (boolAndTrue checked).2
          | unit | bool | word | integer | product | proxy | constructed |
              mapping | instantiated | global | builtin =>
              simp [Value.hasValidCodeAndEvidenceFuel] at checked
      | global key evidence =>
          exact .global (globalCodeAndEvidenceValid_sound checked)
      | builtin function => exact .builtin function

theorem Value.isDeeplySafe_sound
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {expected : Ty} {value : Value}
    (checked : value.isDeeplySafe fuel signatures plan state expected = true) :
    value.DeeplySafe signatures plan state expected := by
  exact ⟨Value.hasLocalTypeFuel_sound (boolAndTrue checked).1,
    Value.hasValidCodeAndEvidenceFuel_sound (boolAndTrue checked).2⟩

theorem RuntimeState.isDeeplySafe_sound
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState}
    (checked : state.isDeeplySafe fuel signatures plan = true) :
    state.DeeplySafe signatures plan := by
  intro cell member value stored
  have cellChecked := List.all_eq_true.mp checked cell member
  simp [stored] at cellChecked
  exact Value.isDeeplySafe_sound cellChecked

theorem RuntimeState.typeLayoutExtends_sound
    {initial finalState : RuntimeState}
    (checked : initial.typeLayoutExtends finalState = true) :
    initial.TypeLayoutExtends finalState := by
  unfold RuntimeState.typeLayoutExtends at checked
  unfold RuntimeState.TypeLayoutExtends
  exact of_decide_eq_true checked

theorem valuesDeeplySafe_sound
    {fuel : Nat} {signatures : ProgramSignatures} {plan : Plan}
    {state : RuntimeState} {values : List Value} {types : List Ty}
    (checked : valuesDeeplySafe fuel signatures plan state values types = true) :
    ValuesDeeplySafe signatures plan state values types := by
  induction values generalizing types with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons type types => simp [valuesDeeplySafe] at checked
  | cons value values induction =>
      cases types with
      | nil => simp [valuesDeeplySafe] at checked
      | cons type types =>
          exact .cons
            (Value.isDeeplySafe_sound (boolAndTrue checked).1)
            (induction (boolAndTrue checked).2)

namespace RuntimeState.DeeplySafe

/-- Read inversion for a whole-heap deep-safety certificate. -/
theorem read_value
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (safe : state.DeeplySafe signatures plan)
    {location : Location} {cell : Cell} {value : Value}
    (found : state.read? location = some cell)
    (stored : cell.value = some value) :
    value.DeeplySafe signatures plan state cell.type := by
  apply safe cell
  · exact List.mem_of_getElem? (by
      simpa [RuntimeState.read?] using found)
  · exact stored

end RuntimeState.DeeplySafe

namespace Value.HasLocalType

/-- Local structural typing includes the exact outer runtime tag. -/
theorem outer
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {value : Value} {expected : Ty}
    (typed : value.HasLocalType signatures plan state expected) :
    value.type? plan = some (runtimeType expected) := by
  cases typed <;> assumption

/-- The finite graph-local invariant unfolds to every requested step index.
Captured cycles are handled by decreasing the observation index while the
whole-heap certificate supplies the target cell's local invariant. -/
theorem hasDeepTypeFuel
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (stateSafe : state.DeeplySafe signatures plan)
    {value : Value} {expected : Ty}
    (typed : value.HasLocalType signatures plan state expected)
    (fuel : Nat) :
    value.HasDeepTypeFuel fuel signatures plan state expected := by
  induction fuel generalizing value expected with
  | zero => trivial
  | succ fuel induction =>
      cases typed with
      | unit outerType expectedType =>
          exact ⟨outerType, trivial⟩
      | bool value outerType expectedType =>
          exact ⟨outerType, trivial⟩
      | word value outerType expectedType =>
          exact ⟨outerType, trivial⟩
      | integer value outerType expectedType =>
          exact ⟨outerType, trivial⟩
      | product outerType expectedType leftTyped rightTyped =>
          refine ⟨outerType, ?_⟩
          rw [expectedType]
          exact ⟨induction leftTyped, induction rightTyped⟩
      | proxy outerType expectedType =>
          exact ⟨outerType, trivial⟩
      | constructed outerType expectedType valid sameLength argumentsTyped =>
          refine ⟨outerType, expectedType.symm, valid, sameLength, ?_⟩
          intro pair member
          exact induction (argumentsTyped pair member)
      | mapping outerType expectedType keysTyped valuesTyped =>
          refine ⟨outerType, ?_⟩
          rw [expectedType]
          refine ⟨rfl, rfl, ?_⟩
          intro entry member
          exact ⟨induction (keysTyped entry member),
            induction (valuesTyped entry member)⟩
      | closure outerType expectedType captures =>
          refine ⟨outerType, expectedType, ?_⟩
          intro binding member
          obtain ⟨cell, found⟩ := captures binding member
          refine ⟨cell, found, ?_⟩
          intro capturedValue stored
          exact induction (stateSafe.read_value found stored).typed
      | @instantiated expected principalType substitution requirements principal
          outerType principalTypeEq expectedType principalTyped =>
          refine ⟨outerType, ?_⟩
          simp only
          rw [principalTypeEq]
          exact induction principalTyped
      | global outerType selected expectedType authenticated =>
          exact ⟨outerType, _, selected, expectedType.symm, authenticated⟩
      | builtin function outerType expectedType =>
          exact ⟨outerType, trivial⟩

/-- Finite local typing plus whole-heap safety gives the existing all-fuel
deep structural type. -/
theorem hasDeepType
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (stateSafe : state.DeeplySafe signatures plan)
    {value : Value} {expected : Ty}
    (typed : value.HasLocalType signatures plan state expected) :
    value.HasDeepType signatures plan state expected := by
  intro fuel
  exact typed.hasDeepTypeFuel stateSafe fuel

end Value.HasLocalType

namespace Value.DeeplySafe

theorem hasDeepType
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (stateSafe : state.DeeplySafe signatures plan)
    {value : Value} {expected : Ty}
    (safe : value.DeeplySafe signatures plan state expected) :
    value.HasDeepType signatures plan state expected :=
  safe.typed.hasDeepType stateSafe

end Value.DeeplySafe

namespace ValuesDeeplySafe

/-- A zipped public-input member inherits its complete finite certificate. -/
theorem zip_member
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    {values : List Value} {types : List Ty}
    (safe : ValuesDeeplySafe signatures plan state values types)
    {pair : Ty × Value} (member : pair ∈ List.zip types values) :
    pair.2.DeeplySafe signatures plan state pair.1 := by
  induction safe with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | tailMember
      · exact head
      · exact induction tailMember

end ValuesDeeplySafe

namespace RuntimeState.DeeplySafe

theorem hasDeepTypes
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (safe : state.DeeplySafe signatures plan) :
    state.HasDeepTypes signatures plan := by
  intro fuel cell member value stored
  exact (safe cell member value stored).hasDeepType safe fuel

theorem hasValidCodeAndEvidence
    {signatures : ProgramSignatures} {plan : Plan} {state : RuntimeState}
    (safe : state.DeeplySafe signatures plan) :
    ∀ cell, cell ∈ state.heap → ∀ value, cell.value = some value →
      value.HasValidCodeAndEvidence signatures plan := by
  intro cell member value stored
  exact (safe cell member value stored).code_and_evidence

end RuntimeState.DeeplySafe

/-- The prepared plan is deterministic.  Keeping this witness as an ordinary
definition lets the `Prop`-valued public certificate expose the plan without
storing computational data in a proof. -/
def preparedDeepExecutablePlan (program : CheckedProgram) (plan : Plan) : Plan :=
  match prepareExecutablePlanEvidence program plan with
  | .ok executablePlan => executablePlan
  | .error _ => plan

/-- Post-execution deep certificate retained by the compiler facade. -/
structure PreparedDeepResult (program : CheckedProgram) (plan : Plan)
    (expected : Ty) (value : Value) (state : RuntimeState) : Prop where
  prepared : prepareExecutablePlanEvidence program plan =
    .ok (preparedDeepExecutablePlan program plan)
  state_safe : state.DeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan)
  value_safe : value.DeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan) state expected

namespace PreparedDeepResult

/-- Compatibility accessor used by clients which name the certified plan. -/
def executablePlan
    {program : CheckedProgram} {plan : Plan} {expected : Ty} {value : Value}
    {state : RuntimeState}
    (_certificate : PreparedDeepResult program plan expected value state) : Plan :=
  preparedDeepExecutablePlan program plan

end PreparedDeepResult

/-- Full pre/post certificate for one normally completing boundary call. -/
structure PreparedDeepExecution (program : CheckedProgram) (plan : Plan)
    (argumentTypes : List Ty) (resultType : Ty) (arguments : List Value)
    (initial : RuntimeState) (value : Value) (finalState : RuntimeState) : Prop where
  prepared : prepareExecutablePlanEvidence program plan =
    .ok (preparedDeepExecutablePlan program plan)
  initial_state_safe : initial.DeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan)
  inputs_safe : ValuesDeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan) initial arguments argumentTypes
  final_state_safe : finalState.DeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan)
  state_layout_extends : initial.TypeLayoutExtends finalState
  value_safe : value.DeeplySafe program.signatures
    (preparedDeepExecutablePlan program plan) finalState resultType

/-- A value has the expected runtime representation in the exact executable
plan deterministically prepared from a caller-supplied specialization plan.
This retains provenance for first-class globals discovered only through a
selected operator or coercion method. -/
def Value.HasPreparedType (program : CheckedProgram) (plan : Plan)
    (value : Value) (expected : Ty) : Prop :=
  ∃ executablePlan,
    prepareExecutablePlanEvidence program plan = .ok executablePlan ∧
      value.type? executablePlan = some (runtimeType expected)

end Solcore.Frontend.SourceTypedRuntime
end

section
-- leanmerge: from Solcore.Frontend.SourceTypedStaticSafetyProperties
/-!
Static lookup provenance for source-typed runtime lambdas.

These lemmas identify the exact checked specialization and occurrence table
from which a lambda node was selected. They intentionally do not infer body
typing from an arbitrary `CheckedFunction` record: that stronger claim needs a
separate source-checker soundness certificate.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceTypedRuntime

open SourceInference TypeSystem SourceCompilationPlan

/-- A successful exact runtime lookup selects a member of the finite plan
whose key is precisely the requested key. -/
theorem exactSpecialization_member_and_key
    (plan : Plan) (key : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (selected : exactSpecialization plan key = .ok specialized) :
    specialized ∈ plan.specializations ∧ specialized.key = key := by
  unfold exactSpecialization at selected
  cases filtered : plan.specializations.filter (fun candidate =>
      decide (candidate.key = key)) with
  | nil =>
      rw [filtered] at selected
      cases selected
  | cons first rest =>
      cases rest with
      | nil =>
          rw [filtered] at selected
          cases selected
          have member : specialized ∈ plan.specializations.filter (fun candidate =>
              decide (candidate.key = key)) := by
            rw [filtered]
            simp
          obtain ⟨inPlan, matching⟩ := List.mem_filter.mp member
          exact ⟨inPlan, of_decide_eq_true matching⟩
      | cons second tail =>
          rw [filtered] at selected
          cases selected

/-- A successful typed expression lookup really returns a node in the
function's heterogeneous occurrence table, at the queried occurrence. -/
theorem lookupExpression_member_and_occurrence
    (source : TypedSource) (id : ExpressionId) (node : ExpressionNode)
    (found : source.lookupExpression? id = some node) :
    Node.expression node ∈ source.nodes ∧
      node.id.occurrence = id.occurrence := by
  unfold TypedSource.lookupExpression? at found
  cases lookup : source.lookupNode? id.occurrence with
  | none =>
      rw [lookup] at found
      cases found
  | some selected =>
      rw [lookup] at found
      cases selected with
      | statement statement => cases found
      | expression expression =>
          cases found
          unfold TypedSource.lookupNode? at lookup
          have member : Node.expression node ∈ source.nodes :=
            List.mem_of_find?_eq_some lookup
          have sameOccurrence :
              decide ((Node.expression node).occurrenceId =
                id.occurrence) = true := by
            exact List.find?_some (p := fun selected : Node =>
              decide (selected.occurrenceId = id.occurrence)) lookup
          exact ⟨member, of_decide_eq_true sameOccurrence⟩

/-- The smallest static lambda-annotation contract needed by the evaluator.
It is deliberately a separate certificate: an arbitrary `CheckedFunction`
record, or the runtime's executable-profile preflight, does not establish it.
The source inference soundness proof should eventually produce this for every
specialization in the canonical plan. -/
def Plan.LambdaAnnotationsAgree (plan : Plan) : Prop :=
  ∀ specialized, specialized ∈ plan.specializations →
    ∀ node, Node.expression node ∈ specialized.function.typedBody.nodes →
      ∀ parameters resultType body,
        node.form = .lambda parameters resultType body →
          node.type = .function
            (Ty.productMany (parameters.map (·.scheme.body))) resultType

/-- A plan-level lambda annotation certificate discharges the node-type
premise used when the typed evaluator creates a closure. -/
theorem exactLambdaNode_hasFunctionType
    (plan : Plan) (owner : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId)
    (annotations : plan.LambdaAnnotationsAgree)
    (selected : exactSpecialization plan owner = .ok specialized)
    (found : specialized.function.typedBody.lookupExpression? id = some node)
    (shape : node.form = .lambda parameters resultType body) :
    node.type = .function
      (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  have inPlan := (exactSpecialization_member_and_key plan owner specialized
    selected).1
  have inSource := (lookupExpression_member_and_occurrence
    specialized.function.typedBody id node found).1
  exact annotations specialized inPlan node inSource parameters resultType
    body shape

/-- The static component of a runtime lambda certificate: its selected owner
and annotated function type come from one node in that checked function's
source table. The annotation equality is an explicit premise, not a theorem
of arbitrary, constructible checked IR. -/
theorem checkedLambdaNode_provenance
    (plan : Plan) (owner : Key)
    (specialized : SourceSpecialization.SpecializedFunction)
    (id : ExpressionId) (node : ExpressionNode)
    (parameters : List TypedBinder) (resultType : Ty)
    (body : List StatementId)
    (selected : exactSpecialization plan owner = .ok specialized)
    (found : specialized.function.typedBody.lookupExpression? id = some node)
    (shape : node.form = .lambda parameters resultType body)
    (annotation : node.type = .function
      (Ty.productMany (parameters.map (·.scheme.body))) resultType) :
    specialized ∈ plan.specializations ∧
      specialized.key = owner ∧
      Node.expression node ∈ specialized.function.typedBody.nodes ∧
      node.id.occurrence = id.occurrence ∧
      node.form = .lambda parameters resultType body ∧
      node.type = .function
        (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  obtain ⟨inPlan, matchingKey⟩ :=
    exactSpecialization_member_and_key plan owner specialized selected
  obtain ⟨inSource, matchingOccurrence⟩ :=
    lookupExpression_member_and_occurrence specialized.function.typedBody
      id node found
  exact ⟨inPlan, matchingKey, inSource, matchingOccurrence, shape,
    annotation⟩

/-- A runtime closure's code-provenance invariant yields a concrete checked
lambda node in the selected specialization's source table, including its
annotated function type. This still does not certify the lambda *body's*
typing derivation. -/
theorem closure_hasPlanCode_checkedLambdaNode
    (plan : Plan) (owner : Key) (source : TypedSource)
    (environment : Environment) (parameters : List TypedBinder)
    (evidence : RuntimeEvidenceEnvironment)
    (resultType : Ty) (body : List StatementId)
    (code : (Value.closure parameters resultType body source owner
      environment evidence).HasPlanCode plan) :
    ∃ (specialized : SourceSpecialization.SpecializedFunction)
      (id : ExpressionId) (node : ExpressionNode),
      validateExecutablePlan plan = .ok () ∧
      exactSpecialization plan owner = .ok specialized ∧
      specialized.function.typedBody = source ∧
      specialized ∈ plan.specializations ∧
      specialized.key = owner ∧
      Node.expression node ∈ source.nodes ∧
      node.id.occurrence = id.occurrence ∧
      node.form = .lambda parameters resultType body ∧
      node.type = .function
        (Ty.productMany (parameters.map (·.scheme.body))) resultType := by
  have first := code 1
  change validateExecutablePlan plan = .ok () ∧
    ∃ specialized, exactSpecialization plan owner = .ok specialized ∧
      specialized.function.typedBody = source ∧
      ∃ id node, source.lookupExpression? id = some node ∧
        node.form = .lambda parameters resultType body ∧
        node.type = .function
          (Ty.productMany (parameters.map (·.scheme.body))) resultType at first
  obtain ⟨validated, specialized, selected, sameSource,
    id, node, found, shape, annotation⟩ := first
  have foundInSpecialization :
      specialized.function.typedBody.lookupExpression? id = some node := by
    rw [sameSource]
    exact found
  obtain ⟨inPlan, matchingKey, inSpecialization, matchingOccurrence,
    _, _⟩ := checkedLambdaNode_provenance plan owner specialized id node
      parameters resultType body selected foundInSpecialization shape annotation
  refine ⟨specialized, id, node, validated, selected, sameSource, inPlan,
    matchingKey, ?_, matchingOccurrence, shape, annotation⟩
  simpa [sameSource] using inSpecialization

end Solcore.Frontend.SourceTypedRuntime
end
