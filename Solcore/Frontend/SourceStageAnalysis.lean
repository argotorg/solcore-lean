import Solcore.Frontend.SourceInference.Types
import Solcore.SourceSemantics.Staging.Classification

/-!
Scope-aware source staging analysis.

The result is a sidecar over occurrence-addressed typed source.  It deliberately
does not rewrite the typed IR: later consumers can consult the exact stage of an
expression or binder while retaining the source graph and all stable identities.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStageAnalysis

open SourceInference TypeSystem

/-- Whether a source value is known at staged evaluation time, known to depend
on a runtime input, or must be decided by a later staged evaluator. -/
inductive Stage where
  | comptime
  | runtime
  | deferred
  deriving Repr, BEq, DecidableEq

namespace Stage

/-- Eager source-stage join.  Runtime dependence dominates; otherwise an
entirely compile-time collection remains compile-time, and every mixed or
unsupported collection is deferred.  The empty product is compile-time. -/
def join (stages : List Stage) : Stage :=
  if stages.any fun stage => stage == .runtime then
    .runtime
  else if stages.all fun stage => stage == .comptime then
    .comptime
  else
    .deferred

/-- Interpret the executable classifier's three-point result in the
independent declarative staging language. -/
def toSemantic : Stage → SourceSemantics.Staging.Stage
  | .comptime => .comptime
  | .runtime => .runtime
  | .deferred => .deferred

end Stage

/-- The stage assigned to one expression occurrence. -/
structure ExpressionStage where
  expression : ExpressionId
  stage : Stage
  deriving Repr, BEq, DecidableEq

/-- The stage assigned when one stable local binder enters scope. -/
structure BinderStage where
  binder : Resolved.LocalId
  stage : Stage
  deriving Repr, BEq, DecidableEq

/-- Complete stage sidecar for one checked function.  Entries are retained in
root/child encounter order. -/
structure Analysis where
  expressions : List ExpressionStage
  binders : List BinderStage
  deriving Repr, BEq, DecidableEq

namespace Analysis

/-- Look up the unique classified expression occurrence. -/
def expressionStage? (analysis : Analysis) (expression : ExpressionId) :
    Option Stage :=
  (analysis.expressions.find? fun entry =>
    decide (entry.expression = expression)).map (·.stage)

/-- Look up the stage with which a stable local entered its lexical scope. -/
def binderStage? (analysis : Analysis) (binder : Resolved.LocalId) :
    Option Stage :=
  (analysis.binders.find? fun entry =>
    decide (entry.binder = binder)).map (·.stage)

end Analysis

/-- Structural failures make malformed or ambiguous source graphs explicit
instead of allowing first-match node lookup or scope guessing to affect the
classification. -/
inductive Error where
  | sourceOwnerMismatch
      (expected actual : Resolved.DeclarationId)
  | nodeOwnerMismatch
      (expected : Resolved.DeclarationId) (actual : OccurrenceId)
  | binderOwnerMismatch
      (expected : Resolved.DeclarationId) (actual : Resolved.LocalId)
  | duplicateOccurrence (occurrence : OccurrenceId)
  | duplicateBinder (binder : Resolved.LocalId)
  | missingNode (occurrence : OccurrenceId)
  | expectedExpressionNode (occurrence : OccurrenceId)
  | expectedStatementNode (occurrence : OccurrenceId)
  | unknownLocal
      (expression : ExpressionId) (binder : Resolved.LocalId)
  | cycle (occurrence : OccurrenceId)
  | depthLimit (occurrence : OccurrenceId)
  | duplicateTraversal (occurrence : OccurrenceId)
  | conflictingExpressionStage
      (expression : ExpressionId) (first second : Stage)
  | unreachableNode (occurrence : OccurrenceId)
  deriving Repr, DecidableEq

/-- Proof-facing lexical table.  The soundness proof follows the analyzer's
actual scope transitions; exposing this alias changes no runtime behavior. -/
abbrev Environment := List BinderStage

/-- Types whose values exist only at staged evaluation time in the current
source language.  `comptime<T>` is structural; the arbitrary-precision
`Integer` builtin is staged even without an explicit marker. -/
def typeIsComptimeOnly : Ty → Bool
  | .constructor (.builtin .integer)
  | .comptime _ => true
  | _ => false

/-- The local, executable classification rule for a direct declaration call.
Keeping it named makes the analyzer's call-site contract independently
checkable and connects it to the declarative rule below. -/
def directCallStage (node : ExpressionNode)
    (instantiation : DeclarationInstantiation)
    (argumentStages : List Stage) : Stage :=
  let resultIsComptimeOnly :=
    node.coercions.isEmpty && typeIsComptimeOnly node.type
  if (instantiation.returnComptime || resultIsComptimeOnly) &&
      argumentStages.all fun argument => argument == .comptime then
    .comptime
  else
    .deferred

/-! The following executable helpers are public only through `Detail`, for
the independent soundness proof.  Keeping them in one proof-facing namespace
discourages callers from depending on traversal internals. -/
namespace Detail

/-- Proof-facing traversal state.  Its fields permit the independent staging
soundness proof to state and preserve invariants through recursive calls. -/
structure Traversal where
  active : List OccurrenceId := []
  visited : List OccurrenceId := []
  expressions : List ExpressionStage := []
  binders : List BinderStage := []
  /-- Any binder written anywhere in the body is conservatively deferred.
  This keeps branch- and loop-local mutation from being mistaken for an
  immutable compile-time value by later consumers. -/
  mutableBinders : List Resolved.LocalId := []

def lookupEnvironment? (environment : Environment)
    (binder : Resolved.LocalId) : Option Stage :=
  (environment.find? fun entry => decide (entry.binder = binder)).map (·.stage)

def enterOccurrence (state : Traversal) (occurrence : OccurrenceId) :
    Except Error Traversal :=
  if state.active.any fun active => decide (active = occurrence) then
    .error (.cycle occurrence)
  else
    .ok { state with active := occurrence :: state.active }

def leaveOccurrence (state : Traversal) (occurrence : OccurrenceId) :
    Except Error Traversal :=
  if state.visited.any fun visited => decide (visited = occurrence) then
    .error (.duplicateTraversal occurrence)
  else
    .ok {
      state with
      active := state.active.filter fun active => decide (active != occurrence)
      visited := state.visited ++ [occurrence]
    }

def recordExpressionStage (state : Traversal)
    (expression : ExpressionId) (stage : Stage) : Except Error Traversal :=
  match state.expressions.find? fun entry =>
      decide (entry.expression = expression) with
  | none => .ok {
      state with
      expressions := state.expressions ++ [{ expression, stage }]
    }
  | some previous =>
      if previous.stage = stage then
        .error (.duplicateTraversal expression.occurrence)
      else
        .error (.conflictingExpressionStage expression previous.stage stage)

def registerBinder (owner : Resolved.DeclarationId)
    (environment : Environment) (state : Traversal)
    (binder : Resolved.LocalId) (stage : Stage) :
    Except Error (Environment × Traversal) := do
  if binder.owner != owner then
    throw (.binderOwnerMismatch owner binder)
  if state.binders.any fun entry => decide (entry.binder = binder) then
    throw (.duplicateBinder binder)
  let stage := if state.mutableBinders.contains binder then .deferred else stage
  let entry : BinderStage := { binder, stage }
  pure (entry :: environment, {
    state with binders := state.binders ++ [entry]
  })

def registerTypedBinders (owner : Resolved.DeclarationId)
    (forceComptime : Bool) : List TypedBinder → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => .ok (environment, state)
  | binder :: rest, environment, state => do
      let stage := if forceComptime || binder.comptime ||
          typeIsComptimeOnly binder.scheme.body then
          Stage.comptime
        else
          Stage.runtime
      let (environment, state) ←
        registerBinder owner environment state binder.id stage
      registerTypedBinders owner forceComptime rest environment state

def validateNodeTable (owner : Resolved.DeclarationId) :
    List OccurrenceId → List Node → Except Error Unit
  | _, [] => .ok ()
  | seen, node :: rest => do
      let occurrence := node.occurrenceId
      if occurrence.owner != owner then
        throw (.nodeOwnerMismatch owner occurrence)
      if seen.any fun prior => decide (prior = occurrence) then
        throw (.duplicateOccurrence occurrence)
      validateNodeTable owner (occurrence :: seen) rest

def validateOccurrenceOwner (source : TypedSource)
    (occurrence : OccurrenceId) : Except Error Unit :=
  if occurrence.owner = source.owner then
    .ok ()
  else
    .error (.nodeOwnerMismatch source.owner occurrence)

def lookupExpression (source : TypedSource) (id : ExpressionId) :
    Except Error ExpressionNode := do
  validateOccurrenceOwner source id.occurrence
  match source.lookupNode? id.occurrence with
  | none => throw (.missingNode id.occurrence)
  | some (.statement _) => throw (.expectedExpressionNode id.occurrence)
  | some (.expression node) => pure node

def lookupStatement (source : TypedSource) (id : StatementId) :
    Except Error StatementNode := do
  validateOccurrenceOwner source id.occurrence
  match source.lookupNode? id.occurrence with
  | none => throw (.missingNode id.occurrence)
  | some (.expression _) => throw (.expectedStatementNode id.occurrence)
  | some (.statement node) => pure node

def analyzeExpressionListWith
    (analyze : Traversal → ExpressionId →
      Except Error (Stage × Traversal)) :
    List ExpressionId → Traversal → Except Error (List Stage × Traversal)
  | [], state => .ok ([], state)
  | expression :: rest, state => do
      let (stage, state) ← analyze state expression
      let (stages, state) ← analyzeExpressionListWith analyze rest state
      pure (stage :: stages, state)

def analyzeStatementListWith
    (analyze : Environment → Traversal → StatementId →
      Except Error (Environment × Traversal)) :
    List StatementId → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => .ok (environment, state)
  | statement :: rest, environment, state => do
      let (environment, state) ← analyze environment state statement
      analyzeStatementListWith analyze rest environment state

def bindersInPatternInstruction :
    MatchPatternInstruction → List TypedBinder
  | .binder binder => [binder]
  | _ => []

def bindersInPatternResolution :
    MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions
  | .tuple instructions => instructions.flatMap bindersInPatternInstruction
  | _ => []

def registerPatternBinders (owner : Resolved.DeclarationId)
    (stage : Stage) : List TypedBinder → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => pure (environment, state)
  | binder :: binders, environment, state => do
      let (environment, state) ←
        registerBinder owner environment state binder.id stage
      registerPatternBinders owner stage binders environment state

def mutableBindersInForItem : ForItemForm → List Resolved.LocalId
  | .assignValue assignment _ _
  | .assignBitNot assignment => [assignment.target.root]
  | .letDecl _ _
  | .expression _ => []

def mutableBindersInNode : Node → List Resolved.LocalId
  | .statement { form := .assignValue assignment _ _, .. }
  | .statement { form := .assignBitNot assignment, .. } =>
      [assignment.target.root]
  | .statement { form := .forLoop initializer _ post _, .. } =>
      (initializer ++ post).flatMap mutableBindersInForItem
  | _ => []

/-- Evaluate the index occurrences of one place in projection order.  The
helper exposes the same fold used by assignment analysis to the soundness
proof. -/
def analyzePlaceProjectionsWith
    (analyzeExpression : Traversal → ExpressionId →
      Except Error (Stage × Traversal)) :
    List PlaceProjection → Traversal → Except Error Traversal
  | [], state => pure state
  | .member _ _ :: rest, state =>
      analyzePlaceProjectionsWith analyzeExpression rest state
  | .index key :: rest, state => do
      let (_, state) ← analyzeExpression state key
      analyzePlaceProjectionsWith analyzeExpression rest state

/-- Source-ordered match-arm traversal, factored out so stage soundness can
induct on the arm list without changing the classifier's execution. -/
def analyzeMatchCasesWith (owner : Resolved.DeclarationId)
    (scrutineeStage : Stage)
    (analyzeStatements : List StatementId → Environment → Traversal →
      Except Error (Environment × Traversal)) :
    List TypedMatchCase → Environment → Traversal → Except Error Traversal
  | [], _, state => pure state
  | arm :: arms, environment, state => do
      let (armEnvironment, state) ← registerPatternBinders owner scrutineeStage
        (bindersInPatternResolution arm.pattern.resolution) environment state
      let (_, state) ← analyzeStatements arm.body armEnvironment state
      analyzeMatchCasesWith owner scrutineeStage analyzeStatements arms
        environment state

/-- Analyze an optional branch body while discarding its branch-local scope. -/
def analyzeOptionalStatementsWith
    (analyzeStatement : Environment → Traversal → StatementId →
      Except Error (Environment × Traversal))
    (body : Option (List StatementId)) (environment : Environment)
    (state : Traversal) : Except Error Traversal :=
  match body with
  | none => pure state
  | some body => do
      let (_, state) ← analyzeStatementListWith analyzeStatement body
        environment state
      pure state

/-- Source-ordered `for` header traversal, factored out so stage soundness can
induct on the item list without changing the classifier's execution. -/
def analyzeForItemWith (source : TypedSource)
    (analyzeExpression : Environment → Traversal → ExpressionId →
      Except Error (Stage × Traversal))
    (item : ForItemForm) (environment : Environment) (state : Traversal) :
    Except Error (Environment × Traversal) :=
  let analyzeItemExpression := analyzeExpression environment
  match item with
  | .letDecl binder initializer => do
      let (stage, state) ← match initializer with
        | none => pure (.deferred, state)
        | some value => analyzeItemExpression state value
      registerBinder source.owner environment state binder.id stage
  | .expression value => do
      let (_, state) ← analyzeItemExpression state value
      pure (environment, state)
  | .assignValue assignment _ value => do
      let state ← analyzePlaceProjectionsWith analyzeItemExpression
        assignment.target.projections state
      let (_, state) ← analyzeItemExpression state value
      pure (environment, state)
  | .assignBitNot assignment => do
      let state ← analyzePlaceProjectionsWith analyzeItemExpression
        assignment.target.projections state
      pure (environment, state)

/-- Iterate the proof-facing one-item traversal in source order. -/
def analyzeForItemsWith (source : TypedSource)
    (analyzeExpression : Environment → Traversal → ExpressionId →
      Except Error (Stage × Traversal)) :
    List ForItemForm → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => pure (environment, state)
  | item :: rest, environment, state => do
      let (environment, state) ← analyzeForItemWith source analyzeExpression item
        environment state
      analyzeForItemsWith source analyzeExpression rest environment state

/-- The expression-form decision, separated from occurrence bookkeeping for
the proof that every successful decision satisfies declarative staging. -/
def analyzeExpressionFormWith (source : TypedSource) (expression : ExpressionId)
    (node : ExpressionNode)
    (environment : Environment) (state : Traversal)
    (analyzeExpression : Traversal → ExpressionId → Except Error (Stage × Traversal))
    (analyzeStatement : Environment → Traversal → StatementId →
      Except Error (Environment × Traversal)) :
    Except Error (Stage × Traversal) :=
  match node.form with
  | .literal _
  | .integerLiteral _ _ =>
      pure (.comptime, state)
  | .reference _ (.builtinBoolean _) =>
      pure (.comptime, state)
  | .reference _ (.local binder) =>
      if binder.owner != source.owner then
        throw (.binderOwnerMismatch source.owner binder)
      else
        match lookupEnvironment? environment binder with
        | some stage => pure (stage, state)
        | none => throw (.unknownLocal expression binder)
  | .reference _ (.declaration _)
  | .reference _ (.builtinFunction _) =>
      pure (.deferred, state)
  | .group inner
  | .unary _ inner =>
      analyzeExpression state inner
  | .tuple elements => do
      let (stages, state) ←
        analyzeExpressionListWith analyzeExpression elements state
      pure (Stage.join stages, state)
  | .binary left _ right => do
      let (leftStage, state) ← analyzeExpression state left
      let (rightStage, state) ← analyzeExpression state right
      pure (Stage.join [leftStage, rightStage], state)
  | .conditional condition thenBranch elseBranch => do
      let (conditionStage, state) ← analyzeExpression state condition
      let (thenStage, state) ← analyzeExpression state thenBranch
      let (elseStage, state) ← analyzeExpression state elseBranch
      pure (Stage.join [conditionStage, thenStage, elseStage], state)
  | .lambda parameters _ body => do
      let (lambdaEnvironment, state) ←
        registerTypedBinders source.owner false parameters environment state
      let (_, state) ← analyzeStatementListWith analyzeStatement body
        lambdaEnvironment state
      pure (.deferred, state)
  | .call callee arguments resolution => do
      let (_, state) ← analyzeExpression state callee
      let (argumentStages, state) ←
        analyzeExpressionListWith analyzeExpression arguments state
      let stage := match resolution with
        | .declaration instantiation =>
            directCallStage node instantiation argumentStages
        | .indirect _
        | .builtinFunction _ => Stage.deferred
      pure (stage, state)
  | .constructor _ arguments => do
      let (_, state) ←
        analyzeExpressionListWith analyzeExpression arguments state
      pure (.deferred, state)
  | .member base _ _ => do
      let (_, state) ← analyzeExpression state base
      pure (.deferred, state)
  | .proxy _ =>
      pure (.deferred, state)
  | .index base index => do
      let (_, state) ← analyzeExpression state base
      let (_, state) ← analyzeExpression state index
      pure (.deferred, state)

/-- The statement-form decision, separated from occurrence bookkeeping for
the proof that successful lexical transitions satisfy declarative staging. -/
def analyzeStatementFormWith (source : TypedSource) (node : StatementNode)
    (environment : Environment) (state : Traversal)
    (analyzeExpression : Environment → Traversal → ExpressionId →
      Except Error (Stage × Traversal))
    (analyzeStatement : Environment → Traversal → StatementId →
      Except Error (Environment × Traversal)) :
    Except Error (Environment × Traversal) :=
  let analyzeItemExpression := analyzeExpression environment
  match node.form with
  | .letDecl binder initializer => do
      let (stage, state) ← match initializer with
        | none => pure (Stage.deferred, state)
        | some initializer => analyzeItemExpression state initializer
      registerBinder source.owner environment state binder.id stage
  | .returnStmt value => do
      let state ← match value with
        | none => pure state
        | some value => (analyzeItemExpression state value).map (·.2)
      pure (environment, state)
  | .expression expression _ => do
      let (_, state) ← analyzeItemExpression state expression
      pure (environment, state)
  | .assignValue assignment _ value => do
      let state ← analyzePlaceProjectionsWith analyzeItemExpression
        assignment.target.projections state
      let (_, state) ← analyzeItemExpression state value
      pure (environment, state)
  | .assignBitNot assignment => do
      let state ← analyzePlaceProjectionsWith analyzeItemExpression
        assignment.target.projections state
      pure (environment, state)
  | .ifThen condition thenBody elseBody => do
      let (_, state) ← analyzeItemExpression state condition
      let (_, state) ← analyzeStatementListWith analyzeStatement thenBody
        environment state
      let state ← analyzeOptionalStatementsWith analyzeStatement elseBody
        environment state
      pure (environment, state)
  | .block body => do
      let (_, state) ← analyzeStatementListWith analyzeStatement body
        environment state
      pure (environment, state)
  | .matchWith resolution => do
      let (scrutineeStage, state) ←
        analyzeItemExpression state resolution.scrutinee
      let (_, state) ← registerBinder source.owner environment state
        resolution.hiddenScrutinee scrutineeStage
      let state ← analyzeMatchCasesWith source.owner scrutineeStage
        (analyzeStatementListWith analyzeStatement) resolution.cases
        environment state
      let state ← analyzeOptionalStatementsWith analyzeStatement
        resolution.defaultBody environment state
      pure (environment, state)
  | .forLoop initializer condition post body => do
      let (loopEnvironment, state) ← analyzeForItemsWith source
        analyzeExpression initializer environment state
      let (_, state) ← analyzeExpression loopEnvironment state condition
      let (_, state) ← analyzeStatementListWith analyzeStatement body
        loopEnvironment state
      let (_, state) ← analyzeForItemsWith source analyzeExpression post
        loopEnvironment state
      pure (environment, state)
  | .whileLoop condition body => do
      let (_, state) ← analyzeItemExpression state condition
      let (_, state) ← analyzeStatementListWith analyzeStatement body
        environment state
      pure (environment, state)
  | .breakStmt
  | .continueStmt => pure (environment, state)

mutual

  def analyzeExpressionFuel (source : TypedSource) :
      Nat → Environment → Traversal → ExpressionId →
        Except Error (Stage × Traversal)
    | 0, _, _, expression => .error (.depthLimit expression.occurrence)
    | fuel + 1, environment, state, expression => do
        let state ← enterOccurrence state expression.occurrence
        let node ← lookupExpression source expression
        let recurse := analyzeExpressionFuel source fuel environment
        let (stage, state) ← analyzeExpressionFormWith source expression node
          environment state recurse (analyzeStatementFuel source fuel)
        let state ← recordExpressionStage state expression stage
        let state ← leaveOccurrence state expression.occurrence
        pure (stage, state)

  def analyzeStatementFuel (source : TypedSource) :
      Nat → Environment → Traversal → StatementId →
        Except Error (Environment × Traversal)
    | 0, _, _, statement => .error (.depthLimit statement.occurrence)
    | fuel + 1, environment, state, statement => do
        let state ← enterOccurrence state statement.occurrence
        let node ← lookupStatement source statement
        let (environment, state) ← analyzeStatementFormWith source node
          environment state (analyzeExpressionFuel source fuel)
          (analyzeStatementFuel source fuel)
        let state ← leaveOccurrence state statement.occurrence
        pure (environment, state)

end

def analyzeRoots (source : TypedSource) (fuel : Nat) :
    List NodeId → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => .ok (environment, state)
  | .expression expression :: rest, environment, state => do
      let (_, state) ← analyzeExpressionFuel source fuel environment state expression
      analyzeRoots source fuel rest environment state
  | .statement statement :: rest, environment, state => do
      let (environment, state) ←
        analyzeStatementFuel source fuel environment state statement
      analyzeRoots source fuel rest environment state

def firstUnvisited? (state : Traversal) : List Node → Option OccurrenceId
  | [] => none
  | node :: rest =>
      if state.visited.any fun visited => decide (visited = node.occurrenceId) then
        firstUnvisited? state rest
      else
        some node.occurrenceId

end Detail

open Detail

/-- Classify every reachable expression and lexical binder in a checked
function.  The traversal follows roots and lexical statement order rather than
the storage order of the heterogeneous node table. -/
def analyzeFunction (function : CheckedFunction) : Except Error Analysis := do
  let source := function.typedBody
  if source.owner != function.declaration then
    throw (.sourceOwnerMismatch function.declaration source.owner)
  validateNodeTable source.owner [] source.nodes
  let resultIsComptimeOnly := typeIsComptimeOnly function.inferredBodyType
  let initial : Traversal := {
    mutableBinders := source.nodes.flatMap mutableBindersInNode
  }
  let (environment, state) ← registerTypedBinders source.owner
    (function.returnComptime || resultIsComptimeOnly) source.inputs [] initial
  let (_, state) ← analyzeRoots source (source.nodes.length + 1)
    source.roots environment state
  match firstUnvisited? state source.nodes with
  | some occurrence => throw (.unreachableNode occurrence)
  | none => pure {
      expressions := state.expressions
      binders := state.binders
    }

end Solcore.Frontend.SourceStageAnalysis

/-!
## Consolidated module: `Solcore.Frontend.SourceStageAnalysisProperties`
-/

/-! Algebraic laws for aggregation of source staging classifications. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStageAnalysis.Stage

open Solcore.Frontend.SourceStageAnalysis

private theorem comptime_beq_runtime :
    (Stage.comptime == Stage.runtime) = false := rfl

private theorem runtime_beq_runtime :
    (Stage.runtime == Stage.runtime) = true := rfl

private theorem deferred_beq_runtime :
    (Stage.deferred == Stage.runtime) = false := rfl

private theorem comptime_beq_comptime :
    (Stage.comptime == Stage.comptime) = true := rfl

private theorem runtime_beq_comptime :
    (Stage.runtime == Stage.comptime) = false := rfl

private theorem deferred_beq_comptime :
    (Stage.deferred == Stage.comptime) = false := rfl

private theorem any_runtime_true_iff (stages : List Stage) :
    stages.any (fun stage => stage == .runtime) = true ↔
      .runtime ∈ stages := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨stage, member, equal⟩
    cases stage with
    | comptime =>
        simp only [comptime_beq_runtime, Bool.false_eq_true] at equal
    | runtime => exact member
    | deferred =>
        simp only [deferred_beq_runtime, Bool.false_eq_true] at equal
  · intro member
    exact ⟨.runtime, member, runtime_beq_runtime⟩

private theorem all_comptime_true_iff (stages : List Stage) :
    stages.all (fun stage => stage == .comptime) = true ↔
      ∀ stage ∈ stages, stage = .comptime := by
  rw [List.all_eq_true]
  constructor
  · intro all stage member
    have equal := all stage member
    cases stage with
    | comptime => rfl
    | runtime =>
        simp only [runtime_beq_comptime, Bool.false_eq_true] at equal
    | deferred =>
        simp only [deferred_beq_comptime, Bool.false_eq_true] at equal
  · intro all stage member
    rw [all stage member]
    exact comptime_beq_comptime

/-- The empty collection has no runtime dependency. -/
@[simp] theorem join_nil : join [] = .comptime := by
  rfl

/-- Aggregating exactly one stage returns that stage. -/
@[simp] theorem join_singleton (stage : Stage) : join [stage] = stage := by
  cases stage <;> rfl

/-- A runtime occurrence dominates every other stage in the collection. -/
theorem join_eq_runtime_of_mem {stages : List Stage}
    (member : .runtime ∈ stages) :
    join stages = .runtime := by
  have present := any_runtime_true_iff stages |>.mpr member
  simp only [join, present, if_true]

/-- A collection containing only compile-time stages stays compile-time. -/
theorem join_eq_comptime_of_forall {stages : List Stage}
    (all : ∀ stage ∈ stages, stage = .comptime) :
    join stages = .comptime := by
  have onlyComptime := all_comptime_true_iff stages |>.mpr all
  have noRuntime : stages.any (fun stage => stage == .runtime) = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    have member := any_runtime_true_iff stages |>.mp present
    have equal := all .runtime member
    cases equal
  simp only [join, noRuntime, onlyComptime, Bool.false_eq_true, if_false]
  simp

/-- Deferred is precisely a non-runtime collection with a deferred member. -/
theorem join_eq_deferred_iff (stages : List Stage) :
    join stages = .deferred ↔
      .runtime ∉ stages ∧ .deferred ∈ stages := by
  constructor
  · intro joined
    constructor
    · intro member
      have runtime := join_eq_runtime_of_mem member
      rw [joined] at runtime
      contradiction
    · by_cases present : .deferred ∈ stages
      · exact present
      · have all : ∀ stage ∈ stages, stage = .comptime := by
          intro stage member
          cases stage with
          | comptime => rfl
          | runtime =>
              have runtimeJoined := join_eq_runtime_of_mem member
              rw [joined] at runtimeJoined
              contradiction
          | deferred => exact False.elim (present member)
        have comptime := join_eq_comptime_of_forall all
        rw [joined] at comptime
        contradiction
  · rintro ⟨runtimeAbsent, deferredMember⟩
    have noRuntime : stages.any (fun stage => stage == .runtime) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun present =>
        runtimeAbsent (any_runtime_true_iff stages |>.mp present)
    have notAll : stages.all (fun stage => stage == .comptime) ≠ true := by
      intro all
      have equal :=
        all_comptime_true_iff stages |>.mp all .deferred deferredMember
      cases equal
    have notComptime :
        stages.all (fun stage => stage == .comptime) = false :=
      Bool.eq_false_iff.mpr notAll
    simp only [join, noRuntime, notComptime, Bool.false_eq_true, if_false]

/-- Joining concatenated inputs is the same as joining their aggregate stages. -/
theorem join_append (left right : List Stage) :
    join (left ++ right) = join [join left, join right] := by
  generalize leftRuntime :
    left.any (fun stage => stage == .runtime) = leftHasRuntime
  generalize rightRuntime :
    right.any (fun stage => stage == .runtime) = rightHasRuntime
  generalize leftComptime :
    left.all (fun stage => stage == .comptime) = leftIsComptime
  generalize rightComptime :
    right.all (fun stage => stage == .comptime) = rightIsComptime
  cases leftHasRuntime <;> cases rightHasRuntime <;>
    cases leftIsComptime <;> cases rightIsComptime
  all_goals simp only [join, List.any_append, List.all_append,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    leftRuntime, rightRuntime, leftComptime, rightComptime,
    Bool.false_or, Bool.true_or, Bool.or_false, Bool.false_and,
    Bool.true_and, Bool.and_true]
  all_goals simp [comptime_beq_runtime, runtime_beq_runtime,
    deferred_beq_runtime, comptime_beq_comptime, deferred_beq_comptime]

end Solcore.Frontend.SourceStageAnalysis.Stage

namespace Solcore.Frontend.SourceStageAnalysis

open SourceInference TypeSystem

namespace SemanticStaging

abbrev Stage := SourceSemantics.Staging.Stage
abbrev AllComptime := SourceSemantics.Staging.AllComptime
abbrev DirectResultComptime := SourceSemantics.Staging.DirectResultComptime
abbrev DirectCallGetsStage := SourceSemantics.Staging.DirectCallGetsStage

end SemanticStaging

/-- The executable predicate for stage-only source types is exact with
respect to the independent declarative classification. -/
theorem typeIsComptimeOnly_eq_true_iff (type : Ty) :
    typeIsComptimeOnly type = true ↔
      SourceSemantics.Staging.ComptimeOnlyType type := by
  constructor
  · intro accepted
    cases type with
    | constructor constructor =>
        cases constructor with
        | builtin builtin =>
            cases builtin with
            | unit => simp [typeIsComptimeOnly] at accepted
            | bool => simp [typeIsComptimeOnly] at accepted
            | word => simp [typeIsComptimeOnly] at accepted
            | integer => exact .integer
        | declaration declaration =>
            simp [typeIsComptimeOnly] at accepted
    | comptime inner => exact .marked inner
    | «variable» metavariable => simp [typeIsComptimeOnly] at accepted
    | parameter parameter => simp [typeIsComptimeOnly] at accepted
    | application function argument => simp [typeIsComptimeOnly] at accepted
    | function parameter result => simp [typeIsComptimeOnly] at accepted
    | product left right => simp [typeIsComptimeOnly] at accepted
    | mapping key value => simp [typeIsComptimeOnly] at accepted
    | proxy inner => simp [typeIsComptimeOnly] at accepted
    | error => simp [typeIsComptimeOnly] at accepted
  · intro semantic
    cases semantic <;> rfl

@[simp] theorem Stage.toSemantic_eq_comptime_iff (stage : Stage) :
    stage.toSemantic = .comptime ↔ stage = .comptime := by
  cases stage <;> simp [Stage.toSemantic]

/-- Pointwise compile-time arguments in the executable list are exactly the
declarative `AllComptime` premise after stage-carrier conversion. -/
theorem stages_all_comptime_eq_true_iff (stages : List Stage) :
    stages.all (fun stage => stage == .comptime) = true ↔
      SourceSemantics.Staging.AllComptime (stages.map Stage.toSemantic) := by
  rw [Stage.all_comptime_true_iff]
  constructor
  · intro all semantic member
    obtain ⟨stage, sourceMember, equal⟩ := List.mem_map.mp member
    subst semantic
    rw [all stage sourceMember]
    rfl
  · intro all stage member
    have converted := all stage.toSemantic
      (List.mem_map.mpr ⟨stage, member, rfl⟩)
    cases stage <;> simp [Stage.toSemantic] at converted ⊢

/-- The executable direct-result test is equivalent to the premise used by
the declarative direct-call staging rule. -/
theorem directResultComptime_eq_true_iff
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) :
    (instantiation.returnComptime ||
      (node.coercions.isEmpty && typeIsComptimeOnly node.type)) = true ↔
      SourceSemantics.Staging.DirectResultComptime node instantiation := by
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  rw [typeIsComptimeOnly_eq_true_iff]
  simp [SourceSemantics.Staging.DirectResultComptime]

/-- The Boolean condition used by `directCallStage` is exactly the conjunction
of the two premises in declarative `DirectCallGetsStage.comptime`. -/
theorem directCallExecutable_eq_true_iff
    (node : ExpressionNode) (instantiation : DeclarationInstantiation)
    (argumentStages : List Stage) :
    ((instantiation.returnComptime ||
        (node.coercions.isEmpty && typeIsComptimeOnly node.type)) &&
      argumentStages.all fun argument => argument == .comptime) = true ↔
      SourceSemantics.Staging.DirectResultComptime node instantiation ∧
        SourceSemantics.Staging.AllComptime
          (argumentStages.map Stage.toSemantic) := by
  simp only [Bool.and_eq_true]
  rw [directResultComptime_eq_true_iff,
    stages_all_comptime_eq_true_iff]

/-- Each direct-call result computed by the executable classifier satisfies
the corresponding independent declarative call-site rule. -/
theorem directCallStage_sound
    (node : ExpressionNode) (instantiation : DeclarationInstantiation)
    (argumentStages : List Stage) :
    SourceSemantics.Staging.DirectCallGetsStage node instantiation
      (argumentStages.map Stage.toSemantic)
      (directCallStage node instantiation argumentStages).toSemantic := by
  by_cases executable :
      ((instantiation.returnComptime ||
          (node.coercions.isEmpty && typeIsComptimeOnly node.type)) &&
        argumentStages.all fun argument => argument == .comptime) = true
  · simp [directCallStage, executable, Stage.toSemantic]
    obtain ⟨resultComptime, argumentsComptime⟩ :=
      (directCallExecutable_eq_true_iff node instantiation argumentStages).mp
        executable
    exact .comptime resultComptime argumentsComptime
  · have rejected :
        ((instantiation.returnComptime ||
            (node.coercions.isEmpty && typeIsComptimeOnly node.type)) &&
          argumentStages.all fun argument => argument == .comptime) = false :=
        Bool.eq_false_iff.mpr executable
    simp [directCallStage, rejected, Stage.toSemantic]
    apply SourceSemantics.Staging.DirectCallGetsStage.deferred
    intro accepted
    exact executable
      ((directCallExecutable_eq_true_iff node instantiation argumentStages).mpr
        accepted)

/-- Public certificate extracted from one successful whole-function analysis.

The certificate deliberately stops short of `Staging.FunctionHasStages`: that
judgment also reconstructs the complete lexical `StageScope`, assignment
facts, and occurrence-graph derivations.  It nevertheless records the exact
analyzed carrier and guarantees that every direct-call classifier used by the
analysis implements the independent declarative call-site rule. -/
structure FunctionAnalysisCertificate (function : CheckedFunction)
    (analysis : Analysis) : Prop where
  analyzed : analyzeFunction function = .ok analysis
  sourceOwner : function.typedBody.owner = function.declaration
  directCalls : ∀ node,
    .expression node ∈ function.typedBody.nodes →
    ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) →
      ∀ argumentStages,
        SourceSemantics.Staging.DirectCallGetsStage node instantiation
          (argumentStages.map Stage.toSemantic)
          (directCallStage node instantiation argumentStages).toSemantic

/-- Successful executable analysis always exposes the public local-soundness
certificate. -/
theorem analyzeFunction_success_certificate
    (function : CheckedFunction) (analysis : Analysis)
    (success : analyzeFunction function = .ok analysis) :
    FunctionAnalysisCertificate function analysis := by
  have sourceOwner :
      function.typedBody.owner = function.declaration := by
    by_cases same : function.typedBody.owner = function.declaration
    · exact same
    · simp [analyzeFunction, same] at success
      change Except.error
        (Error.sourceOwnerMismatch function.declaration function.typedBody.owner) =
          Except.ok analysis at success
      cases success
  refine {
    analyzed := success
    sourceOwner := sourceOwner
    directCalls := ?_
  }
  intro node member callee arguments instantiation form argumentStages
  exact directCallStage_sound node instantiation argumentStages

end Solcore.Frontend.SourceStageAnalysis
