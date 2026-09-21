import Solcore.Frontend.SourceInference.Types

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

private abbrev Environment := List BinderStage

/-- Types whose values exist only at staged evaluation time in the current
source language.  `comptime<T>` is structural; the arbitrary-precision
`Integer` builtin is staged even without an explicit marker. -/
private def typeIsComptimeOnly : Ty → Bool
  | .constructor (.builtin .integer)
  | .comptime _ => true
  | _ => false

private structure Traversal where
  active : List OccurrenceId := []
  visited : List OccurrenceId := []
  expressions : List ExpressionStage := []
  binders : List BinderStage := []

private def lookupEnvironment? (environment : Environment)
    (binder : Resolved.LocalId) : Option Stage :=
  (environment.find? fun entry => decide (entry.binder = binder)).map (·.stage)

private def enterOccurrence (state : Traversal) (occurrence : OccurrenceId) :
    Except Error Traversal :=
  if state.active.any fun active => decide (active = occurrence) then
    .error (.cycle occurrence)
  else
    .ok { state with active := occurrence :: state.active }

private def leaveOccurrence (state : Traversal) (occurrence : OccurrenceId) :
    Except Error Traversal :=
  if state.visited.any fun visited => decide (visited = occurrence) then
    .error (.duplicateTraversal occurrence)
  else
    .ok {
      state with
      active := state.active.filter fun active => decide (active != occurrence)
      visited := state.visited ++ [occurrence]
    }

private def recordExpressionStage (state : Traversal)
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

private def registerBinder (owner : Resolved.DeclarationId)
    (environment : Environment) (state : Traversal)
    (binder : Resolved.LocalId) (stage : Stage) :
    Except Error (Environment × Traversal) := do
  if binder.owner != owner then
    throw (.binderOwnerMismatch owner binder)
  if state.binders.any fun entry => decide (entry.binder = binder) then
    throw (.duplicateBinder binder)
  let entry : BinderStage := { binder, stage }
  pure (entry :: environment, {
    state with binders := state.binders ++ [entry]
  })

private def registerTypedBinders (owner : Resolved.DeclarationId)
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

private def validateNodeTable (owner : Resolved.DeclarationId) :
    List OccurrenceId → List Node → Except Error Unit
  | _, [] => .ok ()
  | seen, node :: rest => do
      let occurrence := node.occurrenceId
      if occurrence.owner != owner then
        throw (.nodeOwnerMismatch owner occurrence)
      if seen.any fun prior => decide (prior = occurrence) then
        throw (.duplicateOccurrence occurrence)
      validateNodeTable owner (occurrence :: seen) rest

private def validateOccurrenceOwner (source : TypedSource)
    (occurrence : OccurrenceId) : Except Error Unit :=
  if occurrence.owner = source.owner then
    .ok ()
  else
    .error (.nodeOwnerMismatch source.owner occurrence)

private def lookupExpression (source : TypedSource) (id : ExpressionId) :
    Except Error ExpressionNode := do
  validateOccurrenceOwner source id.occurrence
  match source.lookupNode? id.occurrence with
  | none => throw (.missingNode id.occurrence)
  | some (.statement _) => throw (.expectedExpressionNode id.occurrence)
  | some (.expression node) => pure node

private def lookupStatement (source : TypedSource) (id : StatementId) :
    Except Error StatementNode := do
  validateOccurrenceOwner source id.occurrence
  match source.lookupNode? id.occurrence with
  | none => throw (.missingNode id.occurrence)
  | some (.expression _) => throw (.expectedStatementNode id.occurrence)
  | some (.statement node) => pure node

private def analyzeExpressionListWith
    (analyze : Traversal → ExpressionId →
      Except Error (Stage × Traversal)) :
    List ExpressionId → Traversal → Except Error (List Stage × Traversal)
  | [], state => .ok ([], state)
  | expression :: rest, state => do
      let (stage, state) ← analyze state expression
      let (stages, state) ← analyzeExpressionListWith analyze rest state
      pure (stage :: stages, state)

private def analyzeStatementListWith
    (analyze : Environment → Traversal → StatementId →
      Except Error (Environment × Traversal)) :
    List StatementId → Environment → Traversal →
      Except Error (Environment × Traversal)
  | [], environment, state => .ok (environment, state)
  | statement :: rest, environment, state => do
      let (environment, state) ← analyze environment state statement
      analyzeStatementListWith analyze rest environment state

private def analyzeMatchCasesWith
    (analyzeBody : Traversal → List StatementId → Except Error Traversal) :
    List TypedMatchCase → Traversal → Except Error Traversal
  | [], state => .ok state
  | arm :: rest, state => do
      let state ← analyzeBody state arm.body
      analyzeMatchCasesWith analyzeBody rest state

mutual

  private def analyzeExpressionFuel (source : TypedSource) :
      Nat → Environment → Traversal → ExpressionId →
        Except Error (Stage × Traversal)
    | 0, _, _, expression => .error (.depthLimit expression.occurrence)
    | fuel + 1, environment, state, expression => do
        let state ← enterOccurrence state expression.occurrence
        let node ← lookupExpression source expression
        let recurse := analyzeExpressionFuel source fuel environment
        let (stage, state) ← match node.form with
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
              recurse state inner
          | .tuple elements => do
              let (stages, state) ←
                analyzeExpressionListWith recurse elements state
              pure (Stage.join stages, state)
          | .binary left _ right => do
              let (leftStage, state) ← recurse state left
              let (rightStage, state) ← recurse state right
              pure (Stage.join [leftStage, rightStage], state)
          | .conditional condition thenBranch elseBranch => do
              let (conditionStage, state) ← recurse state condition
              let (thenStage, state) ← recurse state thenBranch
              let (elseStage, state) ← recurse state elseBranch
              pure (Stage.join [conditionStage, thenStage, elseStage], state)
          | .lambda parameters _ body => do
              let (lambdaEnvironment, state) ←
                registerTypedBinders source.owner false parameters environment state
              let (_, state) ← analyzeStatementListWith
                (analyzeStatementFuel source fuel) body lambdaEnvironment state
              pure (.deferred, state)
          | .call callee arguments resolution => do
              let (_, state) ← recurse state callee
              let (argumentStages, state) ←
                analyzeExpressionListWith recurse arguments state
              let stage := match resolution with
                | .declaration instantiation =>
                    let resultIsComptimeOnly :=
                      node.coercions.isEmpty && typeIsComptimeOnly node.type
                    if (instantiation.returnComptime || resultIsComptimeOnly) &&
                        argumentStages.all fun argument =>
                          argument == .comptime then
                      Stage.comptime
                    else
                      Stage.deferred
                | .indirect _
                | .builtinFunction _ => Stage.deferred
              pure (stage, state)
          | .proxy _ =>
              pure (.deferred, state)
          | .index base index => do
              let (_, state) ← recurse state base
              let (_, state) ← recurse state index
              pure (.deferred, state)
        let state ← recordExpressionStage state expression stage
        let state ← leaveOccurrence state expression.occurrence
        pure (stage, state)

  private def analyzeStatementFuel (source : TypedSource) :
      Nat → Environment → Traversal → StatementId →
        Except Error (Environment × Traversal)
    | 0, _, _, statement => .error (.depthLimit statement.occurrence)
    | fuel + 1, environment, state, statement => do
        let state ← enterOccurrence state statement.occurrence
        let node ← lookupStatement source statement
        let analyzeExpression := analyzeExpressionFuel source fuel environment
        let (environment, state) ← match node.form with
          | .letDecl binder initializer => do
              let (stage, state) ← match initializer with
                | none => pure (Stage.deferred, state)
                | some initializer => analyzeExpression state initializer
              registerBinder source.owner environment state binder.id stage
          | .returnStmt value => do
              let state ← match value with
                | none => pure state
                | some value => (analyzeExpression state value).map (·.2)
              pure (environment, state)
          | .expression expression _ => do
              let (_, state) ← analyzeExpression state expression
              pure (environment, state)
          | .ifThen condition thenBody elseBody => do
              let (_, state) ← analyzeExpression state condition
              let (_, state) ← analyzeStatementListWith
                (analyzeStatementFuel source fuel) thenBody environment state
              let state ← match elseBody with
                | none => pure state
                | some body => do
                    let (_, state) ← analyzeStatementListWith
                      (analyzeStatementFuel source fuel) body environment state
                    pure state
              pure (environment, state)
          | .block body => do
              let (_, state) ← analyzeStatementListWith
                (analyzeStatementFuel source fuel) body environment state
              pure (environment, state)
          | .matchWith resolution => do
              let (scrutineeStage, state) ←
                analyzeExpression state resolution.scrutinee
              let (_, state) ←
                registerBinder source.owner environment state
                resolution.hiddenScrutinee scrutineeStage
              let analyzeBody := fun state body => do
                let (_, state) ← analyzeStatementListWith
                  (analyzeStatementFuel source fuel) body environment state
                pure state
              let state ← analyzeMatchCasesWith analyzeBody
                resolution.cases state
              let state ← match resolution.defaultBody with
                | none => pure state
                | some body => analyzeBody state body
              pure (environment, state)
        let state ← leaveOccurrence state statement.occurrence
        pure (environment, state)

end

private def analyzeRoots (source : TypedSource) (fuel : Nat) :
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

private def firstUnvisited? (state : Traversal) : List Node → Option OccurrenceId
  | [] => none
  | node :: rest =>
      if state.visited.any fun visited => decide (visited = node.occurrenceId) then
        firstUnvisited? state rest
      else
        some node.occurrenceId

/-- Classify every reachable expression and lexical binder in a checked
function.  The traversal follows roots and lexical statement order rather than
the storage order of the heterogeneous node table. -/
def analyzeFunction (function : CheckedFunction) : Except Error Analysis := do
  let source := function.typedBody
  if source.owner != function.declaration then
    throw (.sourceOwnerMismatch function.declaration source.owner)
  validateNodeTable source.owner [] source.nodes
  let resultIsComptimeOnly := typeIsComptimeOnly function.inferredBodyType
  let (environment, state) ← registerTypedBinders source.owner
    (function.returnComptime || resultIsComptimeOnly) source.inputs [] {}
  let (_, state) ← analyzeRoots source (source.nodes.length + 1)
    source.roots environment state
  match firstUnvisited? state source.nodes with
  | some occurrence => throw (.unreachableNode occurrence)
  | none => pure {
      expressions := state.expressions
      binders := state.binders
    }

end Solcore.Frontend.SourceStageAnalysis
