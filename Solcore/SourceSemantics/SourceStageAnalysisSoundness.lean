import Solcore.Frontend.SourceStageAnalysis
import Solcore.SourceSemantics.Staging.Classification
import Solcore.SourceSemantics.SourceInferenceSoundness

/-!
# Soundness of executable source-stage classification

This module relates the executable three-point classifier and its lexical
tables to the independent staging judgments over resolved source.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceStageAnalysisSoundness

open Frontend Frontend.SourceInference
open Frontend.SourceStageAnalysis
open Frontend.SourceStageAnalysis.Detail
open TypeSystem
open Staging

/-- The executable join always constructs the corresponding declarative join. -/
theorem join_sound (stages : List Frontend.SourceStageAnalysis.Stage) :
    StagesJoin (stages.map Frontend.SourceStageAnalysis.Stage.toSemantic)
      (Frontend.SourceStageAnalysis.Stage.join stages).toSemantic := by
  by_cases hasRuntime : Frontend.SourceStageAnalysis.Stage.runtime ∈ stages
  · rw [Frontend.SourceStageAnalysis.Stage.join_eq_runtime_of_mem hasRuntime]
    exact .runtime (List.mem_map.mpr ⟨.runtime, hasRuntime, rfl⟩)
  · by_cases hasDeferred : Frontend.SourceStageAnalysis.Stage.deferred ∈ stages
    · rw [(Frontend.SourceStageAnalysis.Stage.join_eq_deferred_iff stages).2
          ⟨hasRuntime, hasDeferred⟩]
      refine .deferred ?_ ?_
      · intro member
        rcases List.mem_map.mp member with ⟨stage, stageMem, stageEq⟩
        cases stage with
        | comptime => cases stageEq
        | runtime => exact hasRuntime stageMem
        | deferred => cases stageEq
      · exact List.mem_map.mpr ⟨.deferred, hasDeferred, rfl⟩
    · have all : ∀ stage ∈ stages,
          stage = Frontend.SourceStageAnalysis.Stage.comptime := by
        intro stage member
        cases stage with
        | comptime => rfl
        | runtime => exact False.elim (hasRuntime member)
        | deferred => exact False.elim (hasDeferred member)
      rw [Frontend.SourceStageAnalysis.Stage.join_eq_comptime_of_forall all]
      apply StagesJoin.comptime
      intro stage member
      rcases List.mem_map.mp member with ⟨sourceStage, sourceMember, rfl⟩
      rw [all sourceStage sourceMember]
      rfl

/-- The semantic join of converted stages is exactly the executable result. -/
theorem join_iff (stages : List Frontend.SourceStageAnalysis.Stage)
    (stage : Staging.Stage) :
    StagesJoin (stages.map Frontend.SourceStageAnalysis.Stage.toSemantic) stage ↔
      stage = (Frontend.SourceStageAnalysis.Stage.join stages).toSemantic := by
  constructor
  · intro joined
    exact StagesJoin.unique joined (join_sound stages)
  · intro equal
    subst stage
    exact join_sound stages

/-- The exact source assignment roots exposed by one `for` item. -/
def forItemAssignedBinders : ForItemForm → List Resolved.LocalId
  | .assignValue assignment _ _
  | .assignBitNot assignment => [assignment.target.root]
  | .letDecl _ _
  | .expression _ => []

/-- The exact source assignment roots exposed by one statement form. -/
def statementAssignedBinders : StatementForm → List Resolved.LocalId
  | .assignValue assignment _ _
  | .assignBitNot assignment => [assignment.target.root]
  | .forLoop initializer _ post _ =>
      (initializer ++ post).flatMap forItemAssignedBinders
  | _ => []

/-- The exact source assignment roots exposed by one table node. -/
def nodeAssignedBinders : Node → List Resolved.LocalId
  | .statement node => statementAssignedBinders node.form
  | .expression _ => []

theorem forItemAssigns_iff (item : ForItemForm) (binder : Resolved.LocalId) :
    ForItemAssigns item binder ↔ binder ∈ forItemAssignedBinders item := by
  cases item with
  | letDecl _ _ =>
      simp only [forItemAssignedBinders, List.not_mem_nil, iff_false]
      intro assigned
      cases assigned
  | expression _ =>
      simp only [forItemAssignedBinders, List.not_mem_nil, iff_false]
      intro assigned
      cases assigned
  | assignValue assignment operator value =>
      simp only [forItemAssignedBinders, List.mem_singleton]
      constructor
      · intro assigned
        cases assigned
        rfl
      · intro equal
        subst binder
        exact .value assignment operator value
  | assignBitNot assignment =>
      simp only [forItemAssignedBinders, List.mem_singleton]
      constructor
      · intro assigned
        cases assigned
        rfl
      · intro equal
        subst binder
        exact .bitNot assignment

theorem statementAssigns_iff (form : StatementForm)
    (binder : Resolved.LocalId) :
    StatementAssigns form binder ↔ binder ∈ statementAssignedBinders form := by
  cases form with
  | assignValue assignment operator value =>
      simp only [statementAssignedBinders, List.mem_singleton]
      constructor
      · intro assigned
        cases assigned
        rfl
      · intro equal
        subst binder
        exact .value assignment operator value
  | assignBitNot assignment =>
      simp only [statementAssignedBinders, List.mem_singleton]
      constructor
      · intro assigned
        cases assigned
        rfl
      · intro equal
        subst binder
        exact .bitNot assignment
  | forLoop initializer condition post body =>
      simp only [statementAssignedBinders, List.mem_flatMap,
        List.mem_append]
      constructor
      · intro assigned
        cases assigned with
        | forInitializer member assigns =>
            exact ⟨_, Or.inl member,
              (forItemAssigns_iff _ _).mp assigns⟩
        | forPost member assigns =>
            exact ⟨_, Or.inr member,
              (forItemAssigns_iff _ _).mp assigns⟩
      · rintro ⟨item, member, assigned⟩
        rcases member with member | member
        · exact .forInitializer member
            ((forItemAssigns_iff _ _).mpr assigned)
        · exact .forPost member
            ((forItemAssigns_iff _ _).mpr assigned)
  | letDecl _ _ => simp [statementAssignedBinders]; intro h; cases h
  | returnStmt _ => simp [statementAssignedBinders]; intro h; cases h
  | expression _ _ => simp [statementAssignedBinders]; intro h; cases h
  | ifThen _ _ _ => simp [statementAssignedBinders]; intro h; cases h
  | block _ => simp [statementAssignedBinders]; intro h; cases h
  | matchWith _ => simp [statementAssignedBinders]; intro h; cases h
  | whileLoop _ _ => simp [statementAssignedBinders]; intro h; cases h
  | breakStmt => simp [statementAssignedBinders]; intro h; cases h
  | continueStmt => simp [statementAssignedBinders]; intro h; cases h

/-- The executable mutation inventory is exactly declarative `AssignedIn`. -/
theorem assignedIn_iff (source : TypedSource) (binder : Resolved.LocalId) :
    AssignedIn source binder ↔
      binder ∈ source.nodes.flatMap nodeAssignedBinders := by
  constructor
  · rintro ⟨id, node, contains, assigned⟩
    exact List.mem_flatMap.mpr
      ⟨.statement node, contains.1,
        (statementAssigns_iff node.form binder).mp assigned⟩
  · intro member
    rcases List.mem_flatMap.mp member with ⟨node, nodeMember, assigned⟩
    cases node with
    | expression expression =>
        simp [nodeAssignedBinders] at assigned
    | statement statement =>
        exact ⟨statement.id, statement, ⟨nodeMember, rfl⟩,
          (statementAssigns_iff statement.form binder).mpr assigned⟩

/-- Convert the executable lexical table to a declarative stage scope. -/
def toSemanticScope (environment : List BinderStage) : StageScope :=
  environment.map fun entry => (entry.binder, entry.stage.toSemantic)

/-- The executable first-match lookup, exposed for statementwise proofs. -/
def environmentLookup? (environment : List BinderStage)
    (binder : Resolved.LocalId) : Option Frontend.SourceStageAnalysis.Stage :=
  (environment.find? fun entry => decide (entry.binder = binder)).map (·.stage)

@[simp] theorem environmentLookup?_eq (environment : List BinderStage)
    (binder : Resolved.LocalId) :
    environmentLookup? environment binder =
      lookupEnvironment? environment binder := rfl

@[simp] theorem mutableBindersInForItem_eq (item : ForItemForm) :
    mutableBindersInForItem item = forItemAssignedBinders item := by
  cases item <;> rfl

@[simp] theorem mutableBindersInNode_eq (node : Node) :
    mutableBindersInNode node = nodeAssignedBinders node := by
  have itemsEqual : mutableBindersInForItem = forItemAssignedBinders := by
    funext item
    exact mutableBindersInForItem_eq item
  cases node with
  | expression _ => rfl
  | statement statement =>
      cases statement with
      | mk id span type form =>
          cases form <;>
            simp [mutableBindersInNode, nodeAssignedBinders,
              statementAssignedBinders, itemsEqual]

theorem mutableInventory_eq (source : TypedSource) :
    source.nodes.flatMap mutableBindersInNode =
      source.nodes.flatMap nodeAssignedBinders := by
  induction source.nodes with
  | nil => rfl
  | cons node rest induction =>
      simp only [List.flatMap_cons, mutableBindersInNode_eq node, induction]

theorem environmentLookup?_sound
    {environment : List BinderStage} {binder : Resolved.LocalId}
    {stage : Frontend.SourceStageAnalysis.Stage}
    (found : environmentLookup? environment binder = some stage) :
    (toSemanticScope environment).Lookup binder stage.toSemantic := by
  induction environment with
  | nil => simp [environmentLookup?] at found
  | cons entry rest induction =>
      by_cases same : entry.binder = binder
      · simp [environmentLookup?, same] at found
        subst binder
        subst stage
        exact .head
      · have tailFound : environmentLookup? rest binder = some stage := by
          simpa [environmentLookup?, same] using found
        exact .tail same (induction tailFound)

theorem lookupEnvironment?_sound
    {environment : Frontend.SourceStageAnalysis.Environment}
    {binder : Resolved.LocalId}
    {stage : Frontend.SourceStageAnalysis.Stage}
    (found : lookupEnvironment? environment binder = some stage) :
    (toSemanticScope environment).Lookup binder stage.toSemantic :=
  environmentLookup?_sound (by simpa only [environmentLookup?_eq] using found)

/-- Entering a binder at the executable mutation-adjusted stage is justified
by the declarative assignment inventory. -/
theorem binderGetsStage_of_inventory (source : TypedSource)
    (scope : StageScope) (binder : Resolved.LocalId)
    (requested : Frontend.SourceStageAnalysis.Stage)
    (owned : binder.owner = source.owner) :
    BinderGetsStage source scope binder requested.toSemantic
      (if binder ∈ source.nodes.flatMap mutableBindersInNode then
        Staging.Stage.deferred else requested.toSemantic)
      ((binder, if binder ∈ source.nodes.flatMap mutableBindersInNode then
        Staging.Stage.deferred else requested.toSemantic) :: scope) := by
  by_cases assigned : binder ∈ source.nodes.flatMap mutableBindersInNode
  · simp only [assigned, ↓reduceIte]
    exact .assigned owned
      ((assignedIn_iff source binder).mpr (by
        rw [← mutableInventory_eq source]
        exact assigned))
  · simp only [assigned, ↓reduceIte]
    exact .stable owned (by
      intro semanticAssigned
      apply assigned
      have assignedMirror := (assignedIn_iff source binder).mp semanticAssigned
      rw [mutableInventory_eq source]
      exact assignedMirror)

/-- The immutable assignment inventory is retained throughout traversal. -/
def TraversalValid (source : TypedSource) (state : Traversal) : Prop :=
  state.mutableBinders = source.nodes.flatMap mutableBindersInNode

theorem registerBinder_sound
    (source : TypedSource) (environment : Frontend.SourceStageAnalysis.Environment)
    (state nextState : Traversal) (binder : Resolved.LocalId)
    (requested : Frontend.SourceStageAnalysis.Stage)
    (nextEnvironment : Frontend.SourceStageAnalysis.Environment)
    (valid : TraversalValid source state)
    (registered : registerBinder source.owner environment state binder requested =
      .ok (nextEnvironment, nextState)) :
    TraversalValid source nextState ∧
      ∃ actual : Frontend.SourceStageAnalysis.Stage,
        BinderGetsStage source (toSemanticScope environment) binder
          requested.toSemantic actual.toSemantic
          (toSemanticScope nextEnvironment) := by
  by_cases owned : binder.owner = source.owner
  · by_cases duplicate :
        (state.binders.any fun entry => decide (entry.binder = binder)) = true
    · simp [registerBinder, owned, duplicate] at registered
      change Except.error (Error.duplicateBinder binder) =
        Except.ok (nextEnvironment, nextState) at registered
      cases registered
    · by_cases mutable : binder ∈ state.mutableBinders
      · simp [registerBinder, owned, duplicate, mutable] at registered
        obtain ⟨rfl, rfl⟩ := registered
        constructor
        · exact valid
        · refine ⟨.deferred, ?_⟩
          have assigned : AssignedIn source binder :=
            (assignedIn_iff source binder).mpr (by
              rw [← mutableInventory_eq source, ← valid]
              exact mutable)
          exact .assigned owned assigned
      · simp [registerBinder, owned, duplicate, mutable] at registered
        obtain ⟨rfl, rfl⟩ := registered
        constructor
        · exact valid
        · refine ⟨requested, ?_⟩
          have notAssigned : ¬ AssignedIn source binder := by
            intro assigned
            apply mutable
            rw [valid, mutableInventory_eq source]
            exact (assignedIn_iff source binder).mp assigned
          exact .stable owned notAssigned
  · simp [registerBinder, owned] at registered
    change Except.error (Error.binderOwnerMismatch source.owner binder) =
      Except.ok (nextEnvironment, nextState) at registered
    cases registered

/-- The unforced executable parameter rule implements the declarative
default-stage priority: explicit mark, stage-only type, then runtime. -/
theorem binderDefaultStage_sound (binder : TypedBinder) :
    BinderDefaultStage binder
      (if binder.comptime || typeIsComptimeOnly binder.scheme.body then
        Staging.Stage.comptime else Staging.Stage.runtime) := by
  by_cases marked : binder.comptime = true
  · simp only [marked, Bool.true_or, ↓reduceIte]
    exact .marked marked
  · have unmarked : binder.comptime = false := Bool.eq_false_iff.mpr marked
    by_cases typeOnly : typeIsComptimeOnly binder.scheme.body = true
    · simp only [unmarked, Bool.false_or, typeOnly, ↓reduceIte]
      exact .comptimeType unmarked
        ((Frontend.SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff
          binder.scheme.body).mp typeOnly)
    · have typeRuntime : typeIsComptimeOnly binder.scheme.body = false :=
        Bool.eq_false_iff.mpr typeOnly
      simp only [unmarked, Bool.false_or, typeRuntime, Bool.false_eq_true,
        ↓reduceIte]
      exact .runtime unmarked (by
        intro semanticOnly
        exact typeOnly
          ((Frontend.SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff
            binder.scheme.body).mpr semanticOnly))

theorem registerTypedBinders_sound
    (source : TypedSource) (force : Bool) (binders : List TypedBinder)
    (environment nextEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state nextState : Traversal)
    (valid : TraversalValid source state)
    (registered : registerTypedBinders source.owner force binders environment state =
      .ok (nextEnvironment, nextState)) :
    TraversalValid source nextState ∧
      (force = true → BindersGetStage source .comptime
        (toSemanticScope environment) binders (toSemanticScope nextEnvironment)) ∧
      (force = false → BindersGetDefaultStages source
        (toSemanticScope environment) binders (toSemanticScope nextEnvironment)) := by
  induction binders generalizing environment state with
  | nil =>
      simp only [registerTypedBinders] at registered
      cases registered
      exact ⟨valid, fun _ => .nil _, fun _ => .nil _⟩
  | cons binder rest induction =>
      let requested : Frontend.SourceStageAnalysis.Stage :=
        if force || binder.comptime || typeIsComptimeOnly binder.scheme.body then
          .comptime else .runtime
      have unfoldStep :
          registerTypedBinders source.owner force (binder :: rest)
              environment state =
            registerBinder source.owner environment state binder.id requested >>=
              fun pair => registerTypedBinders source.owner force rest pair.1
                pair.2 := rfl
      cases headResult : registerBinder source.owner environment state binder.id
          requested with
      | error error =>
          rw [unfoldStep, headResult] at registered
          cases registered
      | ok pair =>
          rcases pair with ⟨middleEnvironment, middleState⟩
          have headSuccess : registerBinder source.owner environment state binder.id
              requested = .ok (middleEnvironment, middleState) := headResult
          have tailSuccess :
              registerTypedBinders source.owner force rest middleEnvironment
                middleState = .ok (nextEnvironment, nextState) := by
            rw [unfoldStep, headResult] at registered
            exact registered
          obtain ⟨middleValid, actual, headStage⟩ :=
            registerBinder_sound source environment state middleState binder.id
              requested middleEnvironment valid headSuccess
          obtain ⟨finalValid, tailForced, tailDefault⟩ :=
            induction middleEnvironment middleState middleValid tailSuccess
          refine ⟨finalValid, ?_, ?_⟩
          · intro forced
            have requestedComptime : requested.toSemantic =
                Staging.Stage.comptime := by simp [requested, forced]
            exact BindersGetStage.cons (requestedComptime ▸ headStage)
              (tailForced forced)
          · intro ordinary
            have requestedDefault : BinderDefaultStage binder
                requested.toSemantic := by
              have requestedEq : requested.toSemantic =
                  (if binder.comptime ||
                      typeIsComptimeOnly binder.scheme.body then
                    Staging.Stage.comptime else Staging.Stage.runtime) := by
                cases marked : binder.comptime <;>
                  cases onlyType : typeIsComptimeOnly binder.scheme.body <;>
                  simp [requested, ordinary, marked, onlyType,
                    Frontend.SourceStageAnalysis.Stage.toSemantic]
              rw [requestedEq]
              exact binderDefaultStage_sound binder
            exact BindersGetDefaultStages.cons requestedDefault headStage
              (tailDefault ordinary)

theorem lookupExpression_sound
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (found : lookupExpression source id = .ok node) :
    SourceSemantics.ContainsExpression source id node := by
  unfold lookupExpression at found
  cases ownerResult : validateOccurrenceOwner source id.occurrence with
  | error error =>
      rw [ownerResult] at found
      change Except.error error = Except.ok node at found
      cases found
  | ok _ =>
      rw [ownerResult] at found
      generalize selected : source.lookupNode? id.occurrence = candidate at found
      cases candidate with
      | none =>
          change Except.error (Error.missingNode id.occurrence) =
            Except.ok node at found
          cases found
      | some candidate =>
          cases candidate with
          | statement _ =>
              change Except.error (Error.expectedExpressionNode id.occurrence) =
                Except.ok node at found
              cases found
          | expression expression =>
              change Except.ok expression = Except.ok node at found
              cases found
              exact SourceSemantics.lookupExpression?_sound (by
                simp [TypedSource.lookupExpression?, selected])

theorem lookupStatement_sound
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    (found : lookupStatement source id = .ok node) :
    SourceSemantics.ContainsStatement source id node := by
  unfold lookupStatement at found
  cases ownerResult : validateOccurrenceOwner source id.occurrence with
  | error error =>
      rw [ownerResult] at found
      change Except.error error = Except.ok node at found
      cases found
  | ok _ =>
      rw [ownerResult] at found
      generalize selected : source.lookupNode? id.occurrence = candidate at found
      cases candidate with
      | none =>
          change Except.error (Error.missingNode id.occurrence) =
            Except.ok node at found
          cases found
      | some candidate =>
          cases candidate with
          | expression _ =>
              change Except.error (Error.expectedStatementNode id.occurrence) =
                Except.ok node at found
              cases found
          | statement statement =>
              change Except.ok statement = Except.ok node at found
              cases found
              exact SourceSemantics.lookupStatement?_sound (by
                simp [TypedSource.lookupStatement?, selected])

theorem enterOccurrence_valid
    {source : TypedSource} {state next : Traversal} {id : OccurrenceId}
    (valid : TraversalValid source state)
    (entered : enterOccurrence state id = .ok next) :
    TraversalValid source next := by
  unfold enterOccurrence at entered
  split at entered
  · cases entered
  · cases entered
    exact valid

theorem leaveOccurrence_valid
    {source : TypedSource} {state next : Traversal} {id : OccurrenceId}
    (valid : TraversalValid source state)
    (left : leaveOccurrence state id = .ok next) :
    TraversalValid source next := by
  unfold leaveOccurrence at left
  split at left
  · cases left
  · cases left
    exact valid

theorem recordExpressionStage_valid
    {source : TypedSource} {state next : Traversal}
    {id : ExpressionId} {stage : Frontend.SourceStageAnalysis.Stage}
    (valid : TraversalValid source state)
    (recorded : recordExpressionStage state id stage = .ok next) :
    TraversalValid source next := by
  unfold recordExpressionStage at recorded
  split at recorded
  · cases recorded
    exact valid
  · split at recorded <;> cases recorded

theorem analyzeExpressionListWith_sound
    (source : TypedSource) (scope : StageScope)
    (analyze : Traversal → ExpressionId →
      Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Stage × Traversal))
    (analyzeSound : ∀ state id stage next,
      TraversalValid source state →
      analyze state id = .ok (stage, next) →
      TraversalValid source next ∧
        HasStage source scope id stage.toSemantic)
    (ids : List ExpressionId) (state finalState : Traversal)
    (stages : List Frontend.SourceStageAnalysis.Stage)
    (valid : TraversalValid source state)
    (success : analyzeExpressionListWith analyze ids state =
      .ok (stages, finalState)) :
    TraversalValid source finalState ∧
      ExpressionsHaveStages source scope ids
        (stages.map Frontend.SourceStageAnalysis.Stage.toSemantic) := by
  induction ids generalizing state stages with
  | nil =>
      simp only [analyzeExpressionListWith] at success
      cases success
      exact ⟨valid, .nil _⟩
  | cons id rest induction =>
      simp only [analyzeExpressionListWith] at success
      cases headResult : analyze state id with
      | error error =>
          rw [headResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨stage, middleState⟩
          rw [headResult] at success
          change (analyzeExpressionListWith analyze rest middleState).map
              (fun pair => (stage :: pair.1, pair.2)) =
            Except.ok (stages, finalState) at success
          have head := analyzeSound state id stage middleState valid headResult
          cases tailResult : analyzeExpressionListWith analyze rest middleState with
          | error error =>
              rw [tailResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨tailStages, actualFinal⟩
              rw [tailResult] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, tailStagesSound⟩ :=
                induction middleState tailStages head.1 tailResult
              exact ⟨finalValid, .cons head.2 tailStagesSound⟩

theorem analyzeStatementListWith_sound
    (source : TypedSource)
    (analyze : Frontend.SourceStageAnalysis.Environment → Traversal →
      StatementId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Environment × Traversal))
    (analyzeSound : ∀ environment state id nextEnvironment nextState,
      TraversalValid source state →
      analyze environment state id = .ok (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementStages source (toSemanticScope environment) id
          (toSemanticScope nextEnvironment))
    (ids : List StatementId)
    (environment finalEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzeStatementListWith analyze ids environment state =
      .ok (finalEnvironment, finalState)) :
    TraversalValid source finalState ∧
      StatementsStage source (toSemanticScope environment) ids
        (toSemanticScope finalEnvironment) := by
  induction ids generalizing environment state with
  | nil =>
      simp only [analyzeStatementListWith] at success
      cases success
      exact ⟨valid, .nil _⟩
  | cons id rest induction =>
      simp only [analyzeStatementListWith] at success
      cases headResult : analyze environment state id with
      | error error =>
          rw [headResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨middleEnvironment, middleState⟩
          rw [headResult] at success
          change analyzeStatementListWith analyze rest middleEnvironment
              middleState = Except.ok (finalEnvironment, finalState) at success
          have head := analyzeSound environment state id middleEnvironment
            middleState valid headResult
          cases tailResult : analyzeStatementListWith analyze rest
              middleEnvironment middleState with
          | error error =>
              rw [tailResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨actualEnvironment, actualState⟩
              rw [tailResult] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, tailStagesSound⟩ :=
                induction middleEnvironment middleState head.1 tailResult
              exact ⟨finalValid, .cons head.2 tailStagesSound⟩

theorem bindersInPatternInstruction_eq (instruction : MatchPatternInstruction) :
    bindersInPatternInstruction instruction =
      Staging.instructionBinders instruction := by
  cases instruction <;>
    rfl

theorem bindersInPatternResolution_eq (resolution : MatchPatternResolution) :
    bindersInPatternResolution resolution =
      Staging.patternBinders resolution := by
  have instructionsEq : bindersInPatternInstruction =
      Staging.instructionBinders := by
    funext instruction
    exact bindersInPatternInstruction_eq instruction
  cases resolution <;>
    simp [bindersInPatternResolution, Staging.patternBinders,
      instructionsEq]

theorem registerPatternBinders_sound
    (source : TypedSource)
    (requested : Frontend.SourceStageAnalysis.Stage)
    (binders : List TypedBinder)
    (environment nextEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state nextState : Traversal)
    (valid : TraversalValid source state)
    (registered : registerPatternBinders source.owner requested binders
      environment state = .ok (nextEnvironment, nextState)) :
    TraversalValid source nextState ∧
      BindersGetStage source requested.toSemantic
        (toSemanticScope environment) binders
        (toSemanticScope nextEnvironment) := by
  induction binders generalizing environment state with
  | nil =>
      simp only [registerPatternBinders] at registered
      cases registered
      exact ⟨valid, .nil _⟩
  | cons binder rest induction =>
      have unfoldStep :
          registerPatternBinders source.owner requested (binder :: rest)
              environment state =
            registerBinder source.owner environment state binder.id requested >>=
              fun pair => registerPatternBinders source.owner requested rest
                pair.1 pair.2 := rfl
      cases headResult : registerBinder source.owner environment state binder.id
          requested with
      | error error =>
          rw [unfoldStep, headResult] at registered
          cases registered
      | ok pair =>
          rcases pair with ⟨middleEnvironment, middleState⟩
          have headSuccess : registerBinder source.owner environment state
              binder.id requested = .ok (middleEnvironment, middleState) :=
            headResult
          have tailSuccess : registerPatternBinders source.owner requested rest
              middleEnvironment middleState = .ok (nextEnvironment, nextState) := by
            rw [unfoldStep, headResult] at registered
            exact registered
          obtain ⟨middleValid, actual, headStage⟩ :=
            registerBinder_sound source environment state middleState binder.id
              requested middleEnvironment valid headSuccess
          obtain ⟨finalValid, tailStage⟩ :=
            induction middleEnvironment middleState middleValid tailSuccess
          exact ⟨finalValid, .cons headStage tailStage⟩

theorem analyzeMatchCasesWith_sound
    (source : TypedSource)
    (scrutineeStage : Frontend.SourceStageAnalysis.Stage)
    (analyzeStatements : List StatementId →
      Frontend.SourceStageAnalysis.Environment → Traversal →
      Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Environment × Traversal))
    (analyzeStatementsSound : ∀ ids environment state nextEnvironment nextState,
      TraversalValid source state →
      analyzeStatements ids environment state =
        .ok (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementsStage source (toSemanticScope environment) ids
          (toSemanticScope nextEnvironment))
    (cases : List TypedMatchCase)
    (environment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzeMatchCasesWith source.owner scrutineeStage
      analyzeStatements cases environment state = .ok finalState) :
    TraversalValid source finalState ∧
      MatchCasesStage source (toSemanticScope environment)
        scrutineeStage.toSemantic cases := by
  induction cases generalizing state with
  | nil =>
      simp only [analyzeMatchCasesWith] at success
      cases success
      exact ⟨valid, .nil _ _⟩
  | cons arm rest induction =>
      let binders := bindersInPatternResolution arm.pattern.resolution
      have unfoldStep :
          analyzeMatchCasesWith source.owner scrutineeStage analyzeStatements
              (arm :: rest) environment state =
            registerPatternBinders source.owner scrutineeStage binders
                environment state >>=
              fun pair =>
                analyzeStatements arm.body pair.1 pair.2 >>=
                  fun bodyPair =>
                    analyzeMatchCasesWith source.owner scrutineeStage
                      analyzeStatements rest environment bodyPair.2 := rfl
      cases binderResult : registerPatternBinders source.owner scrutineeStage
          binders environment state with
      | error error =>
          rw [unfoldStep, binderResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨armEnvironment, binderState⟩
          rw [unfoldStep, binderResult] at success
          change (analyzeStatements arm.body armEnvironment binderState >>=
              fun bodyPair => analyzeMatchCasesWith source.owner scrutineeStage
                analyzeStatements rest environment bodyPair.2) =
            Except.ok finalState at success
          have binderSuccess := binderResult
          obtain ⟨binderValid, binderStages⟩ :=
            registerPatternBinders_sound source scrutineeStage binders
              environment armEnvironment state binderState valid binderSuccess
          cases bodyResult : analyzeStatements arm.body armEnvironment
              binderState with
          | error error =>
              rw [bodyResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨bodyEnvironment, bodyState⟩
              rw [bodyResult] at success
              change analyzeMatchCasesWith source.owner scrutineeStage
                  analyzeStatements rest environment bodyState =
                Except.ok finalState at success
              obtain ⟨bodyValid, bodyStages⟩ :=
                analyzeStatementsSound arm.body armEnvironment binderState
                  bodyEnvironment bodyState binderValid bodyResult
              have tailSuccess : analyzeMatchCasesWith source.owner
                  scrutineeStage analyzeStatements rest environment bodyState =
                    .ok finalState := success
              obtain ⟨finalValid, tailStages⟩ :=
                induction bodyState bodyValid tailSuccess
              refine ⟨finalValid, .cons ?_ tailStages⟩
              apply MatchCaseStages.intro
              · simpa [binders, bindersInPatternResolution_eq] using
                  binderStages
              · exact bodyStages

theorem analyzeOptionalStatementsWith_sound
    (source : TypedSource)
    (analyzeStatement : Frontend.SourceStageAnalysis.Environment → Traversal →
      StatementId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Environment × Traversal))
    (statementSound : ∀ environment state id nextEnvironment nextState,
      TraversalValid source state →
      analyzeStatement environment state id = .ok
        (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementStages source (toSemanticScope environment) id
          (toSemanticScope nextEnvironment))
    (body : Option (List StatementId))
    (environment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzeOptionalStatementsWith analyzeStatement body
      environment state = .ok finalState) :
    TraversalValid source finalState ∧
      match body with
      | none => True
      | some ids => ∃ finalEnvironment : Frontend.SourceStageAnalysis.Environment,
          StatementsStage source (toSemanticScope environment) ids
            (toSemanticScope finalEnvironment) := by
  cases body with
  | none =>
      simp only [analyzeOptionalStatementsWith] at success
      cases success
      exact ⟨valid, trivial⟩
  | some ids =>
      simp only [analyzeOptionalStatementsWith] at success
      cases analyzed : analyzeStatementListWith analyzeStatement ids
          environment state with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨nextEnvironment, nextState⟩
          rw [analyzed] at success
          cases success
          obtain ⟨finalValid, bodyStages⟩ :=
            analyzeStatementListWith_sound source analyzeStatement
              statementSound ids environment nextEnvironment state nextState
              valid analyzed
          exact ⟨finalValid, nextEnvironment, bodyStages⟩

def projectionIndexExpressions : List PlaceProjection → List ExpressionId
  | [] => []
  | .member _ _ :: rest => projectionIndexExpressions rest
  | .index key :: rest => key :: projectionIndexExpressions rest

theorem placeIndexExpressions_eq (place : PlaceResolution) :
    Staging.placeIndexExpressions place =
      projectionIndexExpressions place.projections := by
  unfold Staging.placeIndexExpressions
  induction place.projections with
  | nil => rfl
  | cons projection rest induction =>
      cases projection <;>
        simp [projectionIndexExpressions, induction]

theorem analyzePlaceProjectionsWith_sound
    (source : TypedSource) (scope : StageScope)
    (analyze : Traversal → ExpressionId →
      Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Stage × Traversal))
    (analyzeSound : ∀ state id stage next,
      TraversalValid source state →
      analyze state id = .ok (stage, next) →
      TraversalValid source next ∧
        HasStage source scope id stage.toSemantic)
    (projections : List PlaceProjection)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzePlaceProjectionsWith analyze projections state =
      .ok finalState) :
    TraversalValid source finalState ∧
      ∃ stages,
        ExpressionsHaveStages source scope
          (projectionIndexExpressions projections) stages := by
  induction projections generalizing state with
  | nil =>
      simp only [analyzePlaceProjectionsWith] at success
      cases success
      exact ⟨valid, [], .nil _⟩
  | cons projection rest induction =>
      cases projection with
      | member name index =>
          have tailSuccess : analyzePlaceProjectionsWith analyze rest state =
              .ok finalState := by
            simpa only [analyzePlaceProjectionsWith] using success
          exact induction state valid tailSuccess
      | index key =>
          cases headResult : analyze state key with
          | error error =>
              simp only [analyzePlaceProjectionsWith] at success
              rw [headResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, middleState⟩
              have headSound := analyzeSound state key stage middleState valid
                headResult
              have tailSuccess : analyzePlaceProjectionsWith analyze rest
                  middleState = .ok finalState := by
                simp only [analyzePlaceProjectionsWith] at success
                rw [headResult] at success
                exact success
              obtain ⟨finalValid, stages, tailStages⟩ :=
                induction middleState headSound.1 tailSuccess
              exact ⟨finalValid, stage.toSemantic :: stages,
                .cons headSound.2 tailStages⟩

theorem analyzeForItemsWith_sound
    (source : TypedSource)
    (analyze : Frontend.SourceStageAnalysis.Environment → Traversal →
      ExpressionId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Stage × Traversal))
    (analyzeSound : ∀ environment state id stage next,
      TraversalValid source state →
      analyze environment state id = .ok (stage, next) →
      TraversalValid source next ∧
        HasStage source (toSemanticScope environment) id stage.toSemantic)
    (items : List ForItemForm)
    (environment finalEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzeForItemsWith source analyze items environment state =
      .ok (finalEnvironment, finalState)) :
    TraversalValid source finalState ∧
      ForItemsStage source (toSemanticScope environment) items
        (toSemanticScope finalEnvironment) := by
  induction items generalizing environment state with
  | nil =>
      simp only [analyzeForItemsWith] at success
      cases success
      exact ⟨valid, .nil _⟩
  | cons item rest induction =>
      have unfoldStep :
          analyzeForItemsWith source analyze (item :: rest)
              environment state =
            analyzeForItemWith source analyze item environment state >>=
              fun pair => analyzeForItemsWith source analyze rest pair.1 pair.2 := rfl
      rw [unfoldStep] at success
      cases item with
      | letDecl binder initializer =>
          simp only [analyzeForItemWith] at success
          cases initializer with
          | none =>
              change (registerBinder source.owner environment state binder.id
                  .deferred >>= fun pair => analyzeForItemsWith source analyze
                    rest pair.1 pair.2) =
                .ok (finalEnvironment, finalState) at success
              cases registered : registerBinder source.owner environment state
                  binder.id .deferred with
              | error error =>
                  rw [registered] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨middleEnvironment, middleState⟩
                  rw [registered] at success
                  obtain ⟨middleValid, actual, binderStages⟩ :=
                    registerBinder_sound source environment state middleState
                      binder.id .deferred middleEnvironment valid registered
                  obtain ⟨finalValid, tailStages⟩ :=
                    induction middleEnvironment middleState middleValid success
                  exact ⟨finalValid, .cons (.letUninitialized binderStages)
                    tailStages⟩
          | some value =>
              change ((analyze environment state value >>= fun pair =>
                  registerBinder source.owner environment pair.2 binder.id
                    pair.1) >>= fun pair => analyzeForItemsWith source analyze
                    rest pair.1 pair.2) =
                .ok (finalEnvironment, finalState) at success
              cases analyzed : analyze environment state value with
              | error error =>
                  rw [analyzed] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨stage, expressionState⟩
                  rw [analyzed] at success
                  change (registerBinder source.owner environment
                      expressionState binder.id stage >>= fun pair =>
                        analyzeForItemsWith source analyze rest pair.1 pair.2) =
                    .ok (finalEnvironment, finalState) at success
                  obtain ⟨expressionValid, expressionStages⟩ :=
                    analyzeSound environment state value stage expressionState
                      valid analyzed
                  cases registered : registerBinder source.owner environment
                      expressionState binder.id stage with
                  | error error =>
                      rw [registered] at success
                      cases success
                  | ok pair =>
                      rcases pair with ⟨middleEnvironment, middleState⟩
                      rw [registered] at success
                      obtain ⟨middleValid, actual, binderStages⟩ :=
                        registerBinder_sound source environment expressionState
                          middleState binder.id stage middleEnvironment
                          expressionValid registered
                      obtain ⟨finalValid, tailStages⟩ :=
                        induction middleEnvironment middleState middleValid success
                      exact ⟨finalValid, .cons
                        (.letInitialized expressionStages binderStages)
                        tailStages⟩
      | expression value =>
          simp only [analyzeForItemWith] at success
          cases analyzed : analyze environment state value with
          | error error =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, middleState⟩
              rw [analyzed] at success
              obtain ⟨middleValid, expressionStages⟩ :=
                analyzeSound environment state value stage middleState valid
                  analyzed
              obtain ⟨finalValid, tailStages⟩ :=
                induction environment middleState middleValid success
              exact ⟨finalValid, .cons (.expression expressionStages)
                tailStages⟩
      | assignValue assignment operator value =>
          simp only [analyzeForItemWith] at success
          cases projections : analyzePlaceProjectionsWith
              (analyze environment) assignment.target.projections state with
          | error error =>
              rw [projections] at success
              cases success
          | ok projectionState =>
              rw [projections] at success
              change ((analyze environment projectionState value >>= fun pair =>
                  Except.ok (environment, pair.2)) >>= fun pair =>
                    analyzeForItemsWith source analyze rest pair.1 pair.2) =
                .ok (finalEnvironment, finalState) at success
              obtain ⟨projectionValid, projectionStages,
                  projectionProof⟩ :=
                analyzePlaceProjectionsWith_sound source
                  (toSemanticScope environment) (analyze environment)
                  (analyzeSound environment) assignment.target.projections
                  state projectionState valid projections
              cases analyzed : analyze environment projectionState value with
              | error error =>
                  rw [analyzed] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨stage, middleState⟩
                  rw [analyzed] at success
                  obtain ⟨middleValid, valueStages⟩ :=
                    analyzeSound environment projectionState value stage
                      middleState projectionValid analyzed
                  obtain ⟨finalValid, tailStages⟩ :=
                    induction environment middleState middleValid success
                  exact ⟨finalValid, .cons
                    (.assignValue (by simpa [placeIndexExpressions_eq]
                      using projectionProof) valueStages) tailStages⟩
      | assignBitNot assignment =>
          simp only [analyzeForItemWith] at success
          cases projections : analyzePlaceProjectionsWith
              (analyze environment) assignment.target.projections state with
          | error error =>
              rw [projections] at success
              cases success
          | ok middleState =>
              rw [projections] at success
              obtain ⟨middleValid, projectionStages,
                  projectionProof⟩ :=
                analyzePlaceProjectionsWith_sound source
                  (toSemanticScope environment) (analyze environment)
                  (analyzeSound environment) assignment.target.projections
                  state middleState valid projections
              obtain ⟨finalValid, tailStages⟩ :=
                induction environment middleState middleValid success
              exact ⟨finalValid, .cons
                (.assignBitNot (by simpa [placeIndexExpressions_eq]
                  using projectionProof)) tailStages⟩

theorem except_bind_ok_inv {error : Type} {α β : Type}
    (input : Except error α) (next : α → Except error β) (result : β)
    (success : input >>= next = .ok result) :
    ∃ value, input = .ok value ∧ next value = .ok result := by
  cases input with
  | error problem => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem analyzeExpressionFormWith_sound
    (source : TypedSource) (id : ExpressionId) (node : ExpressionNode)
    (environment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (stage : Frontend.SourceStageAnalysis.Stage)
    (analyzeExpression : Traversal → ExpressionId →
      Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Stage × Traversal))
    (analyzeStatement : Frontend.SourceStageAnalysis.Environment → Traversal →
      StatementId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Environment × Traversal))
    (expressionSound : ∀ state id stage next,
      TraversalValid source state →
      analyzeExpression state id = .ok (stage, next) →
      TraversalValid source next ∧
        HasStage source (toSemanticScope environment) id stage.toSemantic)
    (statementSound : ∀ environment state id nextEnvironment nextState,
      TraversalValid source state →
      analyzeStatement environment state id = .ok
        (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementStages source (toSemanticScope environment) id
          (toSemanticScope nextEnvironment))
    (contains : SourceSemantics.ContainsExpression source id node)
    (valid : TraversalValid source state)
    (success : analyzeExpressionFormWith source id node environment state
      analyzeExpression analyzeStatement = .ok (stage, finalState)) :
    TraversalValid source finalState ∧
      HasStage source (toSemanticScope environment) id stage.toSemantic := by
  cases form : node.form with
  | literal literal =>
      simp only [analyzeExpressionFormWith, form] at success
      cases success
      exact ⟨valid, .literal contains form⟩
  | integerLiteral literal resolution =>
      simp only [analyzeExpressionFormWith, form] at success
      cases success
      exact ⟨valid, .integerLiteral contains form⟩
  | reference name resolution =>
      cases resolution with
      | builtinBoolean value =>
          simp only [analyzeExpressionFormWith, form] at success
          cases success
          exact ⟨valid, .builtinBoolean contains form⟩
      | «local» binder =>
          by_cases owned : binder.owner = source.owner
          · cases lookup : lookupEnvironment? environment binder with
            | none =>
                simp [analyzeExpressionFormWith, form, owned, lookup] at success
            | some result =>
                simp [analyzeExpressionFormWith, form, owned, lookup] at success
                obtain ⟨rfl, rfl⟩ := success
                exact ⟨valid, .local contains form owned
                  (lookupEnvironment?_sound lookup)⟩
          · simp [analyzeExpressionFormWith, form, owned] at success
      | declaration instantiation =>
          simp only [analyzeExpressionFormWith, form] at success
          cases success
          exact ⟨valid, .declaration contains form⟩
      | builtinFunction function =>
          simp only [analyzeExpressionFormWith, form] at success
          cases success
          exact ⟨valid, .builtinFunction contains form⟩
  | group inner =>
      simp only [analyzeExpressionFormWith, form] at success
      obtain ⟨finalValid, innerStage⟩ :=
        expressionSound state inner stage finalState valid success
      exact ⟨finalValid, .group contains form innerStage⟩
  | tuple elements =>
      simp only [analyzeExpressionFormWith, form] at success
      cases analyzed : analyzeExpressionListWith analyzeExpression elements
          state with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨stages, nextState⟩
          rw [analyzed] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, elementStages⟩ :=
            analyzeExpressionListWith_sound source
              (toSemanticScope environment) analyzeExpression expressionSound
              elements state nextState stages valid analyzed
          exact ⟨finalValid, .tuple contains form elementStages
            (join_sound stages)⟩
  | unary operator operand =>
      simp only [analyzeExpressionFormWith, form] at success
      obtain ⟨finalValid, operandStage⟩ :=
        expressionSound state operand stage finalState valid success
      exact ⟨finalValid, .unary contains form operandStage⟩
  | binary left operator right =>
      simp only [analyzeExpressionFormWith, form] at success
      cases leftResult : analyzeExpression state left with
      | error problem =>
          rw [leftResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨leftStage, middleState⟩
          rw [leftResult] at success
          obtain ⟨middleValid, leftStages⟩ :=
            expressionSound state left leftStage middleState valid leftResult
          change (analyzeExpression middleState right >>= fun pair =>
              .ok (Frontend.SourceStageAnalysis.Stage.join
                [leftStage, pair.1], pair.2)) =
            .ok (stage, finalState) at success
          cases rightResult : analyzeExpression middleState right with
          | error problem =>
              rw [rightResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨rightStage, nextState⟩
              rw [rightResult] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, rightStages⟩ :=
                expressionSound middleState right rightStage nextState
                  middleValid rightResult
              exact ⟨finalValid, .binary contains form leftStages rightStages
                (join_sound [leftStage, rightStage])⟩
  | conditional condition thenBranch elseBranch =>
      simp only [analyzeExpressionFormWith, form] at success
      cases conditionResult : analyzeExpression state condition with
      | error problem =>
          rw [conditionResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨conditionStage, conditionState⟩
          rw [conditionResult] at success
          obtain ⟨conditionValid, conditionStages⟩ :=
            expressionSound state condition conditionStage conditionState valid
              conditionResult
          change (analyzeExpression conditionState thenBranch >>= fun pair =>
              analyzeExpression pair.2 elseBranch >>= fun last =>
                .ok (Frontend.SourceStageAnalysis.Stage.join
                  [conditionStage, pair.1, last.1], last.2)) =
            .ok (stage, finalState) at success
          cases thenResult : analyzeExpression conditionState thenBranch with
          | error problem =>
              rw [thenResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨thenStage, thenState⟩
              rw [thenResult] at success
              obtain ⟨thenValid, thenStages⟩ :=
                expressionSound conditionState thenBranch thenStage thenState
                  conditionValid thenResult
              change (analyzeExpression thenState elseBranch >>= fun pair =>
                  .ok (Frontend.SourceStageAnalysis.Stage.join
                    [conditionStage, thenStage, pair.1], pair.2)) =
                .ok (stage, finalState) at success
              cases elseResult : analyzeExpression thenState elseBranch with
              | error problem =>
                  rw [elseResult] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨elseStage, nextState⟩
                  rw [elseResult] at success
                  obtain ⟨rfl, rfl⟩ := success
                  obtain ⟨finalValid, elseStages⟩ :=
                    expressionSound thenState elseBranch elseStage nextState
                      thenValid elseResult
                  exact ⟨finalValid, .conditional contains form conditionStages
                    thenStages elseStages
                    (join_sound [conditionStage, thenStage, elseStage])⟩
  | lambda parameters returnType body =>
      simp only [analyzeExpressionFormWith, form] at success
      cases registered : registerTypedBinders source.owner false parameters
          environment state with
      | error problem =>
          rw [registered] at success
          cases success
      | ok pair =>
          rcases pair with ⟨lambdaEnvironment, binderState⟩
          rw [registered] at success
          change (analyzeStatementListWith analyzeStatement body
              lambdaEnvironment binderState).map
                (fun pair => (Frontend.SourceStageAnalysis.Stage.deferred,
                  pair.2)) =
            .ok (stage, finalState) at success
          obtain ⟨binderValid, _, bindersStage⟩ :=
            registerTypedBinders_sound source false parameters environment
              lambdaEnvironment state binderState valid registered
          cases analyzed : analyzeStatementListWith analyzeStatement body
              lambdaEnvironment binderState with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨finalEnvironment, nextState⟩
              rw [analyzed] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, bodyStages⟩ :=
                analyzeStatementListWith_sound source analyzeStatement
                  statementSound body lambdaEnvironment finalEnvironment
                  binderState nextState binderValid analyzed
              exact ⟨finalValid, .lambda contains form (bindersStage rfl)
                bodyStages⟩
  | call callee arguments resolution =>
      simp only [analyzeExpressionFormWith, form] at success
      cases calleeResult : analyzeExpression state callee with
      | error problem =>
          rw [calleeResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨calleeStage, calleeState⟩
          rw [calleeResult] at success
          obtain ⟨calleeValid, calleeStages⟩ :=
            expressionSound state callee calleeStage calleeState valid
              calleeResult
          cases resolution with
          | declaration instantiation =>
              change (analyzeExpressionListWith analyzeExpression arguments
                  calleeState >>= fun pair =>
                    .ok (directCallStage node instantiation pair.1, pair.2)) =
                .ok (stage, finalState) at success
              cases argumentsResult : analyzeExpressionListWith
                  analyzeExpression arguments calleeState with
              | error problem =>
                  rw [argumentsResult] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨argumentStages, argumentState⟩
                  rw [argumentsResult] at success
                  obtain ⟨rfl, rfl⟩ := success
                  obtain ⟨argumentsValid, argumentsStages⟩ :=
                    analyzeExpressionListWith_sound source
                      (toSemanticScope environment) analyzeExpression
                      expressionSound arguments calleeState argumentState
                      argumentStages calleeValid argumentsResult
                  exact ⟨argumentsValid, .directCall contains form
                    calleeStages argumentsStages
                    (directCallStage_sound node instantiation argumentStages)⟩
          | indirect metadata =>
              change (analyzeExpressionListWith analyzeExpression arguments
                  calleeState >>= fun pair =>
                    .ok (Frontend.SourceStageAnalysis.Stage.deferred, pair.2)) =
                .ok (stage, finalState) at success
              cases argumentsResult : analyzeExpressionListWith
                  analyzeExpression arguments calleeState with
              | error problem =>
                  rw [argumentsResult] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨argumentStages, argumentState⟩
                  rw [argumentsResult] at success
                  obtain ⟨rfl, rfl⟩ := success
                  obtain ⟨argumentsValid, argumentsStages⟩ :=
                    analyzeExpressionListWith_sound source
                      (toSemanticScope environment) analyzeExpression
                      expressionSound arguments calleeState argumentState
                      argumentStages calleeValid argumentsResult
                  exact ⟨argumentsValid, .indirectCall contains form
                    calleeStages argumentsStages⟩
          | builtinFunction function =>
              change (analyzeExpressionListWith analyzeExpression arguments
                  calleeState >>= fun pair =>
                    .ok (Frontend.SourceStageAnalysis.Stage.deferred, pair.2)) =
                .ok (stage, finalState) at success
              cases argumentsResult : analyzeExpressionListWith
                  analyzeExpression arguments calleeState with
              | error problem =>
                  rw [argumentsResult] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨argumentStages, argumentState⟩
                  rw [argumentsResult] at success
                  obtain ⟨rfl, rfl⟩ := success
                  obtain ⟨argumentsValid, argumentsStages⟩ :=
                    analyzeExpressionListWith_sound source
                      (toSemanticScope environment) analyzeExpression
                      expressionSound arguments calleeState argumentState
                      argumentStages calleeValid argumentsResult
                  exact ⟨argumentsValid, .builtinCall contains form
                    calleeStages argumentsStages⟩
  | constructor instantiation arguments =>
      simp only [analyzeExpressionFormWith, form] at success
      cases analyzed : analyzeExpressionListWith analyzeExpression arguments
          state with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨stages, nextState⟩
          rw [analyzed] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, argumentStages⟩ :=
            analyzeExpressionListWith_sound source
              (toSemanticScope environment) analyzeExpression expressionSound
              arguments state nextState stages valid analyzed
          exact ⟨finalValid, .constructor contains form argumentStages⟩
  | member base name index =>
      simp only [analyzeExpressionFormWith, form] at success
      cases analyzed : analyzeExpression state base with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨baseStage, nextState⟩
          rw [analyzed] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, baseStages⟩ :=
            expressionSound state base baseStage nextState valid analyzed
          exact ⟨finalValid, .member contains form baseStages⟩
  | proxy inner =>
      simp only [analyzeExpressionFormWith, form] at success
      cases success
      exact ⟨valid, .proxy contains form⟩
  | index base key =>
      simp only [analyzeExpressionFormWith, form] at success
      cases baseResult : analyzeExpression state base with
      | error problem =>
          rw [baseResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨baseStage, middleState⟩
          rw [baseResult] at success
          obtain ⟨middleValid, baseStages⟩ :=
            expressionSound state base baseStage middleState valid baseResult
          change (analyzeExpression middleState key >>= fun pair =>
              .ok (Frontend.SourceStageAnalysis.Stage.deferred, pair.2)) =
            .ok (stage, finalState) at success
          cases keyResult : analyzeExpression middleState key with
          | error problem =>
              rw [keyResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨keyStage, nextState⟩
              rw [keyResult] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, keyStages⟩ :=
                expressionSound middleState key keyStage nextState
                  middleValid keyResult
              exact ⟨finalValid, .index contains form baseStages keyStages⟩

theorem analyzeStatementFormWith_sound
    (source : TypedSource) (id : StatementId) (node : StatementNode)
    (environment finalEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (analyzeExpression : Frontend.SourceStageAnalysis.Environment → Traversal →
      ExpressionId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Stage × Traversal))
    (analyzeStatement : Frontend.SourceStageAnalysis.Environment → Traversal →
      StatementId → Except Frontend.SourceStageAnalysis.Error
        (Frontend.SourceStageAnalysis.Environment × Traversal))
    (expressionSound : ∀ environment state id stage next,
      TraversalValid source state →
      analyzeExpression environment state id = .ok (stage, next) →
      TraversalValid source next ∧
        HasStage source (toSemanticScope environment) id stage.toSemantic)
    (statementSound : ∀ environment state id nextEnvironment nextState,
      TraversalValid source state →
      analyzeStatement environment state id = .ok
        (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementStages source (toSemanticScope environment) id
          (toSemanticScope nextEnvironment))
    (contains : SourceSemantics.ContainsStatement source id node)
    (valid : TraversalValid source state)
    (success : analyzeStatementFormWith source node environment state
      analyzeExpression analyzeStatement = .ok (finalEnvironment, finalState)) :
    TraversalValid source finalState ∧
      StatementStages source (toSemanticScope environment) id
        (toSemanticScope finalEnvironment) := by
  cases form : node.form with
  | letDecl binder initializer =>
      simp only [analyzeStatementFormWith, form] at success
      cases initializer with
      | none =>
          change registerBinder source.owner environment state binder.id
              .deferred = .ok (finalEnvironment, finalState) at success
          obtain ⟨finalValid, actual, binderStages⟩ :=
            registerBinder_sound source environment state finalState binder.id
              .deferred finalEnvironment valid success
          exact ⟨finalValid, .letUninitialized contains form binderStages⟩
      | some initializer =>
          change (analyzeExpression environment state initializer >>= fun pair =>
              registerBinder source.owner environment pair.2 binder.id
                pair.1) = .ok (finalEnvironment, finalState) at success
          cases analyzed : analyzeExpression environment state initializer with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, expressionState⟩
              rw [analyzed] at success
              obtain ⟨expressionValid, initializerStages⟩ :=
                expressionSound environment state initializer stage
                  expressionState valid analyzed
              obtain ⟨finalValid, actual, binderStages⟩ :=
                registerBinder_sound source environment expressionState
                  finalState binder.id stage finalEnvironment expressionValid
                  success
              exact ⟨finalValid, .letInitialized contains form
                initializerStages binderStages⟩
  | returnStmt value =>
      cases value with
      | none =>
          simp [analyzeStatementFormWith, form] at success
          obtain ⟨rfl, rfl⟩ := success
          exact ⟨valid, .returnUnit contains form⟩
      | some value =>
          simp only [analyzeStatementFormWith, form] at success
          cases analyzed : analyzeExpression environment state value with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, nextState⟩
              rw [analyzed] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, valueStages⟩ :=
                expressionSound environment state value stage nextState valid
                  analyzed
              exact ⟨finalValid, .returnValue contains form valueStages⟩
  | expression expression semicolon =>
      simp only [analyzeStatementFormWith, form] at success
      cases analyzed : analyzeExpression environment state expression with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨stage, nextState⟩
          rw [analyzed] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, expressionStages⟩ :=
            expressionSound environment state expression stage nextState valid
              analyzed
          exact ⟨finalValid, .expression contains form expressionStages⟩
  | assignValue assignment operator value =>
      simp only [analyzeStatementFormWith, form] at success
      cases projections : analyzePlaceProjectionsWith
          (analyzeExpression environment) assignment.target.projections state with
      | error problem =>
          rw [projections] at success
          cases success
      | ok projectionState =>
          rw [projections] at success
          obtain ⟨projectionValid, projectionStages, projectionProof⟩ :=
            analyzePlaceProjectionsWith_sound source
              (toSemanticScope environment) (analyzeExpression environment)
              (expressionSound environment) assignment.target.projections
              state projectionState valid projections
          change (analyzeExpression environment projectionState value >>= fun pair =>
              .ok (environment, pair.2)) =
            .ok (finalEnvironment, finalState) at success
          cases analyzed : analyzeExpression environment projectionState value with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, nextState⟩
              rw [analyzed] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, valueStages⟩ :=
                expressionSound environment projectionState value stage
                  nextState projectionValid analyzed
              exact ⟨finalValid, .assignValue contains form
                (by simpa [placeIndexExpressions_eq] using projectionProof)
                valueStages⟩
  | assignBitNot assignment =>
      simp only [analyzeStatementFormWith, form] at success
      cases projections : analyzePlaceProjectionsWith
          (analyzeExpression environment) assignment.target.projections state with
      | error problem =>
          rw [projections] at success
          cases success
      | ok nextState =>
          rw [projections] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, projectionStages, projectionProof⟩ :=
            analyzePlaceProjectionsWith_sound source
              (toSemanticScope environment) (analyzeExpression environment)
              (expressionSound environment) assignment.target.projections
              state finalState valid projections
          exact ⟨finalValid, .assignBitNot contains form
            (by simpa [placeIndexExpressions_eq] using projectionProof)⟩
  | ifThen condition thenBody elseBody =>
      simp only [analyzeStatementFormWith, form] at success
      cases conditionResult : analyzeExpression environment state condition with
      | error problem =>
          rw [conditionResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨conditionStage, conditionState⟩
          rw [conditionResult] at success
          obtain ⟨conditionValid, conditionStages⟩ :=
            expressionSound environment state condition conditionStage
              conditionState valid conditionResult
          change (analyzeStatementListWith analyzeStatement thenBody
              environment conditionState >>= fun pair =>
                analyzeOptionalStatementsWith analyzeStatement elseBody
                  environment pair.2 >>= fun next =>
                    .ok (environment, next)) =
            .ok (finalEnvironment, finalState) at success
          cases thenResult : analyzeStatementListWith analyzeStatement thenBody
              environment conditionState with
          | error problem =>
              rw [thenResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨thenEnvironment, thenState⟩
              rw [thenResult] at success
              obtain ⟨thenValid, thenStages⟩ :=
                analyzeStatementListWith_sound source analyzeStatement
                  statementSound thenBody environment thenEnvironment
                  conditionState thenState conditionValid thenResult
              change (analyzeOptionalStatementsWith analyzeStatement elseBody
                  environment thenState >>= fun next =>
                    .ok (environment, next)) =
                .ok (finalEnvironment, finalState) at success
              cases elseResult : analyzeOptionalStatementsWith analyzeStatement
                  elseBody environment thenState with
              | error problem =>
                  rw [elseResult] at success
                  cases success
              | ok nextState =>
                  rw [elseResult] at success
                  obtain ⟨rfl, rfl⟩ := success
                  obtain ⟨finalValid, elseStages⟩ :=
                    analyzeOptionalStatementsWith_sound source
                      analyzeStatement statementSound elseBody environment
                      thenState finalState thenValid elseResult
                  cases elseBody with
                  | none =>
                      exact ⟨finalValid, .ifWithoutElse contains form
                        conditionStages thenStages⟩
                  | some body =>
                      rcases elseStages with ⟨elseEnvironment, stages⟩
                      exact ⟨finalValid, .ifWithElse contains form
                        conditionStages thenStages stages⟩
  | block body =>
      simp only [analyzeStatementFormWith, form] at success
      cases analyzed : analyzeStatementListWith analyzeStatement body
          environment state with
      | error problem =>
          rw [analyzed] at success
          cases success
      | ok pair =>
          rcases pair with ⟨bodyEnvironment, nextState⟩
          rw [analyzed] at success
          obtain ⟨rfl, rfl⟩ := success
          obtain ⟨finalValid, bodyStages⟩ :=
            analyzeStatementListWith_sound source analyzeStatement
              statementSound body environment bodyEnvironment state nextState
              valid analyzed
          exact ⟨finalValid, .block contains form bodyStages⟩
  | matchWith resolution =>
      simp only [analyzeStatementFormWith, form] at success
      cases scrutineeResult : analyzeExpression environment state
          resolution.scrutinee with
      | error problem =>
          rw [scrutineeResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨scrutineeStage, scrutineeState⟩
          rw [scrutineeResult] at success
          obtain ⟨scrutineeValid, scrutineeStages⟩ :=
            expressionSound environment state resolution.scrutinee
              scrutineeStage scrutineeState valid scrutineeResult
          change (registerBinder source.owner environment scrutineeState
              resolution.hiddenScrutinee scrutineeStage >>= fun pair =>
                analyzeMatchCasesWith source.owner scrutineeStage
                  (analyzeStatementListWith analyzeStatement)
                  resolution.cases environment pair.2 >>= fun casesState =>
                    analyzeOptionalStatementsWith analyzeStatement
                      resolution.defaultBody environment casesState >>=
                      fun next => .ok (environment, next)) =
            .ok (finalEnvironment, finalState) at success
          cases binderResult : registerBinder source.owner environment
              scrutineeState resolution.hiddenScrutinee scrutineeStage with
          | error problem =>
              rw [binderResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨hiddenEnvironment, hiddenState⟩
              rw [binderResult] at success
              obtain ⟨hiddenValid, hiddenStage, hiddenBinder⟩ :=
                registerBinder_sound source environment scrutineeState
                  hiddenState resolution.hiddenScrutinee scrutineeStage
                  hiddenEnvironment scrutineeValid binderResult
              change (analyzeMatchCasesWith source.owner scrutineeStage
                  (analyzeStatementListWith analyzeStatement)
                  resolution.cases environment hiddenState >>=
                    fun casesState => analyzeOptionalStatementsWith
                      analyzeStatement resolution.defaultBody environment
                      casesState >>= fun next => .ok (environment, next)) =
                .ok (finalEnvironment, finalState) at success
              cases casesResult : analyzeMatchCasesWith source.owner
                  scrutineeStage (analyzeStatementListWith analyzeStatement)
                  resolution.cases environment hiddenState with
              | error problem =>
                  rw [casesResult] at success
                  cases success
              | ok casesState =>
                  rw [casesResult] at success
                  obtain ⟨casesValid, caseStages⟩ :=
                    analyzeMatchCasesWith_sound source scrutineeStage
                      (analyzeStatementListWith analyzeStatement)
                      (fun ids env state nextEnv nextState valid success =>
                        analyzeStatementListWith_sound source
                          analyzeStatement statementSound ids env nextEnv state
                          nextState valid success)
                      resolution.cases environment hiddenState casesState
                      hiddenValid casesResult
                  change (analyzeOptionalStatementsWith analyzeStatement
                      resolution.defaultBody environment casesState >>=
                        fun next => .ok (environment, next)) =
                    .ok (finalEnvironment, finalState) at success
                  cases defaultResult : analyzeOptionalStatementsWith
                      analyzeStatement resolution.defaultBody environment
                      casesState with
                  | error problem =>
                      rw [defaultResult] at success
                      cases success
                  | ok nextState =>
                      rw [defaultResult] at success
                      obtain ⟨rfl, rfl⟩ := success
                      obtain ⟨finalValid, defaultStages⟩ :=
                        analyzeOptionalStatementsWith_sound source
                          analyzeStatement statementSound
                          resolution.defaultBody environment casesState
                          finalState casesValid defaultResult
                      split at defaultStages
                      · exact ⟨finalValid, .matchWithoutDefault contains form
                          (by assumption) scrutineeStages hiddenBinder
                          caseStages⟩
                      · rcases defaultStages with
                          ⟨defaultEnvironment, stages⟩
                        exact ⟨finalValid, .matchWithDefault contains form
                          (by assumption) scrutineeStages hiddenBinder
                          caseStages stages⟩
  | forLoop initializer condition post body =>
      simp only [analyzeStatementFormWith, form] at success
      cases initializerResult : analyzeForItemsWith source analyzeExpression
          initializer environment state with
      | error problem =>
          rw [initializerResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨loopEnvironment, initializerState⟩
          rw [initializerResult] at success
          obtain ⟨initializerValid, initializerStages⟩ :=
            analyzeForItemsWith_sound source analyzeExpression expressionSound
              initializer environment loopEnvironment state initializerState
              valid initializerResult
          change (analyzeExpression loopEnvironment initializerState condition >>=
              fun pair => analyzeStatementListWith analyzeStatement body
                loopEnvironment pair.2 >>= fun bodyPair =>
                  analyzeForItemsWith source analyzeExpression post
                    loopEnvironment bodyPair.2 >>= fun finalPair =>
                      .ok (environment, finalPair.2)) =
            .ok (finalEnvironment, finalState) at success
          cases conditionResult : analyzeExpression loopEnvironment
              initializerState condition with
          | error problem =>
              rw [conditionResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨conditionStage, conditionState⟩
              rw [conditionResult] at success
              obtain ⟨conditionValid, conditionStages⟩ :=
                expressionSound loopEnvironment initializerState condition
                  conditionStage conditionState initializerValid
                  conditionResult
              change (analyzeStatementListWith analyzeStatement body
                  loopEnvironment conditionState >>= fun bodyPair =>
                    analyzeForItemsWith source analyzeExpression post
                      loopEnvironment bodyPair.2 >>= fun finalPair =>
                        .ok (environment, finalPair.2)) =
                .ok (finalEnvironment, finalState) at success
              cases bodyResult : analyzeStatementListWith analyzeStatement body
                  loopEnvironment conditionState with
              | error problem =>
                  rw [bodyResult] at success
                  cases success
              | ok pair =>
                  rcases pair with ⟨bodyEnvironment, bodyState⟩
                  rw [bodyResult] at success
                  obtain ⟨bodyValid, bodyStages⟩ :=
                    analyzeStatementListWith_sound source analyzeStatement
                      statementSound body loopEnvironment bodyEnvironment
                      conditionState bodyState conditionValid bodyResult
                  change (analyzeForItemsWith source analyzeExpression post
                      loopEnvironment bodyState >>= fun pair =>
                        .ok (environment, pair.2)) =
                    .ok (finalEnvironment, finalState) at success
                  cases postResult : analyzeForItemsWith source
                      analyzeExpression post loopEnvironment bodyState with
                  | error problem =>
                      rw [postResult] at success
                      cases success
                  | ok pair =>
                      rcases pair with ⟨postEnvironment, postState⟩
                      rw [postResult] at success
                      obtain ⟨rfl, rfl⟩ := success
                      obtain ⟨finalValid, postStages⟩ :=
                        analyzeForItemsWith_sound source analyzeExpression
                          expressionSound post loopEnvironment postEnvironment
                          bodyState postState bodyValid postResult
                      exact ⟨finalValid, .forLoop contains form
                        initializerStages conditionStages bodyStages
                        postStages⟩
  | whileLoop condition body =>
      simp only [analyzeStatementFormWith, form] at success
      cases conditionResult : analyzeExpression environment state condition with
      | error problem =>
          rw [conditionResult] at success
          cases success
      | ok pair =>
          rcases pair with ⟨conditionStage, conditionState⟩
          rw [conditionResult] at success
          obtain ⟨conditionValid, conditionStages⟩ :=
            expressionSound environment state condition conditionStage
              conditionState valid conditionResult
          change (analyzeStatementListWith analyzeStatement body environment
              conditionState >>= fun pair => .ok (environment, pair.2)) =
            .ok (finalEnvironment, finalState) at success
          cases bodyResult : analyzeStatementListWith analyzeStatement body
              environment conditionState with
          | error problem =>
              rw [bodyResult] at success
              cases success
          | ok pair =>
              rcases pair with ⟨bodyEnvironment, nextState⟩
              rw [bodyResult] at success
              obtain ⟨rfl, rfl⟩ := success
              obtain ⟨finalValid, bodyStages⟩ :=
                analyzeStatementListWith_sound source analyzeStatement
                  statementSound body environment bodyEnvironment
                  conditionState nextState conditionValid bodyResult
              exact ⟨finalValid, .whileLoop contains form conditionStages
                bodyStages⟩
  | breakStmt =>
      simp [analyzeStatementFormWith, form] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨valid, .breakStmt contains form⟩
  | continueStmt =>
      simp [analyzeStatementFormWith, form] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨valid, .continueStmt contains form⟩

/-- Mutual fuel induction: every successful recursive classification follows
the corresponding independent expression or statement staging derivation. -/
theorem analyzeFuel_sound (source : TypedSource) (fuel : Nat) :
    (∀ environment state id stage nextState,
      TraversalValid source state →
      analyzeExpressionFuel source fuel environment state id =
        .ok (stage, nextState) →
      TraversalValid source nextState ∧
        HasStage source (toSemanticScope environment) id stage.toSemantic) ∧
    (∀ environment state id nextEnvironment nextState,
      TraversalValid source state →
      analyzeStatementFuel source fuel environment state id =
        .ok (nextEnvironment, nextState) →
      TraversalValid source nextState ∧
        StatementStages source (toSemanticScope environment) id
          (toSemanticScope nextEnvironment)) := by
  induction fuel with
  | zero =>
      constructor
      · intro environment state id stage nextState valid success
        simp [analyzeExpressionFuel] at success
      · intro environment state id nextEnvironment nextState valid success
        simp [analyzeStatementFuel] at success
  | succ fuel induction =>
      rcases induction with ⟨expressionIH, statementIH⟩
      constructor
      · intro environment state id stage nextState valid success
        simp only [analyzeExpressionFuel] at success
        cases entered : enterOccurrence state id.occurrence with
        | error problem =>
            rw [entered] at success
            cases success
        | ok enteredState =>
            rw [entered] at success
            have enteredValid := enterOccurrence_valid valid entered
            cases looked : lookupExpression source id with
            | error problem =>
                rw [looked] at success
                cases success
            | ok node =>
                rw [looked] at success
                have contains := lookupExpression_sound looked
                change (analyzeExpressionFormWith source id node environment
                    enteredState (analyzeExpressionFuel source fuel environment)
                    (analyzeStatementFuel source fuel) >>= fun pair =>
                      recordExpressionStage pair.2 id pair.1 >>=
                        fun recordedState =>
                          leaveOccurrence recordedState id.occurrence >>=
                            fun finalState => .ok (pair.1, finalState)) =
                  .ok (stage, nextState) at success
                cases analyzed : analyzeExpressionFormWith source id node
                    environment enteredState
                    (analyzeExpressionFuel source fuel environment)
                    (analyzeStatementFuel source fuel) with
                | error problem =>
                    rw [analyzed] at success
                    cases success
                | ok pair =>
                    rcases pair with ⟨computedStage, formState⟩
                    rw [analyzed] at success
                    obtain ⟨formValid, expressionStages⟩ :=
                      analyzeExpressionFormWith_sound source id node
                        environment enteredState formState computedStage
                        (analyzeExpressionFuel source fuel environment)
                        (analyzeStatementFuel source fuel)
                        (expressionIH environment)
                        statementIH contains enteredValid analyzed
                    change (recordExpressionStage formState id computedStage >>=
                        fun recordedState =>
                          leaveOccurrence recordedState id.occurrence >>=
                            fun finalState => .ok (computedStage, finalState)) =
                      .ok (stage, nextState) at success
                    cases recorded : recordExpressionStage formState id
                        computedStage with
                    | error problem =>
                        rw [recorded] at success
                        cases success
                    | ok recordedState =>
                        rw [recorded] at success
                        have recordedValid :=
                          recordExpressionStage_valid formValid recorded
                        change (leaveOccurrence recordedState id.occurrence >>=
                            fun finalState => .ok (computedStage, finalState)) =
                          .ok (stage, nextState) at success
                        cases left : leaveOccurrence recordedState
                            id.occurrence with
                        | error problem =>
                            rw [left] at success
                            cases success
                        | ok finalState =>
                            rw [left] at success
                            obtain ⟨rfl, rfl⟩ := success
                            exact ⟨leaveOccurrence_valid recordedValid left,
                              expressionStages⟩
      · intro environment state id nextEnvironment nextState valid success
        simp only [analyzeStatementFuel] at success
        cases entered : enterOccurrence state id.occurrence with
        | error problem =>
            rw [entered] at success
            cases success
        | ok enteredState =>
            rw [entered] at success
            have enteredValid := enterOccurrence_valid valid entered
            cases looked : lookupStatement source id with
            | error problem =>
                rw [looked] at success
                cases success
            | ok node =>
                rw [looked] at success
                have contains := lookupStatement_sound looked
                change (analyzeStatementFormWith source node environment
                    enteredState (analyzeExpressionFuel source fuel)
                    (analyzeStatementFuel source fuel) >>= fun pair =>
                      leaveOccurrence pair.2 id.occurrence >>= fun finalState =>
                        .ok (pair.1, finalState)) =
                  .ok (nextEnvironment, nextState) at success
                cases analyzed : analyzeStatementFormWith source node
                    environment enteredState (analyzeExpressionFuel source fuel)
                    (analyzeStatementFuel source fuel) with
                | error problem =>
                    rw [analyzed] at success
                    cases success
                | ok pair =>
                    rcases pair with ⟨formEnvironment, formState⟩
                    rw [analyzed] at success
                    obtain ⟨formValid, statementStages⟩ :=
                      analyzeStatementFormWith_sound source id node environment
                        formEnvironment enteredState formState
                        (analyzeExpressionFuel source fuel)
                        (analyzeStatementFuel source fuel)
                        expressionIH statementIH contains enteredValid analyzed
                    change (leaveOccurrence formState id.occurrence >>=
                        fun finalState => .ok (formEnvironment, finalState)) =
                      .ok (nextEnvironment, nextState) at success
                    cases left : leaveOccurrence formState id.occurrence with
                    | error problem =>
                        rw [left] at success
                        cases success
                    | ok finalState =>
                        rw [left] at success
                        obtain ⟨rfl, rfl⟩ := success
                        exact ⟨leaveOccurrence_valid formValid left,
                          statementStages⟩

theorem analyzeRoots_sound (source : TypedSource) (fuel : Nat)
    (roots : List NodeId)
    (environment finalEnvironment : Frontend.SourceStageAnalysis.Environment)
    (state finalState : Traversal)
    (valid : TraversalValid source state)
    (success : analyzeRoots source fuel roots environment state =
      .ok (finalEnvironment, finalState)) :
    TraversalValid source finalState ∧
      RootsStage source (toSemanticScope environment) roots
        (toSemanticScope finalEnvironment) := by
  induction roots generalizing environment state with
  | nil =>
      simp only [analyzeRoots] at success
      cases success
      exact ⟨valid, .nil _⟩
  | cons root rest induction =>
      cases root with
      | expression id =>
          simp only [analyzeRoots] at success
          cases analyzed : analyzeExpressionFuel source fuel environment state
              id with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨stage, middleState⟩
              rw [analyzed] at success
              obtain ⟨middleValid, expressionStages⟩ :=
                (analyzeFuel_sound source fuel).1 environment state id stage
                  middleState valid analyzed
              obtain ⟨finalValid, tailStages⟩ :=
                induction environment middleState middleValid success
              exact ⟨finalValid, .cons (.expression expressionStages)
                tailStages⟩
      | statement id =>
          simp only [analyzeRoots] at success
          cases analyzed : analyzeStatementFuel source fuel environment state
              id with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨middleEnvironment, middleState⟩
              rw [analyzed] at success
              obtain ⟨middleValid, statementStages⟩ :=
                (analyzeFuel_sound source fuel).2 environment state id
                  middleEnvironment middleState valid analyzed
              obtain ⟨finalValid, tailStages⟩ :=
                induction middleEnvironment middleState middleValid success
              exact ⟨finalValid, .cons (.statement statementStages)
                tailStages⟩

/-- Whole-function soundness, assuming the independent structural properties
supplied by successful source checking. -/
theorem analyzeFunction_success_hasStages_of_wellFormed
    (function : CheckedFunction) (analysis : Analysis)
    (graphClosed : SourceSemantics.OccurrenceGraphClosed function.typedBody)
    (localIdentities :
      SourceSemantics.LocalIdentityOwnership function.typedBody)
    (success : analyzeFunction function = .ok analysis) :
    FunctionHasStages function := by
  let source := function.typedBody
  have owner : source.owner = function.declaration :=
    (analyzeFunction_success_certificate function analysis success).sourceOwner
  let initial : Traversal := {
    mutableBinders := source.nodes.flatMap mutableBindersInNode
  }
  have initialValid : TraversalValid source initial := rfl
  let force := function.returnComptime ||
    typeIsComptimeOnly function.inferredBodyType
  have ownerDirect : function.typedBody.owner = function.declaration := owner
  unfold analyzeFunction at success
  simp [ownerDirect] at success
  cases validated : validateNodeTable function.declaration []
      function.typedBody.nodes with
  | error problem =>
      rw [validated] at success
      cases success
  | ok _ =>
      rw [validated] at success
      cases registered : registerTypedBinders function.declaration
          (function.returnComptime ||
            typeIsComptimeOnly function.inferredBodyType)
          function.typedBody.inputs []
          { mutableBinders := function.typedBody.nodes.flatMap
              mutableBindersInNode } with
      | error problem =>
          rw [registered] at success
          cases success
      | ok pair =>
          rcases pair with ⟨inputEnvironment, binderState⟩
          rw [registered] at success
          have registeredSource : registerTypedBinders source.owner force
              source.inputs [] initial = .ok (inputEnvironment, binderState) := by
            simpa [source, force, initial, ownerDirect] using registered
          obtain ⟨binderValid, forcedBinders, ordinaryBinders⟩ :=
            registerTypedBinders_sound source force source.inputs []
              inputEnvironment initial binderState initialValid
              registeredSource
          change (analyzeRoots source (source.nodes.length + 1)
              source.roots inputEnvironment binderState >>= fun pair =>
                match firstUnvisited? pair.2 source.nodes with
                | some occurrence => .error (.unreachableNode occurrence)
                | none => .ok {
                    expressions := pair.2.expressions
                    binders := pair.2.binders
                  }) = .ok analysis at success
          cases analyzed : analyzeRoots source (source.nodes.length + 1)
              source.roots inputEnvironment binderState with
          | error problem =>
              rw [analyzed] at success
              cases success
          | ok pair =>
              rcases pair with ⟨finalEnvironment, finalState⟩
              rw [analyzed] at success
              obtain ⟨_, rootsStage⟩ :=
                analyzeRoots_sound source (source.nodes.length + 1)
                  source.roots inputEnvironment finalEnvironment binderState
                  finalState binderValid analyzed
              have inputsStage : FunctionInputsStage source
                  function.returnComptime function.inferredBodyType
                  (toSemanticScope inputEnvironment) := by
                by_cases forced : force = true
                · apply FunctionInputsStage.forced
                  · have enabled : function.returnComptime = true ∨
                        typeIsComptimeOnly function.inferredBodyType = true := by
                      simpa [force, Bool.or_eq_true] using forced
                    rcases enabled with marked | stageOnly
                    · exact Or.inl marked
                    · exact Or.inr
                        ((Frontend.SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff
                          function.inferredBodyType).mp stageOnly)
                  · exact forcedBinders forced
                · have ordinary : force = false := Bool.eq_false_iff.mpr forced
                  have noForce : function.returnComptime = false ∧
                      typeIsComptimeOnly function.inferredBodyType = false := by
                    cases marked : function.returnComptime <;>
                      cases stageOnly : typeIsComptimeOnly
                        function.inferredBodyType <;>
                      simp [force, marked, stageOnly] at ordinary ⊢
                  apply FunctionInputsStage.ordinary
                  · exact noForce.1
                  · intro stageOnly
                    have onlyType : typeIsComptimeOnly
                        function.inferredBodyType = true :=
                      (Frontend.SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff
                        function.inferredBodyType).mpr stageOnly
                    rw [noForce.2] at onlyType
                    cases onlyType
                  · exact ordinaryBinders ordinary
              exact .intro owner graphClosed localIdentities inputsStage
                rootsStage

/-- A checked body that is successfully classified has the complete
independent staging derivation; source checking supplies structural evidence. -/
theorem checkFunctionBody_analysis_success_hasStages
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {function : CheckedFunction}
    (checked : checkFunctionBody environment signatures signature fuel =
      .ok function)
    {analysis : Analysis}
    (analyzed : analyzeFunction function = .ok analysis) :
    FunctionHasStages function :=
  analyzeFunction_success_hasStages_of_wellFormed function analysis
    (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed
      checked)
    (SourceInferenceSoundness.checkFunctionBody_success_localIdentityOwnership
      checked)
    analyzed

end Solcore.SourceSemantics.SourceStageAnalysisSoundness
