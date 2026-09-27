import Solcore.Frontend.SourceInference.Expression
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.Frontend.SourceInference.StateProperties
import Solcore.Frontend.ProgramSignatureFormationProperties
import Solcore.TypeSystem.InferenceProperties

/-! Declaration-scoped state preservation for source inference traversals. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Solcore.Frontend.SourceInference.Detail

open TypeSystem

/-- Module-local name filtering never invents function signatures outside
the whole-program catalog. -/
theorem localFunctionsNamed_subset_catalog (context : Context) (name : String) :
    localFunctionsNamed context name ⊆ context.signatures.functions := by
  intro signature member
  exact (List.mem_filter.mp member).1

/-- Resolving visible declarations back to function signatures only retains
entries found in the whole-program function catalog. -/
theorem signaturesForDeclarations_subset_catalog (context : Context)
    (declarations : List ProgramDeclaration) :
    signaturesForDeclarations context declarations ⊆
      context.signatures.functions := by
  intro signature member
  simp only [signaturesForDeclarations, List.mem_filterMap] at member
  obtain ⟨declaration, _, found⟩ := member
  exact List.mem_of_find?_eq_some found

/-- Every successful unqualified function lookup returns only cataloged
function signatures, whether it chose the local tier or imported visibility. -/
theorem functionsNamed_success_subset_catalog
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    (success : functionsNamed context name = .ok candidates) :
    candidates ⊆ context.signatures.functions := by
  by_cases localEmpty : localFunctionsNamed context name = []
  · cases imported : buildProgramImports context.environment
      context.scope.currentModule with
    | error errors =>
        simp [functionsNamed, localEmpty, imported] at success
    | ok visibility =>
        simp [functionsNamed, localEmpty, imported] at success
        subst candidates
        exact signaturesForDeclarations_subset_catalog context
          (visibility.valuesNamed name)
  · simp [functionsNamed, localEmpty] at success
    subst candidates
    exact localFunctionsNamed_subset_catalog context name

/-- A successful qualified lookup which resolves to a concrete candidate list
returns only signatures found in the whole-program function catalog.  A known
namespace with no matching value is represented by the empty subset. -/
theorem qualifiedFunctionsNamed_success_subset_catalog
    {context : Context} {namespacePath : List String} {name : String}
    {candidates : List ProgramFunctionSignature}
    (success : qualifiedFunctionsNamed context namespacePath name =
      .ok (some candidates)) :
    candidates ⊆ context.signatures.functions := by
  cases imported : buildProgramImports context.environment
      context.scope.currentModule with
  | error errors =>
      simp [qualifiedFunctionsNamed, imported] at success
  | ok visibility =>
      cases root : visibility.hasNamespaceRoot namespacePath with
      | false =>
          simp [qualifiedFunctionsNamed, imported, root] at success
      | true =>
          cases targets : visibility.namespacePathTargets namespacePath with
          | nil =>
              simp [qualifiedFunctionsNamed, imported, root, targets]
                at success
              subst candidates
              simp
          | cons target rest =>
              cases rest with
              | nil =>
                  simp [qualifiedFunctionsNamed, imported, root, targets]
                    at success
                  subst candidates
                  exact signaturesForDeclarations_subset_catalog context
                    (visibility.valuesInNamespacePathNamed namespacePath name)
              | cons second tail =>
                  simp [qualifiedFunctionsNamed, imported, root, targets]
                    at success

private theorem plannedCoercionPath_isValid_cons_iff
    (source target : Ty) (step : PlannedCoercionStep)
    (rest : List PlannedCoercionStep) :
    PlannedCoercionPath.isValid source target (step :: rest) = true ↔
      step.source = source ∧
        PlannedCoercionPath.isValid step.target target rest = true := by
  cases rest <;>
    simp [PlannedCoercionPath.isValid, Bool.and_eq_true, beq_iff_eq]

private theorem plannedCoercionPath_isValid_append
    {source current : Ty} {steps : List PlannedCoercionStep}
    (valid : PlannedCoercionPath.isValid source current steps = true)
    (step : PlannedCoercionStep) (source_eq : step.source = current) :
    PlannedCoercionPath.isValid source step.target (steps ++ [step]) = true := by
  induction steps generalizing source with
  | nil =>
      simp [PlannedCoercionPath.isValid, beq_iff_eq] at valid ⊢
      exact source_eq.trans valid.symm
  | cons head rest induction =>
      have parts := (plannedCoercionPath_isValid_cons_iff
        source current head rest).mp valid
      apply (plannedCoercionPath_isValid_cons_iff source step.target head
        (rest ++ [step])).mpr
      exact ⟨parts.1, induction parts.2⟩

private theorem coercionRuleEdge?_some_source
    {trait : Resolved.DeclarationId} {source : Ty}
    {rule : ProgramImplRule} {edge : CoercionEdge}
    (success : coercionRuleEdge? trait source rule = some edge) :
    edge.source = source := by
  by_cases traitMismatch :
      (rule.head.trait != ProgramTraitId.declaration trait) = true
  · simp [coercionRuleEdge?, traitMismatch] at success
  · simp only [coercionRuleEdge?, traitMismatch, ↓reduceIte] at success
    cases arguments : (TypedTraitResolution.freshenRuleFor rule {
        trait := ProgramTraitId.declaration trait
        subject := source
        arguments := [source]
      }).head.arguments with
    | nil => simp [arguments, bind, Option.bind] at success
    | cons target rest =>
        cases rest with
        | cons second tail => simp [arguments, bind, Option.bind] at success
        | nil =>
            simp only [arguments, bind, Option.bind] at success
            cases unified : (Unification.unify [{
                left := (TypedTraitResolution.freshenRuleFor rule {
                  trait := ProgramTraitId.declaration trait
                  subject := source
                  arguments := [source]
                }).head.subject
                right := source
              }]).toOption with
            | none => simp [unified] at success
            | some substitution =>
                simp only [unified, Option.bind_some] at success
                by_cases blocked :
                    substitution.domain.any source.freeVariables.contains = true
                · simp [blocked] at success
                · by_cases ground :
                      isGroundCoercionTarget
                        (substitution.apply target) = true
                  · simp [blocked, ground] at success
                    subst edge
                    rfl
                  · simp [blocked, ground] at success

private theorem assumptionCoercionEdges_member_source
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈ assumptionCoercionEdges context state trait source) :
    edge.source = source := by
  unfold assumptionCoercionEdges at member
  simp only [List.mem_filterMap] at member
  obtain ⟨assumption, _, produced⟩ := member
  grind

private theorem rawCoercionEdges_member_source
    {context : Context} {state : State}
    {trait : Resolved.DeclarationId} {source : Ty} {edge : CoercionEdge}
    (member : edge ∈
      ((context.signatures.implRules.filterMap
        (coercionRuleEdge? trait source)) ++
        assumptionCoercionEdges context state trait source).eraseDups) :
    edge.source = source := by
  rw [List.mem_eraseDups, List.mem_append] at member
  rcases member with ruleMember | assumptionMember
  · simp only [List.mem_filterMap] at ruleMember
    obtain ⟨rule, _, produced⟩ := ruleMember
    exact coercionRuleEdge?_some_source produced
  · exact assumptionCoercionEdges_member_source assumptionMember

private def attachCoercionMethodPredicates
    (profile : Option CoercionMethodProfile) (edge : CoercionEdge) :
    Except Error CoercionEdge := do
  let methodPredicates ←
    coercionMethodPredicates profile edge.source edge.target
  pure { edge with methodPredicates }

private theorem mapCoercionMethodPredicates_success_sources
    (profile : Option CoercionMethodProfile) (source : Ty) :
    ∀ (input output : List CoercionEdge),
      (∀ (edge : CoercionEdge), edge ∈ input → edge.source = source) →
      input.mapM (attachCoercionMethodPredicates profile) = .ok output →
      ∀ (edge : CoercionEdge), edge ∈ output → edge.source = source := by
  intro input
  induction input with
  | nil =>
      intro output _ success
      change Except.ok [] = Except.ok output at success
      injection success with outputEq
      subst output
      simp
  | cons head rest induction =>
      intro output inputSources success
      cases methodResult :
          coercionMethodPredicates profile head.source head.target with
      | error error =>
          simp [List.mapM_cons, attachCoercionMethodPredicates, methodResult,
            bind, Except.bind, pure, Pure.pure, Except.pure] at success
      | ok methodPredicates =>
          simp only [List.mapM_cons, attachCoercionMethodPredicates,
            methodResult, bind, Except.bind, pure, Pure.pure, Except.pure]
            at success
          cases tailResult : rest.mapM
              (attachCoercionMethodPredicates profile) with
          | error error =>
              rw [tailResult] at success
              contradiction
          | ok tail =>
              rw [tailResult] at success
              injection success with outputEq
              subst output
              intro edge member
              rcases List.mem_cons.mp member with rfl | member
              · exact inputSources head (by simp)
              · exact induction tail
                  (fun candidate candidateMember =>
                    inputSources candidate (by simp [candidateMember]))
                  tailResult edge member

private theorem coercionEdges_success_sources
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {edges : List CoercionEdge}
    (success : coercionEdges context state profile trait source = .ok edges) :
    ∀ edge, edge ∈ edges → edge.source = source := by
  unfold coercionEdges at success
  let input :=
    ((context.signatures.implRules.filterMap
      (coercionRuleEdge? trait source)) ++
      assumptionCoercionEdges context state trait source).eraseDups
  change input.mapM (attachCoercionMethodPredicates profile) = .ok edges
    at success
  exact mapCoercionMethodPredicates_success_sources profile source input
    edges (fun edge member => by
      exact rawCoercionEdges_member_source (by simpa [input] using member))
    success

private theorem viableCoercionEdges_viable_subset
    (context : Context) (state : State) (edges : List CoercionEdge) :
    (viableCoercionEdges context state edges).viable ⊆ edges := by
  intro edge member
  induction edges with
  | nil => simp [viableCoercionEdges] at member
  | cons head rest induction =>
      simp only [viableCoercionEdges] at member
      cases result : coercionEvidenceViable context state head.predicate
          head.methodPredicates with
      | error error =>
          simp [result] at member
          exact List.mem_cons_of_mem head (induction member)
      | ok viable =>
          cases viable with
          | false =>
              simp [result] at member
              exact List.mem_cons_of_mem head (induction member)
          | true =>
              simp [result] at member
              rcases member with rfl | member
              · simp
              · exact List.mem_cons_of_mem head (induction member)

private theorem expandCoercionPath_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {path : CoercionPath} {expansion : CoercionExpansion}
    (pathValid : PlannedCoercionPath.isValid source path.current
      path.steps = true)
    (success : expandCoercionPath context state profile trait path =
      .ok expansion) :
    ∀ candidate, candidate ∈ expansion.paths →
      PlannedCoercionPath.isValid source candidate.current
        candidate.steps = true := by
  unfold expandCoercionPath at success
  cases edgesResult : coercionEdges context state profile trait path.current with
  | error error =>
      simp [edgesResult, bind, Except.bind] at success
  | ok allEdges =>
      simp only [edgesResult, bind, Except.bind, pure, Pure.pure, Except.pure]
        at success
      injection success with expansionEq
      subst expansion
      intro candidate member
      simp only [List.mem_map] at member
      obtain ⟨edge, edgeMember, rfl⟩ := member
      change PlannedCoercionPath.isValid source edge.target
        (path.steps ++ [{
          source := edge.source
          target := edge.target
          predicate := edge.predicate
          methodPredicates := edge.methodPredicates
        }]) = true
      exact plannedCoercionPath_isValid_append pathValid
        ({
          source := edge.source
          target := edge.target
          predicate := edge.predicate
          methodPredicates := edge.methodPredicates
        } : PlannedCoercionStep)
        (coercionEdges_success_sources edgesResult edge
          (List.mem_filter.mp
            (viableCoercionEdges_viable_subset context state _ edgeMember)).1)

private theorem expandCoercionPaths_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source : Ty}
    {frontier : List CoercionPath} {expansion : CoercionExpansion}
    (frontierValid : ∀ path, path ∈ frontier →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : expandCoercionPaths context state profile trait frontier =
      .ok expansion) :
    ∀ path, path ∈ expansion.paths →
      PlannedCoercionPath.isValid source path.current path.steps = true := by
  induction frontier generalizing expansion with
  | nil =>
      simp [expandCoercionPaths, pure, Pure.pure, Except.pure] at success
      subst expansion
      simp
  | cons path rest induction =>
      simp only [expandCoercionPaths] at success
      cases headResult : expandCoercionPath context state profile trait path with
      | error error =>
          simp [headResult, bind, Except.bind] at success
      | ok head =>
          cases tailResult : expandCoercionPaths context state profile trait
              rest with
          | error error =>
              simp [headResult, tailResult, bind, Except.bind] at success
          | ok tail =>
              simp [headResult, tailResult, bind, Except.bind, pure,
                Pure.pure, Except.pure] at success
              subst expansion
              intro candidate member
              rw [List.mem_append] at member
              rcases member with headMember | tailMember
              · exact expandCoercionPath_success_valid
                  (frontierValid path (by simp)) headResult candidate headMember
              · exact induction
                  (fun candidate candidateMember =>
                    frontierValid candidate (by simp [candidateMember]))
                  tailResult candidate tailMember

private theorem selectCoercionPath_success_valid
    {source target : Ty} {paths : List CoercionPath}
    {steps : List PlannedCoercionStep}
    (pathsValid : ∀ path, path ∈ paths →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : selectCoercionPath source target paths = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  unfold selectCoercionPath at success
  cases matchingEq :
      (paths.filter fun path => path.current == target).eraseDups with
  | nil => simp [matchingEq] at success
  | cons first rest =>
      cases rest with
      | nil =>
          simp [matchingEq] at success
          subst steps
          have firstMember : first ∈
              (paths.filter fun path => path.current == target).eraseDups := by
            rw [matchingEq]
            simp
          rw [List.mem_eraseDups, List.mem_filter] at firstMember
          have currentEq : first.current = target :=
            beq_iff_eq.mp firstMember.2
          subst target
          exact pathsValid first firstMember.1
      | cons second tail => simp [matchingEq] at success

private theorem finishCoercionSearch_ne_some
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (success : finishCoercionSearch blocked = .ok (some steps)) : False := by
  unfold finishCoercionSearch at success
  cases blocked <;> simp at success

private theorem searchCoercionPaths_success_valid
    {context : Context} {state : State}
    {profile : Option CoercionMethodProfile}
    {trait : Resolved.DeclarationId} {source target : Ty}
    {fuel : Nat} {frontier : List CoercionPath}
    {blocked : List Error} {steps : List PlannedCoercionStep}
    (frontierValid : ∀ path, path ∈ frontier →
      PlannedCoercionPath.isValid source path.current path.steps = true)
    (success : searchCoercionPaths context state profile trait source target
      fuel frontier blocked = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  induction fuel generalizing frontier blocked steps with
  | zero =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state profile trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok beyond =>
          simp only [expandedResult, bind, Except.bind] at success
          by_cases empty : beyond.paths.isEmpty = true
          · simp only [empty, ↓reduceIte] at success
            exact (finishCoercionSearch_ne_some success).elim
          · simp [empty] at success
  | succ fuel induction =>
      simp only [searchCoercionPaths] at success
      cases expandedResult :
          expandCoercionPaths context state profile trait frontier with
      | error error =>
          simp [expandedResult, bind, Except.bind] at success
      | ok next =>
          simp only [expandedResult, bind, Except.bind] at success
          have nextValid :=
            expandCoercionPaths_success_valid frontierValid expandedResult
          cases selectedResult : selectCoercionPath source target next.paths with
          | error error =>
              simp [selectedResult, bind, Except.bind] at success
          | ok selected =>
              simp only [selectedResult, bind, Except.bind] at success
              cases selected with
              | some selectedSteps =>
                  simp [pure, Pure.pure, Except.pure] at success
                  subst steps
                  exact selectCoercionPath_success_valid nextValid
                    selectedResult
              | none =>
                  simp only at success
                  by_cases empty : next.paths.isEmpty = true
                  · simp only [empty, ↓reduceIte] at success
                    exact (finishCoercionSearch_ne_some success).elim
                  · simp only [empty, Bool.false_eq_true, ↓reduceIte]
                      at success
                    exact induction nextValid success

/-- Every coercion plan returned by source inference has the requested exact
endpoints and pairwise-adjacent planned steps. -/
theorem coercionPlan?_some_isValid
    {context : Context} {state : State} {source target : Ty}
    {steps : List PlannedCoercionStep}
    (success : coercionPlan? context state source target = .ok (some steps)) :
    PlannedCoercionPath.isValid source target steps = true := by
  unfold coercionPlan? at success
  cases traitResult : conventionalTraitWithArity? context "Coerce" 2 with
  | error error =>
      simp [traitResult, bind, Except.bind] at success
  | ok traitOption =>
      simp only [traitResult, bind, Except.bind] at success
      cases traitOption with
      | none => simp [pure, Pure.pure, Except.pure] at success
      | some trait =>
          cases profileResult : coercionMethodProfile? context trait with
          | error error =>
              simp [profileResult, bind, Except.bind] at success
          | ok profile =>
              simp only [profileResult, bind, Except.bind] at success
              let direct : ProgramPredicate := {
                trait
                subject := source
                arguments := [target]
              }
              cases methodResult :
                  coercionMethodPredicates profile source target with
              | error error =>
                  simp [methodResult, bind, Except.bind] at success
              | ok methodPredicates =>
                  simp only [methodResult, bind, Except.bind] at success
                  cases viableResult : coercionEvidenceViable context state
                      direct methodPredicates with
                  | error error =>
                      simp [direct, viableResult] at success
                  | ok viable =>
                      cases viable with
                      | true =>
                          simp [direct, viableResult, pure, Pure.pure,
                            Except.pure] at success
                          subst steps
                          simp [PlannedCoercionPath.isValid]
                      | false =>
                          cases searchResult : searchCoercionPaths context state
                              profile trait source target context.coercionDepth
                              [{
                                current := source
                                visited := [source]
                                steps := []
                              }] [] with
                          | error error =>
                              simp [direct, viableResult, searchResult, bind,
                                Except.bind] at success
                          | ok plan =>
                              simp only [direct, viableResult, searchResult,
                                bind, Except.bind] at success
                              cases plan with
                              | none =>
                                  simp [pure, Pure.pure, Except.pure] at success
                                  subst steps
                                  simp [PlannedCoercionPath.isValid]
                              | some searchedSteps =>
                                  simp [pure, Pure.pure, Except.pure] at success
                                  subst steps
                                  exact searchCoercionPaths_success_valid
                                    (by
                                      intro path member
                                      simp at member
                                      subst path
                                      simp [PlannedCoercionPath.isValid])
                                    searchResult

@[simp] private theorem addRequirementsWithIds_resolve
    (state : State) (predicates : List ProgramPredicate) (type : Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type =
      state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

/-- Allocating coercion requirement identities leaves type resolution
unchanged. -/
@[simp] theorem commitCoercionPlan_resolve
    (state : State) (plan : List PlannedCoercionStep) (type : Ty) :
    (commitCoercionPlan state plan).2.resolve type = state.resolve type := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      exact addRequirementsWithIds_resolve
        (state.addRequirementWithId step.predicate).2
        step.methodPredicates type

/-- Every successful expected-type fit returns either the empty equality path
or a committed coercion path with exact resolved endpoints and adjacency. -/
theorem withExpected_success_coercions_isValid
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    CoercionPath.isValid (result.state.resolve actual.type)
      result.expression.type result.coercions = true := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      simp [CoercionPath.isValid]
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          apply beq_iff_eq.mpr
          exact TypeSystem.InferState.unify_resolve_eq unification
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted =>
              simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error =>
                  simp [planResult, bind, Except.bind] at success
              | ok planOption =>
                  cases planOption with
                  | none =>
                      simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      have planValid : PlannedCoercionPath.isValid
                          (state.resolve actual.type) (state.resolve expected)
                          plan = true :=
                        coercionPlan?_some_isValid planResult
                      have committedValid :=
                        commitCoercionPlan_isValid state plan planValid
                      simpa only [commitCoercionPlan_resolve] using
                        committedValid

/-- A successfully resolved source annotation contains no flexible
metavariables, so every inference substitution fixes it. -/
theorem resolveSourceType_success_apply_eq_self
    {context : Context} {source : Syntax.TypeExpr} {type : Ty}
    (substitution : Substitution)
    (success : resolveSourceType context source = .ok type) :
    substitution.apply type = type :=
  (resolveSourceType_success_formation success).apply_eq_self substitution

@[simp] private theorem except_pure_eq_ok {ε α : Type}
    (value result : α) :
    ((pure value : Except ε α) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem except_map_eq_ok {ε α β : Type} {map : α → β}
    {computation : Except ε α} {result : β}
    (success : map <$> computation = .ok result) :
    ∃ value, computation = .ok value ∧ map value = result := by
  cases computation with
  | error error =>
      change Except.error error = Except.ok result at success
      contradiction
  | ok value =>
      refine ⟨value, rfl, ?_⟩
      change Except.ok (map value) = Except.ok result at success
      exact Except.ok.inj success

private def PreservesStateHeader {α : Type} (stateOf : α → State)
    (initial : State) (computation : Except Error α) : Prop :=
  ∀ result, computation = .ok result →
    (stateOf result).header = initial.header

private theorem pair_success_state_header {α : Type}
    {operation : α × State} {value : α} {next initial : State}
    (operationHeader : operation.2.header = initial.header)
    (success : operation = (value, next)) :
    next.header = initial.header := by
  calc
    next.header = operation.2.header := by
      exact (congrArg (fun result => result.2.header) success).symm
    _ = initial.header := operationHeader

private theorem pair_eq_property {α β : Type} {result : α × β}
    {property : β → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {ε α β : Type}
    {computation : Except ε (α × β)} {result : α × β}
    {property : β → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem allocateExpressionId_success_header
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateExpressionId_header state) success

private theorem allocateStatementId_success_header
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateStatementId_header state) success

private theorem state_fresh_success_header
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    next.header = state.header :=
  pair_success_state_header (State.fresh_header state) success

private theorem allocateHiddenLocal_success_header
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    next.header = state.header :=
  pair_success_state_header (State.allocateHiddenLocal_header state) success

private theorem addRequirementWithId_success_header
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.addRequirementWithId_header state predicate) success

private theorem addRequirementsWithIds_success_header
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.addRequirementsWithIds_header state predicates) success

private theorem allocateBinder_success_header
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    next.header = state.header :=
  pair_success_state_header
    (State.allocateBinder_header state name scheme span comptime
      schemeRequirements) success

@[simp] private theorem commitCoercionPlan_state_header
    (state : State) (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.header = state.header := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest induction =>
      simp only [commitCoercionPlan]
      rw [induction]
      simp

private theorem withExpected_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.header = state.header := by
  cases expected with
  | none =>
      simp only [withExpected] at success
      injection success with resultEq
      subst result
      rfl
  | some expected =>
      cases unification : state.inference.unify actual.type expected with
      | ok inference =>
          simp only [withExpected, unification] at success
          injection success with resultEq
          subst result
          rfl
      | error error =>
          cases error with
          | occursCheck metavariable type =>
              simp [withExpected, unification] at success
          | exhausted => simp [withExpected, unification] at success
          | mismatch left right =>
              simp only [withExpected, unification] at success
              cases planResult : coercionPlan? context state
                  (state.resolve actual.type) (state.resolve expected) with
              | error error => simp [planResult, bind, Except.bind] at success
              | ok plan? =>
                  cases plan? with
                  | none => simp [planResult, bind, Except.bind] at success
                  | some plan =>
                      simp only [planResult, bind, Except.bind] at success
                      change Except.ok _ = Except.ok result at success
                      injection success with resultEq
                      subst result
                      exact commitCoercionPlan_state_header state plan

@[simp] private theorem withExpected_preserves_owner
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (withExpected_state_header success)

@[simp] private theorem withExpected_preserves_inputs
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : withExpected context state actual expected = .ok result) :
    result.state.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (withExpected_state_header success)

@[simp] private theorem recordExpression_state_header
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State) :
    (recordExpression source expression form requirements coercions state).2.header =
      state.header := by
  exact State.recordNode_header state _

private theorem recordExpressionWithExpected_state_header
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordExpressionWithExpected context source id type form
      requirements expected state = .ok result) :
    result.2.header = state.header := by
  unfold recordExpressionWithExpected at success
  cases fittedResult : withExpected context state { id, type } expected with
  | error error => simp [fittedResult, bind, Except.bind] at success
  | ok fitted =>
      simp only [fittedResult, bind, Except.bind, except_pure_eq_ok] at success
      subst result
      exact (recordExpression_state_header source fitted.expression form
        (requirements ++ coercionRequirements fitted.coercions)
        fitted.coercions fitted.state).trans
          (withExpected_state_header fittedResult)

private theorem bindLambdaParameters_state_header
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    result.2.2.header = state.header := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      rfl
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind,
            Except.pure] at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all [Except.pure]
          all_goals
            subst result
            subst_vars
            have tailHeader := induction _ _ _ (by assumption)
            exact tailHeader.trans (by
              simp_all [State.header, State.fresh, State.allocateBinder])
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error => simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all [Except.pure]
              all_goals
                subst result
                subst_vars
                have tailHeader := induction _ _ _ (by assumption)
                exact tailHeader.trans (by
                  simp_all [State.header, State.allocateBinder])

/-- Successful unification changes only the inference substitution, preserving
the declaration owner and original input binders. -/
@[simp] theorem unify_state_header
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.header = state.header := by
  unfold unify at success
  cases inferenceResult : liftUnification (state.inference.unify left right) with
  | error error => simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok next at success
      injection success with nextEq
      subst next
      rfl

/-- Successful source-inference unification makes the original input types
equal under the returned inference state. -/
theorem unify_resolve_eq
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.inference.resolve left = next.inference.resolve right := by
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      exact TypeSystem.InferState.unify_resolve_eq inferenceSuccess

/-- Any type equality already visible through the input inference state
remains visible after a successful incremental unification. -/
theorem unify_preserves_resolve_eq
    {state next : State} {left right first second : Ty}
    (equal : state.resolve first = state.resolve second)
    (success : unify state left right = .ok next) :
    next.resolve first = next.resolve second := by
  unfold unify at success
  cases inferenceSuccess : state.inference.unify left right with
  | error error =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
  | ok inference =>
      simp [liftUnification, inferenceSuccess, bind, Except.bind] at success
      cases success
      unfold State.resolve at equal ⊢
      unfold TypeSystem.InferState.unify at inferenceSuccess
      cases updateSuccess : TypeSystem.Unification.unifyTypes
          (state.inference.resolve left) (state.inference.resolve right) with
      | error error =>
          simp [updateSuccess, bind, Except.bind] at inferenceSuccess
      | ok update =>
          simp [updateSuccess, bind, Except.bind] at inferenceSuccess
          cases inferenceSuccess
          simpa [TypeSystem.InferState.resolve,
            TypeSystem.Substitution.compose_apply] using
              congrArg update.apply equal

@[simp] private theorem unify_preserves_owner
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.owner = state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (unify_state_header success)

@[simp] private theorem unify_preserves_inputs
    {state next : State} {left right : Ty}
    (success : unify state left right = .ok next) :
    next.inputs = state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (unify_state_header success)

@[simp] private theorem freshTypes_preserves_header
    (count : Nat) (state : State) :
    (freshTypes count state).2.header = state.header := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [freshTypes]
      rw [induction]
      exact State.fresh_header state

@[simp] private theorem freshTypes_preserves_owner
    (count : Nat) (state : State) :
    (freshTypes count state).2.owner = state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (freshTypes_preserves_header count state)

@[simp] private theorem freshTypes_preserves_inputs
    (count : Nat) (state : State) :
    (freshTypes count state).2.inputs = state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (freshTypes_preserves_header count state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_header
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.header =
      state.header := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ =>
      (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldHeader (parameters : List TypeParameterId)
      (accumulator : List Ty × State) :
      (parameters.foldl step accumulator).2.header =
        accumulator.2.header := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter parameters induction =>
        simp only [List.foldl_cons]
        rw [induction]
        exact State.fresh_header accumulator.2
  unfold freshDataConstructorInstantiation
  exact foldHeader dataType.parameters ([], state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_owner
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.owner =
      state.owner := by
  exact congrArg (fun header : State.Header => header.owner)
    (freshDataConstructorInstantiation_preserves_header dataType constructor
      state)

@[simp] private theorem freshDataConstructorInstantiation_preserves_inputs
    (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.inputs =
      state.inputs := by
  exact congrArg (fun header : State.Header => header.inputs)
    (freshDataConstructorInstantiation_preserves_header dataType constructor
      state)

private theorem inferMatchPatternFlatFuel_preserves_header
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesStateHeader InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
      (motive1 := fun fuel pattern expected seen state =>
        PreservesStateHeader InferredPattern.state state
          (inferMatchPatternFlatFuel fuel context pattern expected seen state))
      (motive2 := fun fuel patterns expected seen state =>
        PreservesStateHeader InferredPatterns.state state
          (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesStateHeader at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel,
      bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have headerEq := unify_state_header (by assumption)
    all_goals try have ownerEq := unify_preserves_owner (by assumption)
    all_goals try have inputsEq := unify_preserves_inputs (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try simp_all [State.header, State.fresh,
      State.addRequirementWithId, State.allocateBinder, bind, Except.bind]
    all_goals grind [unify_preserves_owner, unify_preserves_inputs,
      freshDataConstructorInstantiation_preserves_owner,
      freshDataConstructorInstantiation_preserves_inputs,
      freshTypes_preserves_owner, freshTypes_preserves_inputs]

/-- Successful pattern inference preserves the declaration-scoped state
header. -/
theorem inferMatchPatternFuel_state_header
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    result.2.header = state.header := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact inferMatchPatternFlatFuel_preserves_header fuel context pattern
        expected [] state inferred flatResult

private theorem inferUnaryOperator_state_header
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem inferBinaryOperator_state_header
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    result.state.header = state.header := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem candidateWithExpected_some_state_header
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (success : candidateWithExpected context state actual expected =
      .ok (some result)) :
    result.state.header = state.header := by
  unfold candidateWithExpected at success
  cases fittedResult : withExpected context state actual expected with
  | error error =>
      cases error <;> simp [fittedResult] at success
      all_goals cases ‹Unification.Error› <;> simp_all [fittedResult]
  | ok fitted =>
      simp only [fittedResult] at success
      injection success with resultEq
      have fittedEq : fitted = result := Option.some.inj resultEq
      subst result
      exact withExpected_state_header fittedResult

private theorem fitArguments_some_state_header
    {context : Context} {state : State}
    {arguments : List InferredExpression} {parameters : List Ty}
    {result : ArgumentFitResult}
    (success : fitArguments context state arguments parameters =
      .ok (some result)) :
    result.state.header = state.header := by
  induction arguments generalizing parameters state result with
  | nil =>
      cases parameters <;> simp [fitArguments] at success
      subst result
      rfl
  | cons argument arguments induction =>
      cases parameters with
      | nil => simp [fitArguments] at success
      | cons parameter parameters =>
          simp only [fitArguments] at success
          cases fittedResult :
              candidateWithExpected context state argument (some parameter) with
          | error error =>
              simp [fittedResult, bind, Except.bind] at success
          | ok fitted? =>
              cases fitted? with
              | none => simp [fittedResult, bind, Except.bind] at success
              | some fitted =>
                  simp only [fittedResult, bind, Except.bind] at success
                  cases tailResult : fitArguments context fitted.state arguments
                      parameters with
                  | error error =>
                      simp [tailResult, bind, Except.bind] at success
                  | ok tail? =>
                      cases tail? with
                      | none => simp [tailResult, bind, Except.bind] at success
                      | some tail =>
                          simp only [tailResult, bind, Except.bind,
                            except_pure_eq_ok] at success
                          have resultEq : _ = result := Option.some.inj success
                          clear success
                          subst result
                          exact (induction tailResult).trans
                            (candidateWithExpected_some_state_header fittedResult)

/-- A successful function-candidate attempt retains exactly the generic
instantiation allocated before argument fitting, expected-type fitting, and
predicate validation.  None of those later checks may replace the selected
declaration or its shared parameter substitution. -/
theorem tryFunctionCandidate_some_instantiation
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.instantiation =
      DeclarationInstantiation.ofInstantiated signature
        (signature.scheme.instantiate state.inference.next) := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals simp_all

private theorem tryFunctionCandidate_some_state_header
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (success : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.header = state.header := by
  unfold tryFunctionCandidate at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have fitHeader :=
    fitArguments_some_state_header (by assumption)
  all_goals try have expectedHeader :=
    candidateWithExpected_some_state_header (by assumption)
  all_goals try simp_all
  all_goals simp_all [State.header, State.addRequirementsWithIds,
    State.addRequirementWithId, State.markDirectCallRequirements]

private theorem collectCandidateAttempts_success_header
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)}
    {state : State}
    (attemptHeader : ∀ signature result,
      attempt signature = .ok (some result) →
        result.state.header = state.header) :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        success.attempt.state.header = state.header := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro success member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          exact induction success member
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              exact induction success member
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl successEq =>
                  subst success
                  exact attemptHeader signature result attemptResult
              | inr member => exact induction success member

private theorem collectCandidateAttempts_success_provenance
    {attempt : ProgramFunctionSignature →
      Except Error (Option CandidateAttemptResult)} :
    ∀ candidates success,
      success ∈ (collectCandidateAttempts attempt candidates).successes →
        ∃ signature, signature ∈ candidates ∧
          attempt signature = .ok (some success.attempt) := by
  intro candidates
  induction candidates with
  | nil => simp [collectCandidateAttempts]
  | cons signature candidates induction =>
      intro success member
      simp only [collectCandidateAttempts] at member
      cases attemptResult : attempt signature with
      | error error =>
          simp only [attemptResult] at member
          obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
            induction success member
          exact ⟨selected, by simp [selectedMember], selectedSuccess⟩
      | ok result? =>
          cases result? with
          | none =>
              simp only [attemptResult] at member
              obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
                induction success member
              exact ⟨selected, by simp [selectedMember], selectedSuccess⟩
          | some result =>
              simp only [attemptResult, List.mem_cons] at member
              cases member with
              | inl successEq =>
                  subst success
                  exact ⟨signature, by simp, attemptResult⟩
              | inr member =>
                  obtain ⟨selected, selectedMember, selectedSuccess⟩ :=
                    induction success member
                  exact ⟨selected, by simp [selectedMember], selectedSuccess⟩

private theorem bestCandidateSuccesses_subset
    (successes : List CandidateSuccess) :
    bestCandidateSuccesses successes ⊆ successes := by
  intro success member
  unfold bestCandidateSuccesses at member
  dsimp only at member
  split at member
  · contradiction
  · have preferredMember := (List.mem_filter.mp member).1
    by_cases empty :
        (successes.filter fun success =>
          !success.attempt.hasDeferredIntegerLiterals).isEmpty
    · simpa [empty] using preferredMember
    · have groundMember :
          success ∈ successes.filter fun success =>
            !success.attempt.hasDeferredIntegerLiterals := by
        simpa [empty] using preferredMember
      exact (List.mem_filter.mp groundMember).1

/-- Every successfully selected overload is the unchanged successful result
of checking one signature from the caller-provided candidate list.  Ranking
may discard other successes, but it cannot synthesize or rewrite the retained
candidate attempt. -/
theorem selectFunctionCandidateFrom_success_candidate
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∃ signature, signature ∈ candidates ∧
      tryFunctionCandidate context arguments integerLiteralOrigins call
        expected state signature = .ok (some result) := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_subset search.successes
                (by simp [selected])
            simpa [attempt] using
              (collectCandidateAttempts_success_provenance
                candidates candidate member)

/-- Overload ranking returns one unchanged successful candidate attempt, so
its requirement ledger is canonical whenever the shared input ledger is. -/
theorem selectFunctionCandidateFrom_preserves_requirementsWellFormed
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  obtain ⟨signature, _, candidateSuccess⟩ :=
    selectFunctionCandidateFrom_success_candidate success
  exact tryFunctionCandidate_preserves_requirementsWellFormed
    candidateSuccess wellFormed

/-- Resolving the visible overload set is state-free; successful ordinary
selection therefore inherits the explicit-candidate ledger guarantee. -/
theorem selectFunctionCandidate_preserves_requirementsWellFormed
    {context : Context} {name : String}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidate context name arguments
      integerLiteralOrigins call expected state = .ok result)
    (wellFormed : state.RequirementsWellFormed) :
    result.state.RequirementsWellFormed := by
  unfold selectFunctionCandidate at success
  cases candidatesResult : functionsNamed context name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      simp only [candidatesResult, bind, Except.bind] at success
      exact selectFunctionCandidateFrom_preserves_requirementsWellFormed
        success wellFormed

private theorem selectFunctionCandidateFrom_state_header
    {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : CandidateAttemptResult}
    (success : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.header = state.header := by
  unfold selectFunctionCandidateFrom at success
  let attempt := tryFunctionCandidate context arguments integerLiteralOrigins
    call expected state
  let search := collectCandidateAttempts attempt candidates
  change selectCandidateSearch name candidates search = .ok result at success
  unfold selectCandidateSearch at success
  cases selected : bestCandidateSuccesses search.successes with
  | nil =>
      simp only [selected] at success
      repeat' first | split at success
      all_goals contradiction
  | cons candidate rest =>
      cases rest with
      | cons second tail => simp [selected] at success
      | nil =>
          simp only [selected] at success
          split at success
          · contradiction
          · injection success with resultEq
            subst result
            have member : candidate ∈ search.successes :=
              bestCandidateSuccesses_subset search.successes
                (by simp [selected])
            exact collectCandidateAttempts_success_header
              (state := state)
              (fun signature result attemptSuccess =>
                tryFunctionCandidate_some_state_header attemptSuccess)
              candidates candidate member

@[simp] private theorem attachExpressionCoercions_state_header
    (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).header = state.header := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries induction =>
      simp only [List.foldl_cons]
      exact (induction _).trans
        (State.modifyExpressionNode_header state entry.expression _)

@[simp] private theorem recordSelectedCall_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    (recordSelectedCall source callee name arguments attempt).2.header =
      attempt.state.header := by
  simp [recordSelectedCall, recordSelectedCallResult]

@[simp] private theorem recordSelectedCallResult_state_header
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep)
    (state : State) :
    (recordSelectedCallResult source callee name arguments attempt result
      trailingCoercions state).2.header = state.header := by
  simp [recordSelectedCallResult]

private theorem applyFunctionType_state_header
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    result.state.header = state.header := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact (withExpected_state_header resultResult).trans
                (withExpected_state_header argumentResult)
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult, bind, Except.bind] at success
          | ok fittedResult =>
              simp only [resultResult, bind, Except.bind] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact (withExpected_state_header resultResult).trans
                ((unify_state_header unifyResult).trans
                  (state_fresh_success_header freshResultEq))

@[simp] private theorem recordIndirectCall_state_header
    (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    (recordIndirectCall source callee arguments result).2.header =
      result.state.header := by
  simp [recordIndirectCall]

private theorem unifyBuiltinFunctionArgumentsEqual_state_header
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    next.header = state.header := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      rfl
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          rfl
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unifiedState =>
              simp only [unifyResult, bind, Except.bind] at success
              exact (induction success).trans (unify_state_header unifyResult)

private theorem recordBuiltinFunctionCall_state_header
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    result.2.header = state.header := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try have argumentsHeader :=
    unifyBuiltinFunctionArgumentsEqual_state_header (by assumption)
  all_goals try have headerEq := unify_state_header (by assumption)
  all_goals try simp_all
  all_goals try simp_all [State.header, State.allocateExpressionId,
    State.recordNode, recordExpression, bind, Except.bind]
  all_goals grind [unify_preserves_owner, unify_preserves_inputs]

private theorem syntheticTuple_result_state_header
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    result.snd.header = state.header := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [except_pure_eq_ok] using success
  rw [← resultEq]
  simp only [State.recordNode_header, State.allocateExpressionId_header]

private theorem pure_pair_result_state_header {ε α : Type}
    {value : α} {next initial : State} {
      result : α × State}
    (nextHeader : next.header = initial.header)
    (success : (pure (value, next) : Except ε (α × State)) = .ok result) :
    result.snd.header = initial.header := by
  have resultEq : (value, next) = result := by
    simpa only [except_pure_eq_ok] using success
  rw [← resultEq]
  exact nextHeader

private theorem pair_result_state_header {α : Type}
    {value : α} {next initial : State} {result : α × State}
    (nextHeader : next.header = initial.header)
    (success : (value, next) = result) :
    result.snd.header = initial.header := by
  rw [← success]
  exact nextHeader

private theorem restore_state_header {state initial : State}
    {scope : LexicalScope} (header : state.header = initial.header) :
    (state.restoreLexicalScope scope).header = initial.header :=
  (State.restoreLexicalScope_header state scope).trans header

private theorem restored_pair_result_state_header {α : Type}
    {value : α} {state initial : State} {scope : LexicalScope}
    {result : α × State}
    (header : state.header = initial.header)
    (success : (value, state.restoreLexicalScope scope) = result) :
    result.snd.header = initial.header :=
  pair_result_state_header (restore_state_header header) success

set_option maxHeartbeats 500000 in
private theorem inferStatementsFuel_preserves_header_internal
    (fuel : Nat) (context : Context) (statements : List Syntax.Statement)
    (expectedReturn : Ty) (state : State) :
    PreservesStateHeader BlockResult.state state
      (inferStatementsFuel fuel context statements expectedReturn state) := by
  apply inferStatementsFuel.induct
    (motive1 := fun fuel context expression expected state =>
      PreservesStateHeader Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesStateHeader Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesStateHeader Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesStateHeader BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesStateHeader StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesStateHeader InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesStateHeader Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesStateHeader Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesStateHeader (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesStateHeader Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesStateHeader MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesStateHeader at *
    intro result success
    have statementIdHeader :=
      allocateStatementId_success_header statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsHeader :=
      expressionsInduction _ (by assumption)
    all_goals try have casesHeader :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodyHeader :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleHeader :=
      syntheticTuple_result_state_header (by assumption)
    all_goals try have defaultHeader :=
      pure_pair_result_state_header casesHeader (by assumption)
    all_goals simp_all only [Prod.eta, except_pure_eq_ok,
      State.allocateExpressionId_header, State.allocateHiddenLocal_header,
      State.restoreLexicalScope_header, State.recordNode_header]
    all_goals try exact
      restored_pair_result_state_header bodyHeader (by assumption)
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesStateHeader at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try have placeHeader :=
      pair_except_property placeInduction (by assumption)
    all_goals try have valueHeader :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedHeader := unify_state_header (by assumption)
    all_goals simp_all [Prod.eta]
  case case67 =>
    unfold PreservesStateHeader at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesStateHeader at *
    intro result success
    first
      | unfold inferExprFuel at success
      | unfold inferConstructorApplicationFuel at success
      | unfold inferConstructorArgumentsFuel at success
      | unfold inferStatementsFuel at success
      | unfold inferStatementFuel at success
      | unfold inferForItemsFuel at success
      | unfold inferForItemFuel at success
      | unfold inferPlaceFuel at success
      | unfold inferAssignedValueFuel at success
      | unfold inferExprsFuel at success
      | unfold inferMatchCasesFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | have ih1Header := pair_eq_property ih1
      | have ih1Header := pair_except_property ih1 (by assumption)
      | have ih1Header := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Header := pair_eq_property ih2
      | have ih2Header := pair_except_property ih2 (by assumption)
      | have ih2Header := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Header := pair_eq_property ih3
      | have ih3Header := pair_except_property ih3 (by assumption)
      | have ih3Header := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have headerEq := unify_state_header (by assumption)
    all_goals try have expressionIdHeader :=
      allocateExpressionId_success_header (by assumption)
    all_goals try have statementIdHeader :=
      allocateStatementId_success_header (by assumption)
    all_goals try have freshHeader := state_fresh_success_header (by assumption)
    all_goals try have hiddenLocalHeader :=
      allocateHiddenLocal_success_header (by assumption)
    all_goals try have requirementHeader :=
      addRequirementWithId_success_header (by assumption)
    all_goals try have requirementsHeader :=
      addRequirementsWithIds_success_header (by assumption)
    all_goals try have binderHeader :=
      allocateBinder_success_header (by assumption)
    all_goals try have recordHeader :=
      recordExpressionWithExpected_state_header (by assumption)
    all_goals try have lambdaHeader :=
      bindLambdaParameters_state_header (by assumption)
    all_goals try have patternHeader :=
      inferMatchPatternFuel_state_header (by assumption)
    all_goals try have unaryHeader :=
      inferUnaryOperator_state_header (by assumption)
    all_goals try have binaryHeader :=
      inferBinaryOperator_state_header (by assumption)
    all_goals try have selectionHeader :=
      selectFunctionCandidateFrom_state_header (by assumption)
    all_goals try have expectedHeader :=
      withExpected_state_header (by assumption)
    all_goals try have applicationHeader :=
      applyFunctionType_state_header (by assumption)
    all_goals try have builtinHeader :=
      recordBuiltinFunctionCall_state_header (by assumption)
    all_goals try simp_all
    all_goals try simp_all [State.header, State.fresh,
      State.addRequirementWithId, State.addRequirementsWithIds,
      State.allocateBinder, State.allocateHiddenLocal,
      State.restoreLexicalScope, State.recordNode, bind, Except.bind]
    all_goals grind [unify_preserves_owner, unify_preserves_inputs,
      freshDataConstructorInstantiation_preserves_owner,
      freshDataConstructorInstantiation_preserves_inputs,
      freshTypes_preserves_owner, freshTypes_preserves_inputs]

/-- Successful statement-list inference preserves the declaration owner and
the original input binders. -/
theorem inferStatementsFuel_state_header
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.header = state.header := by
  exact inferStatementsFuel_preserves_header_internal fuel context statements
    expectedReturn state result success

@[simp] theorem inferStatementsFuel_preserves_owner
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.owner = state.owner :=
  congrArg (fun header : State.Header => header.owner)
    (inferStatementsFuel_state_header success)

@[simp] theorem inferStatementsFuel_preserves_inputs
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    result.state.inputs = state.inputs :=
  congrArg (fun header : State.Header => header.inputs)
    (inferStatementsFuel_state_header success)

end Solcore.Frontend.SourceInference.Detail
