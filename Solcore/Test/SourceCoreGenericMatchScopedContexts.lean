import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts

/-! Same-body arms and a same-body default retain different source scope IDs.
Actual compiled pattern scopes select the right independent context, while
duplicated equal requests remain in source order. Payload annotations are not
used to infer source context or native typing. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreGenericMatchScopedContexts
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes GenericMatchChildren
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_scoped_contexts", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_scoped_contexts.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], some [], []⟩
private def node : StatementNode := ⟨site, span, .unit, .matchWith resolution⟩
private def source : TypedSource := {owner, inputs := [], roots := [.statement site], nodes := [.statement node]}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem admitted : TypeAdmissible context .unit := .unit (by simp [TypeParameterBindersWellFormed, context, Context.ofSignatures])
private theorem patternTyped (index : Nat) : TypedMatchPatternHasType context (pattern index) .unit [binder index] 0 := {
  type_eq := rfl, source_represents := .group (.binder rfl)
  resolution_type := .binder {
    scheme_eq := rfl, runtime := rfl
    wellFormed := by intro declaration installed; cases installed }
  binders_distinct := ⟨by simp, by simp⟩ }
private def armContext (index : Nat) : SourceSemantics.Context :=
  context.withLocal (binder index).id (binder index).scheme []
private theorem extended (index : Nat) : BindersExtend source.owner context [binder index] (armContext index) := by
  apply BindersExtend.cons (middle := armContext index)
  · apply BinderExtends.intro
    · exact {
        owned := rfl, scheme := SchemeWellFormed.monoAdmissible admitted
        quantified_fresh := by intro metavariable member; cases member
        monomorphic_requirements_empty := by intro mono; rfl }
    · simp [LocalFresh, context, Context.ofSignatures]
  · exact .nil _
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 20 [.unit]).toOption.get catalogExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some checked.catalog.definitions⟩
private def hiddenScope : Scope := [(hidden, .unit)]
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (index : Nat) : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source hiddenScope site span .unit (pattern index) with
  | .ok result => result | .error _ => fallback
private theorem firstAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 0) = .ok (compiled 0) := by rfl
private theorem secondAccepted : compilePattern compilation 20 source hiddenScope site span .unit (pattern 1) = .ok (compiled 1) := by rfl
private theorem emptyScope : CompatibleExpressionReads.ScopeDeclarations source [] context := by
  intro binder declared index type selected authentic
  cases selected
private theorem hiddenAbsent : hidden ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id) := by
  simp [SourceCoreDataPlaces.declaredBinders, SourceCoreDataPlaces.patternBinders,
    source, node, resolution, arm, pattern, binder, hidden]

private def request (index : Nat) : Request :=
  ⟨armScope hiddenScope (compiled index).pattern, [], LocalLoop.fallthrough .unit⟩
private def defaultRequest : Request := ⟨hiddenScope, [], LocalLoop.fallthrough .unit⟩

theorem first_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 0) (armContext 0) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 0)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0)

theorem second_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    (request 1) (armContext 1) :=
  ScopedContextFor.compiled_arm (scope := hiddenScope) (arm := arm 1)
    (cases := resolution.cases) (fallback := resolution.defaultBody)
    (LocalLoop.fallthrough .unit) (List.mem_cons_of_mem _ List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1)

theorem default_scoped : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
    defaultRequest context := .default rfl rfl

theorem first_declarations : CompatibleExpressionReads.ScopeDeclarations source (request 0).scope (armContext 0) :=
  first_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

theorem second_declarations : CompatibleExpressionReads.ScopeDeclarations source (request 1).scope (armContext 1) :=
  second_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

theorem default_declarations : CompatibleExpressionReads.ScopeDeclarations source defaultRequest.scope context :=
  default_scoped.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope

private theorem wrong_declarations : ¬ CompatibleExpressionReads.ScopeDeclarations source (request 0).scope (armContext 1) := by
  intro declarations
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  have selected := Resolved.LocalScope.lookup?_iff.mpr selected
  simp [armContext, context, Context.ofSignatures, Context.withLocal, Resolved.LocalScope.lookup?, binder] at selected

/-- The old source-only relation admitted this context for the shared body.
Its scope refinement excludes it without using native payload types. -/
theorem wrong_arm_excluded : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody (request 0) (armContext 1) := by
  intro related
  exact wrong_declarations
    (related.source_declarations (scope := []) (site := site) (node := node) (by rfl) rfl hiddenAbsent emptyScope)

theorem old_relation_admits_other_context : ContextFor source context .unit resolution.cases
    resolution.defaultBody (request 0) (armContext 1) :=
  .arm (List.mem_cons_of_mem _ List.mem_cons_self) rfl (patternTyped 1) (extended 1)

theorem arm_cannot_be_default : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody (request 0) context := by
  intro related
  have declarations := related.source_declarations (scope := []) (site := site) (node := node)
    (by rfl) rfl hiddenAbsent emptyScope
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  cases selected

theorem default_cannot_be_arm : ¬ ScopedContextFor source context [hidden] .unit resolution.cases
    resolution.defaultBody defaultRequest (armContext 0) := by
  intro related
  cases related with
  | @arm actual binders arity _ member statements typed extended ids =>
    have member : actual = arm 0 ∨ actual = arm 1 := by simpa [resolution] using member
    rcases member with rfl | rfl
    · have same := CompatiblePatternSourceBinders.pattern_binders typed
      simp [SourceCoreDataPlaces.patternBinders, arm, pattern] at same
      rw [← same] at ids
      have length := congrArg List.length ids
      simp [defaultRequest, hiddenScope] at length
    · have same := CompatiblePatternSourceBinders.pattern_binders typed
      simp [SourceCoreDataPlaces.patternBinders, arm, pattern] at same
      rw [← same] at ids
      have length := congrArg List.length ids
      simp [defaultRequest, hiddenScope] at length

theorem duplicate_requests_preserved :
    let requests := [request 0, request 0, request 1, defaultRequest]
    requests.length = 4 ∧ requests[0]? = requests[1]? ∧
      Occurs requests (request 0).scope [] (LocalLoop.fallthrough .unit) := by
  exact ⟨rfl, rfl, List.mem_cons_self⟩

theorem raw_payload_annotations_are_independent :
    let altered : Request := ⟨[((binder 0).id, .word), (hidden, .bool)], [], .unit⟩
    ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody altered (armContext 0) ∧
      CompatibleExpressionReads.ScopeDeclarations source altered.scope (armContext 0) := by
  have related : ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
      ⟨[((binder 0).id, .word), (hidden, .bool)], [], .unit⟩ (armContext 0) :=
    .arm List.mem_cons_self rfl (patternTyped 0) (extended 0) rfl
  exact ⟨related, related.source_declarations (scope := []) (site := site) (node := node)
    (by rfl) rfl hiddenAbsent emptyScope⟩

theorem selected_source_arm_context (control : ControlContext) :
    ScopedContextFor source context [hidden] .unit resolution.cases resolution.defaultBody
      (request 0) (armContext 0) := by
  have typed : MatchCasesHaveType source control context .unit resolution.cases [.empty, .empty] :=
    .cons (.intro (patternTyped 0) (extended 0) (.nil control _))
      (.cons (.intro (patternTyped 1) (extended 1) (.nil control _)) (.nil _ _ _))
  have selected : Dynamic.MatchCasesSelect context .unit resolution.cases resolution.defaultBody
      (.arm [] [(binder 0, .unit)]) := .head (.intro (.group (.binder rfl)) .binder)
  exact ScopedContextFor.selected_arm_at (request 0) rfl rfl typed selected (extended 0)

theorem allocation_order :
    ([(binder 0, Ty.word), (binder 1, Ty.bool)].foldl
      (fun scope binding => (binding.1.id, binding.2) :: scope) hiddenScope).map Prod.fst =
      [(binder 1).id, (binder 0).id, hidden] :=
  scope_binder_ids _ _

example : (request 0).statements = (request 1).statements ∧ (request 0).statements = defaultRequest.statements := ⟨rfl, rfl⟩
example : (request 0).scope.map Prod.fst ≠ (request 1).scope.map Prod.fst := by decide
example : (request 0).scope.map Prod.fst ≠ defaultRequest.scope.map Prod.fst := by decide
example : ContextFor source context .unit resolution.cases resolution.defaultBody (request 0) (armContext 0) := first_scoped.forget
private theorem hiddenSourceFresh : GenericImperativeMatch.MatchHiddenFresh source := by
  intro id actualNode actualResolution found form
  have sameNode : actualNode = node := by
    have member := (lookupStatement?_sound found).1
    simpa [source] using member
  subst actualNode
  have sameResolution : actualResolution = resolution := StatementForm.matchWith.inj form.symm
  subst actualResolution
  exact hiddenAbsent

theorem automatic_child_scopes {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {definitions : DataEnvironment} {administrative : Core.Context} :
    GenericImperativeMatch.MatchChildStatic compilation source certificates definitions administrative :=
  GenericImperativeMatch.MatchChildStatic.of_hidden hiddenSourceFresh

end Tests.SourceCoreGenericMatchScopedContexts
