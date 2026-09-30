import Solcore.SourceSemantics.CoreLowering.GenericMatchPreservation

/-! Actual match acceptance and universal child preservation compile an
independent source trace to finite Core evaluation. The initial Core store contains an administrative
closure, so the hidden source location zero maps to Core location one. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreGenericMatchPreservation
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GenericMatchMeaning

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"generic_match", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "generic_match.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def scrutinee : ExpressionId := ⟨⟨owner, 1⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 0⟩
private def pattern : TypedMatchPattern := { source := .wildcard span span, type := .unit, resolution := .wildcard }
private def resolution : MatchResolution := ⟨scrutinee, hidden, [⟨span, pattern, []⟩], some [], []⟩
private def node : ExpressionNode := { id := scrutinee, span, type := .unit, form := .tuple [] }
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement site]
  nodes := [.statement ⟨site, span, .unit, .matchWith resolution⟩, .expression node]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨{}, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def compilation : SourceCoreDataMatches.Context := ⟨checked, ⟨[], [], [], [], [], []⟩, []⟩
private def model := GenericHeap.finitePayload compilation.checked.catalog compilation.signatures
private def context := SourceSemantics.Context.ofSignatures compilation.signatures
private def control : ControlContext := ⟨.unit, 0⟩
private def program : Program := ⟨compilation.signatures, [], []⟩
private def expression : SourceCoreDataMatches.ExpressionLowerer := fun _ _ _ id _ =>
  if id = scrutinee then .ok ⟨.unit, Core.LanguageResult.success .unit⟩ else .error (.missingExpression id)
private def body : SourceCoreDataMatches.BodyLowerer := fun _ _ _ statements _ _ _ =>
  if statements = [] then .ok (Core.LocalLoop.fallthrough .unit) else .error (.missingStatement site)
private def reasonAt : ExpressionId → Core.Word := fun _ => Core.Word.zero
private def expressionCertificate : DataMatchCertificates.ExpressionCertificate := fun _ id lowered =>
  id = scrutinee ∧ lowered = ⟨.unit, Core.LanguageResult.success .unit⟩
private def bodyCertificate : DataMatchCertificates.BodyCertificate := fun _ statements code =>
  statements = [] ∧ code = Core.LocalLoop.fallthrough .unit
private def faults : FaultRep := fun _ _ => False
private def code : Core.Expr :=
  match SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution .unit reasonAt Core.Word.zero with
  | .ok code => code
  | .error _ => .unit
private theorem accepted : SourceCoreDataMatches.lowerWithReasons compilation expression body 10 source [] site resolution
    .unit reasonAt Core.Word.zero = .ok code := by rfl
private theorem expressionExtract : ∀ fuel scope id lowered,
    expression fuel source scope id reasonAt = .ok lowered → expressionCertificate scope id lowered := by
  intro fuel scope id lowered accepted
  unfold expression at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted
private theorem bodyExtract : ∀ fuel scope statements code,
    body fuel source scope statements .unit reasonAt Core.Word.zero = .ok code → bodyCertificate scope statements code := by
  intro fuel scope statements code accepted
  unfold body at accepted
  split at accepted
  · exact ⟨by assumption, (Except.ok.inj accepted).symm⟩
  · cases accepted

private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds source
  decide
private theorem node_unique {selected : ExpressionNode} (contains : ContainsExpression source scrutinee selected) : selected = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans (show source.lookupExpression? scrutinee = some node from rfl))

private theorem unit_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (evaluated : Dynamic.ExpressionEvaluatesOutcome program context [] source environment before scrutinee outcome after) :
    outcome = .value .unit ∧ after = before := by
  cases evaluated with
  | value evaluated =>
    cases evaluated with
    | intro contains form coercions =>
      have same := node_unique contains
      subst_vars
      cases coercions
      cases form with
      | tuple _ elements packed => cases elements; cases packed; exact ⟨rfl, rfl⟩
    | generalizedLocal contains form =>
      have same := node_unique contains
      subst_vars
      cases form
  | fault fault =>
    cases fault with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent
        (lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl)))
    | form contains fault =>
      have same := node_unique contains
      subst_vars
      cases fault with
      | tuple _ elements => cases elements
    | coercion contains form fault =>
      have same := node_unique contains
      subst_vars
      cases fault
    | generalizedLocalRequirement contains form | generalizedLocalCoercion contains form =>
      have same := node_unique contains
      subst_vars
      cases form

private theorem expressionMeaning : GenericMatchPreservation.ExpressionPreserves compilation model program context [] source expressionCertificate faults := by
  intro scope id lowered certified selected found mapping world admin environment canonical actual before store ξ outcome after
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  have same : selected = node := Option.some.inj (found.symm.trans (show source.lookupExpression? scrutinee = some node from rfl))
  subst selected
  obtain ⟨rfl, rfl⟩ := unit_outcome evaluated
  exact ⟨_, store, mapping, world, .inRight .unit, .value .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem bodyMeaning : GenericMatchPreservation.BodyPreserves compilation model program control [] source bodyCertificate .unit .unit faults := by
  intro scope statements code certified context staticFinal facts typed mapping world admin environment canonical actual before store ξ finalContext outcome after
    environments heaps locals layout evaluated
  rcases certified with ⟨rfl, rfl⟩
  cases evaluated with
  | control executed =>
    cases executed
    exact ⟨_, store, mapping, world, .inRight (.inLeft (.inLeft .unit)), .fallthrough _, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | fault fault => cases fault

private theorem valid : DataPatternLeaves.ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, SourceSemantics.Context.ofSignatures],
    by intro requirement member; simp [context, SourceSemantics.Context.ofSignatures] at member⟩
}
private theorem casesTyped : MatchCasesHaveType source control context .unit resolution.cases [.empty] :=
  .cons (.intro ⟨rfl, .wildcard, .wildcard, ⟨by decide, by decide⟩⟩ (.nil _) (.nil _ _)) (.nil _ _ _)
private theorem defaultTyped : ∀ {statements}, resolution.defaultBody = some statements →
    ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts := by
  intro statements same
  have empty : statements = [] := (Option.some.inj same).symm
  subst statements
  exact ⟨context, .empty, .nil _ _⟩

private def admin : Core.Value := .closure .unit .unit .unit []
private def initialStore : Core.Store := [admin]
private def world : Core.StoreTyping := [.function .unit .unit]
private def finalStore : Core.Store := [admin, .inRight .unit .unit]
private def result : Core.Value := .inRight .word (.inLeft Core.LocalLoop.transferType (.inLeft .unit .unit))
private theorem run : Core.runStateful 150 (Core.State.initial code [] initialStore) = .done result finalStore := by cbv
private theorem heaps : GenericHeap.HeapRepresents model [] world ⟨[]⟩ initialStore :=
  GenericHeap.HeapRepresents.empty.allocate_administrative (.closure .nil .unit)

private theorem sourceExecution : Dynamic.StatementExecutesOutcome program context [] source [] ⟨[]⟩ site context
    (.fallthrough []) ⟨[⟨.unit, some .unit, none⟩]⟩ := by
  apply Dynamic.StatementExecutesOutcome.control
  apply Dynamic.StatementExecutes.matchArm
      (contains := show ContainsStatement source site ⟨site, span, .unit, .matchWith resolution⟩ from ⟨by simp [source], rfl⟩)
      (form_eq := rfl) (scrutinee_contains := lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl))
      (scrutinee_evaluates := Dynamic.ExpressionEvaluates.intro
        (lookupExpression?_sound (show source.lookupExpression? scrutinee = some node from rfl))
        (.tuple rfl .nil .nil) .nil)
      (allocate_hidden := Dynamic.Heap.Allocates.append)
      (select := Dynamic.MatchCasesSelect.head (Dynamic.PatternMatches.intro .wildcard .wildcard))
      (binders_eq := rfl) (values_eq := rfl) (binders_extend := BindersExtend.nil context)
      (allocate_bindings := Dynamic.BindersAllocate.nil _ _) (execute := Dynamic.StatementsExecute.nil)

/-- Independent source execution, actual lowering acceptance and universal
child preservation yield the Core evaluation with final heap/frame evidence. -/
example : ∃ value store finalMap finalWorld,
    Core.Evaluates [] initialStore code value store ∧
    OutcomeRepresents model finalMap finalWorld .unit .unit faults (.fallthrough []) value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld ⟨[⟨.unit, some .unit, none⟩]⟩ store ∧
    GeneralHeap.LocationMap.Extends [] finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved [] initialStore finalMap store ∧
    Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[⟨.unit, some .unit, none⟩]⟩ := by
  have result := GenericMatchPreservation.lowerWithReasons_preserves GenericMatchAllocation.finite_includes
    expressionExtract bodyExtract accepted expressionMeaning bodyMeaning valid unique
    (show source.lookupExpression? resolution.scrutinee = some node from rfl)
    casesTyped defaultTyped (DataHeap.EnvRepresents.nil Core.RuntimeEnvironmentHasTypes.nil) heaps
    Dynamic.EnvironmentAgrees.nil (ξ := Core.Renaming.id)
    (show Core.ReadOnly.EnvironmentsAgree Core.Renaming.id [] [] from fun {_ _} found => found) sourceExecution
  simpa [model] using result

end Tests.SourceCoreGenericMatchPreservation
