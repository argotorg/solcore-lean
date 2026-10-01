import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

/-! Actual accepted arm scopes are paired with their independent source
contexts. Equal body lists do not erase distinct pattern binder identities.
The internal scrutinee does not become a source lexical declaration. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleMatchArmScopes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchArmScopes
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"match_arm_scopes", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "match_arm_scopes.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def hidden : Resolved.LocalId := ⟨owner, 2⟩
private def binder (index : Nat) : TypedBinder :=
  ⟨⟨owner, index⟩, toString index, .mono .unit, [], false, none⟩
private def pattern (index : Nat) : TypedMatchPattern := {
  source := .group span (.binder span (toString index)), type := .unit, resolution := .binder (binder index) }
private def arm (index : Nat) : TypedMatchCase := ⟨span, pattern index, []⟩
private def resolution : MatchResolution := ⟨⟨⟨owner, 1⟩⟩, hidden, [arm 0, arm 1], none, []⟩
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

theorem first_arm_scope : CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 0).pattern) (armContext 0) :=
  Certificate.hidden_arm_scope (site := site) (node := node) (resolution := resolution) (arm := arm 0)
    (scope := []) (payload := .unit) (compiled := (compiled 0).pattern) (by rfl) rfl (List.mem_cons_self)
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0) (extended 0) hiddenAbsent emptyScope

theorem second_arm_scope : CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 1).pattern) (armContext 1) :=
  Certificate.hidden_arm_scope (site := site) (node := node) (resolution := resolution) (arm := arm 1)
    (scope := []) (payload := .unit) (compiled := (compiled 1).pattern) (by rfl) rfl
    (List.mem_cons_of_mem _ (List.mem_cons_self))
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1) (extended 1) hiddenAbsent emptyScope

theorem actual_binder_identity : (compiled 0).pattern.bindings.map Prod.fst = [binder 0] ∧
    (compiled 1).pattern.bindings.map Prod.fst = [binder 1] :=
  ⟨CompatiblePatternSourceBinders.Certificate.source_binders
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 0) (compiled 0) firstAccepted) rfl (patternTyped 0),
    CompatiblePatternSourceBinders.Certificate.source_binders
    (CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source hiddenScope site span .unit
      (pattern 1) (compiled 1) secondAccepted) rfl (patternTyped 1)⟩

example : (arm 0).body = (arm 1).body := rfl
example : (armContext 0).locals ≠ (armContext 1).locals := by cbv; decide
theorem other_arm_context_is_invalid : ¬ CompatibleExpressionReads.ScopeDeclarations source
    (armScope hiddenScope (compiled 0).pattern) (armContext 1) := by
  intro declarations
  have selected := declarations (binder 0).id (binder 0) 0 .unit (by rfl) (by rfl)
  have selected := Resolved.LocalScope.lookup?_iff.mpr selected
  simp [armContext, context, Context.ofSignatures, Context.withLocal,
    Resolved.LocalScope.lookup?, binder] at selected
example : CompatibleExpressionReads.ScopeDeclarations source
    [((binder 0).id, .word), (hidden, .bool)] (armContext 0) :=
  scope_ids (by rfl) first_arm_scope
example : (armScope hiddenScope (compiled 0).pattern).map Prod.fst = [(binder 0).id, hidden] := by rfl
example : SourceCoreDataPlaces.rootBinder source hidden = .error (.missingBinding hidden) := by rfl
end Tests.SourceCoreCompatibleMatchArmScopes
