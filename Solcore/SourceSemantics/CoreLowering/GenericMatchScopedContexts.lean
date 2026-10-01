import Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchSelectionPrefix

/-! Finite match requests retain their ordered source binder identities.
The source context still comes from independent pattern typing and lexical
extension. Scope identity transports source declaration lookup only; no native
payload typing or runtime execution follows from the identity list. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
open Core Frontend SourceInference
open SourceCoreCompatibleDataMatches

/-- Refines the source-only context relation by the actual child's scope IDs.
The hidden scope includes the scrutinee slot and the outer lexical scope. -/
inductive ScopedContextFor (source : TypedSource) (parent : SourceSemantics.Context)
    (hiddenIds : List Resolved.LocalId) (scrutineeType : TypeSystem.Ty)
    (cases : List TypedMatchCase) (fallback : Option (List StatementId))
    (request : Request) : SourceSemantics.Context → Prop where
  | arm {arm binders arity context}
      (member : arm ∈ cases) (statements : request.statements = arm.body)
      (patternTyped : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
      (extended : BindersExtend source.owner parent binders context)
      (scopeIds : request.scope.map Prod.fst = (binders.map (·.id)).reverse ++ hiddenIds) :
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request context
  | default (statements : fallback = some request.statements)
      (scopeIds : request.scope.map Prod.fst = hiddenIds) :
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request parent

theorem ScopedContextFor.forget
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {request : Request}
    (related : ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child) :
    ContextFor source parent scrutineeType cases fallback request child := by
  cases related with
  | arm member statements typed extended _ => exact .arm member statements typed extended
  | default statements _ => exact .default statements

theorem ScopedContextFor.closed_fields
    {source : TypedSource} {parent child : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {fallback : Option (List StatementId)} {request : Request}
    (related : ScopedContextFor source parent hiddenIds scrutineeType cases fallback request child) :
    child.signatures = parent.signatures ∧ child.typeVariables = parent.typeVariables ∧
      child.residualTypeVariables = parent.residualTypeVariables :=
  related.forget.closed_fields

/-- Real marked arm allocation prepends the reversed ordered binder IDs. -/
theorem scope_binder_ids (bindings : List (TypedBinder × Ty)) (scope : Scope) :
    (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope).map Prod.fst =
      (bindings.map (fun binding => binding.1.id)).reverse ++ scope.map Prod.fst := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- An actual compiled arm supplies the refined request at its real scope.
The full source binders are authenticated before retaining their IDs. -/
theorem ScopedContextFor.compiled_arm
    {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {parent child : SourceSemantics.Context} {scope : Scope} {site : StatementId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {arm : TypedMatchCase} {pattern : Pattern}
    {binders : List TypedBinder} {arity : Nat} (body : Expr)
    (member : arm ∈ cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span
      scrutineeType arm.pattern pattern)
    (signatures : parent.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
    (extended : BindersExtend source.owner parent binders child) :
    ScopedContextFor source parent (scope.map Prod.fst) scrutineeType cases fallback
      ⟨CompatibleMatchCertificates.armScope scope pattern, arm.body, body⟩ child := by
  apply ScopedContextFor.arm member rfl typed extended
  rw [CompatibleMatchCertificates.armScope, scope_binder_ids]
  have ids := congrArg (List.map TypedBinder.id)
    (CompatiblePatternSourceBinders.Certificate.source_binders certificate signatures typed)
  simp only [List.map_map, Function.comp_def] at ids
  rw [ids]

/-- Native payload annotations may vary; the source declaration relation only
uses the ordered IDs. The hidden ID's source freshness remains explicit. -/
theorem ScopedContextFor.source_declarations
    {source : TypedSource} {parent child : SourceSemantics.Context} {scope : Scope}
    {site : StatementId} {node : StatementNode} {resolution : MatchResolution}
    {scrutineeType : TypeSystem.Ty} {request : Request}
    (found : source.lookupStatement? site = some node) (form : node.form = .matchWith resolution)
    (hidden : resolution.hiddenScrutinee ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope parent)
    (related : ScopedContextFor source parent (resolution.hiddenScrutinee :: scope.map Prod.fst)
      scrutineeType resolution.cases resolution.defaultBody request child) :
    CompatibleExpressionReads.ScopeDeclarations source request.scope child := by
  have hiddenDeclarations := CompatibleMatchArmScopes.scope_internal .unit hidden declarations
  cases related with
  | @arm arm binders arity context member statements typed extended sameIds =>
    let bindings : List (TypedBinder × Ty) := binders.map (fun binder => (binder, .unit))
    have sameBinders : bindings.map Prod.fst = binders := by simp [bindings, Function.comp_def]
    have members : ∀ binder ∈ bindings.map Prod.fst,
        binder ∈ SourceCoreDataPlaces.declaredBinders source := by
      rw [sameBinders]
      exact CompatibleMatchArmScopes.pattern_declarations found form member typed
    have bound := CompatibleMatchArmScopes.scope_binders (bindings := bindings)
      hiddenDeclarations members (sameBinders.symm ▸ extended)
    apply CompatibleMatchArmScopes.scope_ids (declarations := bound)
    rw [scope_binder_ids, sameIds]
    simp [bindings, List.map_map]
  | default statements sameIds =>
    exact CompatibleMatchArmScopes.scope_ids
      (first := (resolution.hiddenScrutinee, .unit) :: scope) sameIds.symm hiddenDeclarations

/-- Independent source selection supplies the arm context. The scope equation
comes separately from the actual selected allocation, not from a native type. -/
theorem ScopedContextFor.selected_arm
    {source : TypedSource} {control : ControlContext} {parent : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (request : Request) (sameBody : request.statements = body)
    (sameIds : request.scope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ hiddenIds)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings)) :
    ∃ context finalContext bodyFacts,
      ScopedContextFor source parent hiddenIds scrutineeType cases fallback request context ∧
      BindersExtend source.owner parent (bindings.map Prod.fst) context ∧
      StatementsHaveType source control context body finalContext bodyFacts ∧ bodyFacts ∈ facts := by
  cases selected with
  | head matched =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro patternTyped extended bodyTyped =>
        have binders := DataMatchSourceScopes.PatternMatches.binders patternTyped matched
        have ids := congrArg (fun xs => (xs.map TypedBinder.id).reverse ++ hiddenIds) binders
        simp only [List.map_map, Function.comp_def] at ids
        have ids := sameIds.trans ids
        exact ⟨_, _, _, .arm List.mem_cons_self sameBody patternTyped extended ids,
          binders ▸ extended, bodyTyped, List.mem_cons_self⟩
  | @tail arm rest _ _ notMatched selected =>
    cases typed with
    | cons head tail =>
      obtain ⟨context, finalContext, bodyFacts, child, extended, bodyTyped, member⟩ :=
        ScopedContextFor.selected_arm request sameBody sameIds tail selected
      have lifted : ScopedContextFor source parent hiddenIds scrutineeType (arm :: rest) fallback request context := by
        cases child with
        | arm member same typed extended ids => exact .arm (List.mem_cons_of_mem _ member) same typed extended ids
        | default same ids => exact .default same ids
      exact ⟨context, finalContext, bodyFacts, lifted, extended, bodyTyped, List.mem_cons_of_mem _ member⟩
termination_by cases.length

private theorem binder_context_unique
    {owner : Resolved.DeclarationId} {parent first second : SourceSemantics.Context} {binders : List TypedBinder}
    (left : BindersExtend owner parent binders first) (right : BindersExtend owner parent binders second) :
    first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases head
    cases right with
    | cons head tail => cases head; exact ih tail

theorem ScopedContextFor.selected_arm_at
    {source : TypedSource} {control : ControlContext} {parent armContext : SourceSemantics.Context}
    {hiddenIds : List Resolved.LocalId} {scrutineeType : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {fallback : Option (List StatementId)}
    {value : Dynamic.Value} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (request : Request) (sameBody : request.statements = body)
    (sameIds : request.scope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ hiddenIds)
    (typed : MatchCasesHaveType source control parent scrutineeType cases facts)
    (selected : Dynamic.MatchCasesSelect parent value cases fallback (.arm body bindings))
    (extended : BindersExtend source.owner parent (bindings.map Prod.fst) armContext) :
    ScopedContextFor source parent hiddenIds scrutineeType cases fallback request armContext := by
  obtain ⟨context, _, _, related, sameExtension, _, _⟩ :=
    ScopedContextFor.selected_arm request sameBody sameIds typed selected
  exact binder_context_unique sameExtension extended ▸ related

theorem selected_arm_ids
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {scope finalScope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)} {body : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody bodyCertificate scope environment heap type
      (.arm statements bindings) finalScope finalEnvironment finalHeap body) :
    finalScope.map Prod.fst = (bindings.map (fun binding => binding.1.id)).reverse ++ scope.map Prod.fst := by
  cases selected with
  | arm binders allocated certified =>
    rw [scope_binder_ids]
    have ids := congrArg (List.map TypedBinder.id) binders
    simp only [List.map_map, Function.comp_def] at ids
    rw [ids]

theorem selected_default_ids
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {scope finalScope : Scope}
    {environment finalEnvironment : Dynamic.Environment} {heap finalHeap : Dynamic.Heap}
    {type : Ty} {statements : List StatementId} {body : Expr}
    (selected : DataMatchBranchPrefix.SelectedBody bodyCertificate scope environment heap type
      (.default statements) finalScope finalEnvironment finalHeap body) :
    finalScope.map Prod.fst = scope.map Prod.fst := by
  cases selected
  rfl

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      MatchPatternInstruction.binderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [SourceCoreDataPlaces.instructionBinders, MatchPatternInstruction.binderIds] at ih ⊢ <;> exact ih

theorem typed_binder_ids {context : SourceSemantics.Context} {pattern : TypedMatchPattern}
    {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context pattern type binders arity) :
    binders.map (·.id) = pattern.binderIds := by
  rw [← CompatiblePatternSourceBinders.pattern_binders typed]
  cases resolution : pattern.resolution <;>
    simp only [SourceCoreDataPlaces.patternBinders, TypedMatchPattern.binderIds, resolution]
  all_goals try rfl
  all_goals exact instruction_ids _

theorem ScopedContextFor.compiled_arm_ids
    {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {parent child : SourceSemantics.Context} {scope : Scope} {site : StatementId}
    {scrutineeType : TypeSystem.Ty} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {arm : TypedMatchCase} {pattern : Pattern}
    {binders : List TypedBinder} {arity : Nat} (body : Expr)
    (member : arm ∈ cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span
      scrutineeType arm.pattern pattern)
    (typed : TypedMatchPatternHasType parent arm.pattern scrutineeType binders arity)
    (extended : BindersExtend source.owner parent binders child) :
    ScopedContextFor source parent (scope.map Prod.fst) scrutineeType cases fallback
      ⟨CompatibleMatchCertificates.armScope scope pattern, arm.body, body⟩ child := by
  apply ScopedContextFor.arm member rfl typed extended
  rw [CompatibleMatchCertificates.armScope, scope_binder_ids,
    CompatibleMatchSelectionPrefix.certificate_binding_ids certificate, ← typed_binder_ids typed]

end Solcore.SourceSemantics.CoreLowering.GenericMatchChildren
