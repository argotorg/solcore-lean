import Solcore.SourceSemantics.Internal.Compiled.BodySelection
import Solcore.SourceSemantics.Internal.Compiled.Finalization
import Solcore.Frontend.SourceInference.Internal.Continuations
import Solcore.SourceSemantics.SourceInferenceRetainedRequirementFormation
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyFinalization
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization
import Solcore.SourceSemantics.SourceInferenceStatementPrivacyContinuation
import Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary
import Solcore.SourceSemantics.SourceInferenceBackedStatementPrivacy
import Solcore.SourceSemantics.SourceInferenceActiveStatementPosition
import Solcore.SourceSemantics.SourceInferenceNormalizedRequirementFormation

/-!
# Privacy of initialized declarations

An original initialized declaration supplies its generalization receipt, allocator bounds and
certificate. Prior binders stay private through its initializer, and return finalization keeps that
privacy.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledTopLevelInitializerContinuation
/-! Selected accepted compilation supplies a top-level initializer's actual
return state and its continuation through the remaining body, return unification
and final solver. No initializer-typing or substitution-continuation premise is
supplied by the caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem

structure InitializerContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.Statement) where
  childFuel : Nat
  entry : State
  result : Detail.StatementResult
  receipt : LocalLetRequirementTiming.Receipt childFuel
    (context compiled.program.environment compiled.program.signatures
      selected.signature selected.body.declaration) source entry result
  retained : result.state.nodes <+: selected.body.body.state.nodes
  ready : receipt.ready.InferenceReady
  bodyContinuation : receipt.ready.InferenceProgress selected.body.body.state
  finalContinuation : receipt.ready.InferenceProgress selected.body.resources.finalState

namespace InitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem substitution (continuation : InitializerContinuation selected source) :
    selected.body.finalized.substitution.SemanticallyExtends
      continuation.receipt.ready.inference.substitution := by
  rw [selected.body.resources.substitution_eq]
  exact continuation.finalContinuation.substitution_extends

/-- The same actual declaration reaches the finalizer's original node table. -/
theorem original_retained (continuation : InitializerContinuation selected source) :
    .statement {
      id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
      form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id)
    } ∈ selected.body.returned.nodes := by
  rw [selected.body.returned_nodes]
  exact continuation.retained.subset continuation.receipt.recorded

/-- Capture avoidance is validated for this initializer's exact allocated binder. -/
theorem no_capture (continuation : InitializerContinuation selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution
      continuation.receipt.binding.1 := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement {
    id := continuation.entry.allocateStatementId.1, span := source.span, type := .unit,
    form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id)
  }, continuation.original_retained, ?_⟩
  exact List.mem_singleton_self _

end InitializerContinuation

theorem BodySelection.topLevelInitializer {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (InitializerContinuation selected source) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) formation canonical progress.returnBelow selected.body.inferred position
  obtain ⟨childFuel, receipt, ready, bodyContinuation⟩ :=
    occurrence.initialized form formation canonical
  exact ⟨⟨childFuel, occurrence.entry, occurrence.result, receipt, occurrence.retained, ready, bodyContinuation,
    bodyContinuation.trans (progress.returnUnification.trans progress.finalization)⟩⟩

/-- The entry is selected by the real specialization row. The premise names
an original source position, rather than an independently reconstructed body. -/
theorem compile_top_level_initializer_continuation {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          Nonempty (InitializerContinuation selected.toBodySelection source) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected, ?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.topLevelInitializer (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.topLevelInitializer {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (InitializerContinuation selected.toBodySelection source) :=
  selected.toBodySelection.topLevelInitializer checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledForHeaderContinuation
/-! Actual original for-header initializers reach the same selected finalizer,
including the condition, body, post items and later top-level statements. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem ForStatementInferenceContinuation

structure HeaderInitializerContinuation {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel) (source : Syntax.ForItem) where
  inferenceContext : SourceInference.Context
  original : StatementNode
  originalPresent : .statement original ∈ selected.body.body.state.nodes
  header : HeaderContinuation inferenceContext source selected.body.body.state original
  finalContinuation : header.receipt.ready.InferenceProgress selected.body.resources.finalState

namespace HeaderInitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.ForItem}

theorem substitution (continuation : HeaderInitializerContinuation selected source) :
    selected.body.finalized.substitution.SemanticallyExtends
      continuation.header.receipt.ready.inference.substitution := by
  rw [selected.body.resources.substitution_eq]
  exact continuation.finalContinuation.substitution_extends

theorem no_capture (continuation : HeaderInitializerContinuation selected source) :
    Detail.LocalBinderInstantiationNoCapture selected.body.finalized.substitution
      continuation.header.receipt.binding.1 := by
  apply selected.body.resources.local_no_capture
  unfold TypedSource.initializedLetBinders
  apply List.mem_flatMap.mpr
  refine ⟨.statement continuation.original, ?_, continuation.header.retained⟩
  change .statement continuation.original ∈ selected.body.returned.nodes
  rw [selected.body.returned_nodes]
  exact continuation.originalPresent

end HeaderInitializerContinuation

theorem BodySelection.topLevelForHeader {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement}
    (statementPosition : selected.signature.source.value.body.value[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderInitializerContinuation selected source) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := StatementInferenceContinuation.of_position progress.initialReady
    (State.initial_nodesBelowNextOccurrence _ _ _) formation canonical progress.returnBelow
    selected.body.inferred statementPosition
  have accepted := occurrence.accepted
  cases fuelEq : occurrence.fuel with
  | zero => simp [fuelEq, Detail.inferStatementFuel] at accepted
  | succ childFuel =>
      rw [fuelEq] at accepted
      obtain ⟨receipt⟩ := ForStatementInferenceContinuation.of_accepted statementForm accepted
      obtain ⟨header⟩ := receipt.initialized_header occurrence.ready formation canonical
        (progress.returnBelow.weaken occurrence.before.next_le) isPost position form
      let continued := header.continuation.trans occurrence.continuation
      exact ⟨{
        inferenceContext := _
        original := _
        originalPresent := occurrence.retained.subset receipt.recorded
        header := {
          childFuel := header.childFuel, entry := header.entry, result := header.result,
          receipt := header.receipt, ready := header.ready, continuation := continued,
          retained := header.retained }
        finalContinuation := continued.trans (progress.returnUnification.trans progress.finalization)
      }⟩

/-- Compiler success supplies one original check for all actual for-header
positions of the selected function. -/
theorem compile_top_level_for_header_continuation {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {statementIndex : Nat} {statement : Syntax.Statement},
        selected.signature.source.value.body.value[statementIndex]? = some statement →
        ∀ {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
          {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan},
          statement.value = .forLoop headerSpan initializers condition post body →
          ∀ (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem},
            (if isPost then post else initializers)[headerIndex]? = some source →
            ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
              source.value = .letDecl name annotation (some initializer) →
              Nonempty (HeaderInitializerContinuation selected.toBodySelection source) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected, ?_⟩
  intro statementIndex statement statementPosition initializers post condition body headerSpan statementForm
    isPost headerIndex source position name annotation initializer form
  exact selected.toBodySelection.topLevelForHeader (SourceCoreCompiler.compile_checked_source accepted)
    statementPosition statementForm isPost position form


theorem Selected.topLevelForHeader {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {statementIndex : Nat} {statement : Syntax.Statement}
    (statementPosition : selected.signature.source.value.body.value[statementIndex]? = some statement)
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Located (List Syntax.Statement)} {headerSpan : Syntax.SourceSpan}
    (statementForm : statement.value = .forLoop headerSpan initializers condition post body)
    (isPost : Bool) {headerIndex : Nat} {source : Syntax.ForItem}
    (position : (if isPost then post else initializers)[headerIndex]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    Nonempty (HeaderInitializerContinuation selected.toBodySelection source) :=
  selected.toBodySelection.topLevelForHeader checked statementPosition statementForm isPost position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledForHeaderRequirementFormation
/-! The selected initializer's actual continuation and finalizer discharge the
normalization assumptions of retained requirement formation. Only the genuine
issuance formation remains to be supplied by the recursive source traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.HeaderInitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.ForItem}

theorem retained_formation (continuation : HeaderInitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed (localSchemeInitializerContext target
      (continuation.header.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.body.declaration.id)
    (residual : target.residualTypeVariables = true)
    (issued : ∀ requirement ∈ continuation.header.receipt.ready.requirements,
      requirement.id ∈ localSchemeTemplateIds continuation.header.receipt.binding.1 →
        PredicateAdmissible (localSchemeInitializerContext target
          (continuation.header.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
          requirement.predicate) :
    RetainedRequirementPredicateFormationAt continuation.header.receipt.ready
      continuation.header.receipt.binding.1 selected.body.finalized.substitution target := by
  exact SourceInferenceRequirementFormation.retained_formation_of_issuances
    selected.body.resources binders signatures parameters owner residual
    continuation.substitution continuation.no_capture issued

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.HeaderInitializerContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReturnFinalization
/-! Actual return unification against the declared closed signature and the
actual finalizer preserve private variables, including generalized locals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem apply_closed (substitution : Substitution) {type : Ty}
    (closed : type.VariablesBelow 0) : substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type
    (fun v _ occurs => False.elim (Nat.not_lt_zero _ (closed v occurs)))

private theorem closed_right_range {left right : Ty} {substitution : Substitution}
    (closed : right.VariablesBelow 0)
    (accepted : Unification.unifyTypes left right = .ok substitution) :
    ∀ v replacement, (v,replacement) ∈ substitution → replacement.VariablesBelow 0 := by
  have matched : substitution.apply left = right :=
    (Unification.unifyTypes_sound accepted).trans (apply_closed substitution closed)
  have solved := Unification.unifyTypes_solvedBelow
    ((Ty.variablesBelow_nextVariable left).weaken (Nat.le_max_left _ _))
    ((Ty.variablesBelow_nextVariable right).weaken (Nat.le_max_right _ _)) accepted
  intro v replacement member candidate occurs
  have inDomain : v ∈ substitution.domain := List.mem_map.mpr ⟨(v,replacement),member,rfl⟩
  obtain ⟨constraint,present,origin⟩ := Unification.unify_domain_origin accepted inDomain
  have same : constraint = { left, right } := List.mem_singleton.mp present
  subst constraint
  have leftOrigin : v ∈ left.freeVariables := origin.resolve_right
    (fun occurs => Nat.not_lt_zero _ (closed v occurs))
  have found := StructuralSubstitution.Substitution.lookup?_eq_some_of_mem_of_domain_nodup
    solved.domain_nodup member
  have image : candidate ∈ (substitution.apply (.variable v)).freeVariables := by
    simpa only [Substitution.apply,found,Option.getD_some] using occurs
  have inResult := MonomorphicGeneralization.replacement_occurs substitution left leftOrigin image
  rw [matched] at inResult
  exact closed candidate inResult

/-- Successful unification with a declared type containing no flexible
variables can only remove flexible variables from other live types. -/
theorem unify_closed_right_private {protectedVars : List TypeVarId}
    {before after : State} {left right : Ty}
    (closed : right.VariablesBelow 0)
    (accepted : Detail.unify before left right = .ok after) :
    SafeTransport protectedVars before after := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at accepted
    cases accepted
    unfold InferState.unify at unified
    have sameRight : before.inference.resolve right = right := apply_closed _ closed
    rw [sameRight] at unified
    cases update : Unification.unifyTypes (before.inference.resolve left) right with
    | error error => simp [update,bind,Except.bind] at unified
    | ok substitution =>
      simp only [update,bind,Except.bind,pure,Pure.pure,Except.pure,Except.ok.injEq] at unified
      cases unified
      have range : substitution.RangeAvoidsDomain (guard protectedVars) := by
        intro v replacement member candidate occurs
        exact False.elim (Nat.not_lt_zero _ (closed_right_range closed update v replacement member candidate occurs))
      intro type safe
      simpa only [Safe,State.resolve,InferState.resolve,Substitution.compose_apply] using Avoids.apply safe range

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables

namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- A selected actual checker receipt supplies the closed return signature,
its successful unification and its finalizer. No return-type privacy or
post-defaulting transport law is requested from the caller. -/
theorem BodySelection.finishPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (protectedVars : List TypeVarId) :
    ∀ type, Safe protectedVars selected.body.body.state type →
      Avoids protectedVars (selected.body.finalized.substitution.apply type) := by
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have returned : SafeTransport protectedVars selected.body.body.state selected.body.returned :=
    unify_closed_right_private closed selected.body.unified
  intro type safe
  exact finalize_private selected.body.finalization type (returned type safe)


theorem Selected.finishPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (protectedVars : List TypeVarId) :
    ∀ type, Safe protectedVars selected.body.body.state type →
      Avoids protectedVars (selected.body.finalized.substitution.apply type) :=
  selected.toBodySelection.finishPrivacy checked protectedVars

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledStatementPrivacyContinuation
/-! Original selected syntax positions carry their real later inference and
finalization. Only privacy of the newly chosen quantifiers at the declaration
boundary remains for the generalization proof to establish. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

/-- The actual checker result supplies the continuation through all later
statements, return unification and finalization for a selected source position. -/
theorem BodySelection.statementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    ∃ occurrence : StatementPrivacyOccurrence
        (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
        source (Ty.productMany selected.signature.returnTypes)
        (initial selected.signature selected.body.declaration) selected.body.body.state,
      ∀ protectedVars : List TypeVarId,
        (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
        LiveBindersSafe protectedVars occurrence.result.state →
        (∀ type, Safe protectedVars occurrence.result.state type →
          Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ occurrence.result.state.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids protectedVars (selected.body.finalized.substitution.apply type)) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence⟩ := statementPrivacyOccurrence_of_position progress.initialReady
    (State.initial_requirementsWellFormed _ _ _) (State.initial_nodesBelowNextOccurrence _ _ _)
    catalog formation canonical progress.returnBelow selected.body.inferred position
  refine ⟨occurrence,?_⟩
  intro protectedVars bound live
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have continuation := occurrence.privacy protectedVars bound live
    (safe_closed protectedVars occurrence.result.state closed)
  constructor
  · intro type safe
    exact selected.finishPrivacy checked protectedVars type (continuation.1 type safe)
  · intro requirement member fresh type typeMember
    exact selected.finishPrivacy checked protectedVars type
      (continuation.2 requirement member fresh type typeMember)

/-- A successful public compilation chooses the original body and all its
actual statement continuations; no whole-program body typing is assumed. -/
theorem compile_statement_privacy {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∃ occurrence : StatementPrivacyOccurrence
            (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
            source (Ty.productMany selected.signature.returnTypes)
            (initial selected.signature selected.body.declaration) selected.body.body.state,
          ∀ protectedVars : List TypeVarId,
            (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
            LiveBindersSafe protectedVars occurrence.result.state →
            (∀ type, Safe protectedVars occurrence.result.state type →
              Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
            (∀ requirement ∈ selected.body.body.state.requirements,
              requirement ∉ occurrence.result.state.requirements →
              ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
                Avoids protectedVars (selected.body.finalized.substitution.apply type)) := by
  obtain ⟨selected⟩ := of_compile accepted member
  exact ⟨selected,fun position => selected.toBodySelection.statementPrivacy
    (SourceCoreCompiler.compile_checked_source accepted) position⟩


theorem Selected.statementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source) :
    ∃ occurrence : StatementPrivacyOccurrence
        (context compiled.program.environment compiled.program.signatures selected.signature selected.body.declaration)
        source (Ty.productMany selected.signature.returnTypes)
        (initial selected.signature selected.body.declaration) selected.body.body.state,
      ∀ protectedVars : List TypeVarId,
        (∀ v ∈ protectedVars, v.index < occurrence.result.state.inference.next) →
        LiveBindersSafe protectedVars occurrence.result.state →
        (∀ type, Safe protectedVars occurrence.result.state type →
          Avoids protectedVars (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ occurrence.result.state.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids protectedVars (selected.body.finalized.substitution.apply type)) :=
  selected.toBodySelection.statementPrivacy checked position

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializedStatementPrivacy
/-! An original initialized declaration supplies its actual generalization
receipt, allocator bounds, retained binder and final substitution. The genuine
older-template provenance closes its declaration-boundary privacy condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

namespace InitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem retained_binding (continuation : InitializerContinuation selected source) :
    continuation.receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
  unfold TypedSource.initializedLetBinders
  exact List.mem_flatMap.mpr ⟨_,continuation.original_retained,List.mem_singleton_self _⟩

/-- The new quantified variables are actual free variables of the initializer's
resolved output, and therefore lie below its real returned allocator. -/
theorem quantified_below (continuation : InitializerContinuation selected source)
    (valueBelow : continuation.receipt.value.type.VariablesBelow continuation.receipt.ready.inference.next) :
    ∀ q ∈ continuation.receipt.binding.1.scheme.quantified,
      q.index < continuation.result.state.inference.next := by
  intro q member
  have resolvedBelow := continuation.ready.solved.variablesBelow_apply valueBelow
  have occurs : q ∈ (continuation.receipt.ready.resolve continuation.receipt.value.type).freeVariables := by
    exact (List.mem_filter.mp member).1
  have bound := resolvedBelow q occurs
  rwa [continuation.receipt.inference_eq]

/-- Actual finalizer capture checks close the new and older live binder privacy
conditions; no live-privacy or quantifier-disjointness premise is supplied. -/
theorem generalized_live (continuation : InitializerContinuation selected source)
    (origins : ActiveBinderCaptureOrigins continuation.receipt.ready
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (backed : ∀ older ∈ continuation.receipt.ready.localBinders,
      BinderTemplatesBefore continuation.receipt.ready continuation.entry.nextRequirement older) :
    LiveBindersSafe continuation.receipt.binding.1.scheme.quantified continuation.result.state := by
  have live := allocate_generalized_live_from_finalizer selected.body.resources
    continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
    continuation.receipt.name.value (some continuation.receipt.name.span) false
    (origins.withLocals continuation.receipt.locals) continuation.substitution backed continuation.retained_binding
  have same : continuation.result.state.inference = continuation.receipt.binding.2.inference :=
    congrArg (fun result : Detail.StatementResult => result.state.inference) continuation.receipt.completed
  have binders : continuation.result.state.localBinders = continuation.receipt.binding.2.localBinders :=
    congrArg (fun result : Detail.StatementResult => result.state.localBinders) continuation.receipt.completed
  intro binder member
  exact (live binder (binders ▸ member)).transport (.of_substitution_eq (congrArg InferState.substitution same))

end InitializerContinuation

/-- Both the generalization and later privacy use one actual statement call
at the chosen original source position. The remaining producer inputs describe
only the old live binders and their genuine pre-initializer template rows. -/
theorem BodySelection.initializedStatementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected source,
      ∀ _origins : ActiveBinderCaptureOrigins actual.receipt.ready
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)),
        (∀ older ∈ actual.receipt.ready.localBinders,
          BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older) →
        (∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
          Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ actual.receipt.ready.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence,privacy⟩ := selected.statementPrivacy checked position
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ := occurrence.toOccurrence.initialized form formation canonical
  let actual : InitializerContinuation selected source := {
    childFuel := childFuel,entry := occurrence.entry,result := occurrence.result,receipt := receipt,
    retained := occurrence.retained,ready := ready,bodyContinuation := bodyContinuation,
    finalContinuation := bodyContinuation.trans (progress.returnUnification.trans progress.finalization) }
  refine ⟨actual,?_⟩
  intro origins backed
  have inferred := receipt.initializer_inference occurrence.ready formation canonical
  have bound := actual.quantified_below inferred.2.2
  have live := actual.generalized_live origins backed
  have finished := privacy actual.receipt.binding.1.scheme.quantified bound live
  constructor
  · intro type safe
    apply finished.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply finished.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

/-- Public compilation chooses the same selected checker body before the
initialized-declaration boundary is connected to its actual finalizer. -/
theorem compile_initialized_statement_privacy {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          ∃ actual : InitializerContinuation selected.toBodySelection source,
            ∀ _origins : ActiveBinderCaptureOrigins actual.receipt.ready
                (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)),
              (∀ older ∈ actual.receipt.ready.localBinders,
                BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older) →
              (∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
                Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) ∧
              (∀ requirement ∈ selected.body.body.state.requirements,
                requirement ∉ actual.receipt.ready.requirements →
                ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
                  Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedStatementPrivacy (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedStatementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected.toBodySelection source,
      ∀ _origins : ActiveBinderCaptureOrigins actual.receipt.ready
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)),
        (∀ older ∈ actual.receipt.ready.localBinders,
          BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older) →
        (∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
          Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ actual.receipt.ready.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) :=
  selected.toBodySelection.initializedStatementPrivacy checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializedPrivacyProvenance
/-! The actual original statement position provides both capture origins and
pre-initializer raw template rows. Together with the real finalizer these close
initialized-declaration privacy without caller-supplied boundary invariants. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

private theorem return_owner {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.owner = before.owner := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified,Detail.liftUnification,bind,Except.bind] at accepted
  | ok inference =>
    simp only [unified,Detail.liftUnification,bind,Except.bind,pure,Pure.pure,Except.pure] at accepted
    cases accepted
    rfl

structure InitializedStatementPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (actual : InitializerContinuation selected source) : Prop where
  origins : ActiveBinderCaptureOrigins actual.receipt.ready
    (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
  templates : ∀ older ∈ actual.receipt.ready.localBinders,
    BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older
  transport : ∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
    Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)
  newRows : ∀ requirement ∈ selected.body.body.state.requirements,
    requirement ∉ actual.receipt.ready.requirements →
    ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
      Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)

/-- Both provenance invariants and the suffix privacy proof follow the same
actual source-position traversal. The finalizer checks apply to its exact binder. -/
theorem BodySelection.initializedStatementPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected source, InitializedStatementPrivate actual := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  let roots := selected.body.body.statements.map NodeId.statement
  have initialOrigins : ActiveBinderCaptureOrigins (initial selected.signature selected.body.declaration)
      (selected.body.returned.toTypedSource roots) := by
    apply activeBinderCaptureOrigins_initial_mono
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  have retained : TypingSourceExtends (selected.body.body.state.toTypedSource roots)
      (selected.body.returned.toTypedSource roots) := by
    refine ⟨return_owner selected.body.unified,?_⟩
    change selected.body.body.state.nodes <+: selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact List.prefix_rfl
  obtain ⟨occurrence⟩ := backedStatementPrivacyOccurrence_of_position progress.initialReady
    (State.initial_requirementsWellFormed _ _ _) (State.initial_nodesBelowNextOccurrence _ _ _)
    catalog formation canonical progress.returnBelow (LiveTemplatesBacked.initial _ _ _) initialOrigins retained
    selected.body.inferred position
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ := occurrence.toStatementPrivacyOccurrence.toOccurrence.initialized form formation canonical
  let actual : InitializerContinuation selected source := {
    childFuel := childFuel,entry := occurrence.entry,result := occurrence.result,receipt := receipt,
    retained := occurrence.retained,ready := ready,bodyContinuation := bodyContinuation,
    finalContinuation := bodyContinuation.trans (progress.returnUnification.trans progress.finalization) }
  have readyOrigins : ActiveBinderCaptureOrigins receipt.ready (selected.body.returned.toTypedSource roots) :=
    occurrence.entryOrigins.congr_localBinders receipt.ready_binders
  have readyTemplates : ∀ older ∈ receipt.ready.localBinders,
      BinderTemplatesBefore receipt.ready occurrence.entry.nextRequirement older :=
    ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
      occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have inferred := receipt.initializer_inference occurrence.ready formation canonical
  have live := actual.generalized_live readyOrigins readyTemplates
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have suffix := occurrence.privacy actual.receipt.binding.1.scheme.quantified
    (actual.quantified_below inferred.2.2) live (safe_closed _ _ closed)
  refine ⟨actual,⟨readyOrigins,readyTemplates,?_,?_⟩⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply suffix.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply suffix.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

/-- Public compilation closes initialized-declaration privacy at every chosen
original top-level statement position using actual inference and finalization. -/
theorem compile_initialized_statement_private {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedStatementPrivate actual := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedStatementPrivate (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedStatementPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedStatementPrivate actual :=
  selected.toBodySelection.initializedStatementPrivate checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializedPriorPrivacy
/-! The actual prefix establishes privacy for every prior generalized binder.
Initializer inference therefore excludes their variables from its result, closing
the prior-quantifier blocking premise using the same actual finalizer witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

structure InitializedPriorPrivate
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (actual : InitializerContinuation selected source) : Prop extends InitializedStatementPrivate actual where
  priorAvoided : Avoids (activeSchemeQuantifiers actual.entry) (actual.receipt.ready.resolve actual.receipt.value.type)

theorem InitializedPriorPrivate.prior_blocked
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    {actual : InitializerContinuation selected source} (privateVars : InitializedPriorPrivate actual)
    {target : SourceSemantics.Context} {outer : Substitution}
    (aligned : LocalEnvironmentAligned actual.entry outer target) :
    PriorQuantifiersBlockedAt actual.receipt.ready actual.receipt.locals actual.entry.nextRequirement
      (actual.receipt.ready.resolve actual.receipt.value.type) target :=
  priorQuantifiersBlockedAt_of_activeQuantifiersAvoided aligned privateVars.priorAvoided

/-- Both provenance invariants and the suffix privacy proof follow the same
actual source-position traversal. The finalizer checks apply to its exact binder. -/
theorem BodySelection.initializedPriorPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : BodySelection compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected source, InitializedPriorPrivate actual := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have catalog := SignatureCatalogWellFormed.ofCheckProgram checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  have closed : (Ty.productMany selected.signature.returnTypes).VariablesBelow 0 :=
    selected.returns_closed checked
  have monomorphic : ∀ entry ∈ (selected.signature.parameterNames.zip selected.signature.parameterTypes).map (fun parameter =>
      (parameter.1, Scheme.mono parameter.2)), entry.2.quantified = [] := by
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  let roots := selected.body.body.statements.map NodeId.statement
  have initialOrigins : ActiveBinderCaptureOrigins (initial selected.signature selected.body.declaration)
      (selected.body.returned.toTypedSource roots) := by
    apply activeBinderCaptureOrigins_initial_mono
    intro entry member
    obtain ⟨parameter,_,rfl⟩ := List.mem_map.mp member
    rfl
  have retained : TypingSourceExtends (selected.body.body.state.toTypedSource roots)
      (selected.body.returned.toTypedSource roots) := by
    refine ⟨return_owner selected.body.unified,?_⟩
    change selected.body.body.state.nodes <+: selected.body.returned.nodes
    rw [selected.body.returned_nodes]
    exact List.prefix_rfl
  obtain ⟨occurrence⟩ := activeStatementPrivacyOccurrence_of_position selected.body.resources progress.initialReady
    (State.initial_requirementsWellFormed _ _ _) (State.initial_nodesBelowNextOccurrence _ _ _)
    catalog formation canonical progress.returnBelow closed
    (ActiveQuantifiersPrivate.initial _ _ _ monomorphic)
    (activeQuantifiersBelowNext_initial_mono _ _ _ monomorphic)
    (LiveTemplatesBacked.initial _ _ _) initialOrigins retained
    progress.final_substitution selected.body.inferred position
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ := occurrence.toBackedStatementPrivacyOccurrence.toStatementPrivacyOccurrence.toOccurrence.initialized form formation canonical
  let actual : InitializerContinuation selected source := {
    childFuel := childFuel,entry := occurrence.entry,result := occurrence.result,receipt := receipt,
    retained := occurrence.retained,ready := ready,bodyContinuation := bodyContinuation,
    finalContinuation := bodyContinuation.trans (progress.returnUnification.trans progress.finalization) }
  have readyOrigins : ActiveBinderCaptureOrigins receipt.ready (selected.body.returned.toTypedSource roots) :=
    occurrence.entryOrigins.congr_localBinders receipt.ready_binders
  have readyTemplates : ∀ older ∈ receipt.ready.localBinders,
      BinderTemplatesBefore receipt.ready occurrence.entry.nextRequirement older :=
    ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before receipt
      occurrence.entryTemplates occurrence.ready occurrence.entryWellFormed formation canonical
  have inferred := receipt.initializer_inference occurrence.ready formation canonical
  have live := actual.generalized_live readyOrigins readyTemplates
  have suffix := occurrence.privacy actual.receipt.binding.1.scheme.quantified
    (actual.quantified_below inferred.2.2) live (safe_closed _ _ closed)
  have priorAvoided := ProtectedVariables.LocalLetRequirementTiming.Receipt.value_avoids_active receipt
    occurrence.ready occurrence.entryWellFormed occurrence.entryBound occurrence.entryPrivate catalog formation canonical
  refine ⟨actual,⟨⟨readyOrigins,readyTemplates,?_,?_⟩,priorAvoided⟩⟩
  · intro type safe
    apply selected.finishPrivacy checked _ type
    apply suffix.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply selected.finishPrivacy checked _ type
    apply suffix.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

/-- Public compilation closes initialized-declaration privacy at every chosen
original top-level statement position using actual inference and finalization. -/
theorem compile_initialized_prior_private {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedPriorPrivate actual := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.toBodySelection.initializedPriorPrivate (SourceCoreCompiler.compile_checked_source accepted) position form


theorem Selected.initializedPriorPrivate {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected.toBodySelection source, InitializedPriorPrivate actual :=
  selected.toBodySelection.initializedPriorPrivate checked position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerPredicateFormation
/-! Selected initialized-let receipts and retained worklist bindings consume
whole-body predicate formation at their exact finalized initializer scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness SourceSpecializationWorklist

namespace FinalizedBindingEvent
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {binding : LocalLambdaBinding}

theorem finalPredicates (event : FinalizedBindingEvent selected binding)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true) :
    ∀ requirement ∈ (event.originalBinder.applySubstitution selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (event.originalBinder.applySubstitution selected.body.finalized.substitution)) requirement.predicate :=
  selected.normalizedBindingPredicates checked signatures parameters owner residual event.initializer_retained

end FinalizedBindingEvent

namespace InitializerContinuation
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- This uses the continuation's exact recorded binder and initializer. All
predicate formation is discharged by the selected body traversal and solver. -/
theorem finalPredicates (continuation : InitializerContinuation selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true) :
    ∀ requirement ∈ (continuation.receipt.binding.1.applySubstitution
        selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)) requirement.predicate := by
  apply selected.originalBindingPredicates checked signatures parameters owner residual
    (initializer := .expression continuation.receipt.value.id)
  intro requirement member
  apply List.mem_flatMap.mpr
  refine ⟨({ binder := continuation.receipt.binding.1
             initializer := .expression continuation.receipt.value.id } : InitializedLetBinding),
    ?_, List.mem_map.mpr ⟨requirement, member, rfl⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨.statement { id := continuation.entry.allocateStatementId.1
                       span := source.span
                       type := .unit
                       form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) },
    continuation.original_retained, ?_⟩
  exact List.mem_singleton_self _

end InitializerContinuation
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerCertificate
/-! Assemble the existing generalized-let certificate at the exact selected
initializer boundary. Child expression typing remains the recursive input;
formation of its retained predicates comes from the actual whole-body producer
proof. Barrier and prior-quantifier conditions are kept explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

/-- The exact generalized binder keeps the final type returned by its actual
initializer. The actual finalizer excludes quantifier capture and absorbs the
initializer's inference substitution. -/
theorem finalBody (continuation : InitializerContinuation selected source) :
    (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body =
      selected.body.finalized.substitution.apply continuation.receipt.value.type := by
  have restriction : selected.body.finalized.substitution.without
      continuation.receipt.binding.1.scheme.quantified = selected.body.finalized.substitution :=
    FlexibleSubstitution.Substitution.without_eq_self_of_disjoint_domain _ _
      continuation.no_capture.quantified_fresh
  have body : continuation.receipt.binding.1.scheme.body =
      continuation.receipt.ready.resolve continuation.receipt.value.type := by
    change continuation.receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  rw [FlexibleSubstitution.applyTypedBinder_scheme]
  change (selected.body.finalized.substitution.without
    continuation.receipt.binding.1.scheme.quantified).apply continuation.receipt.binding.1.scheme.body = _
  rw [restriction, body]
  exact continuation.substitution continuation.receipt.value.type

/-- The child typing result supplied by the recursive call is converted to
this allocated binder's scheme body without changing the initializer or context. -/
theorem initializerTyping (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (typed : ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    ExpressionHasType
      ((selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).applySubstitution
        selected.body.finalized.substitution)
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution).scheme.body := by
  rw [← selected.body.resources.source_eq, continuation.finalBody]
  exact typed

/-- The generalized initializer consumer now uses the real selected receipt,
finalizer, and producer formation. There is no monomorphism or whole-body typing
premise. The two generalization conditions are not inferred from checker success. -/
theorem certificate (continuation : InitializerContinuation selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (prior : PriorQuantifiersBlockedAt continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type) target)
    (typed : ExpressionHasType selected.body.finalized.typedSource
      (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
      continuation.receipt.value.id
      (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  have declarationEq := (ProgramEnvironment.declaration?_sound selected.body.declared).2
  have owner : target.currentDeclaration = some selected.signature.id := by
    simpa only [context, ProgramTypeScope.ofDeclaration, declarationEq] using invariant.declarationEq
  have retained : continuation.receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
    exact List.mem_flatMap.mpr ⟨_, continuation.original_retained, List.mem_singleton_self _⟩
  have templates : ∀ requirement ∈ continuation.receipt.binding.1.schemeRequirements,
      ContainsLocalSchemeTemplate
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
        {binder := continuation.receipt.binding.1,
          initializer := .expression continuation.receipt.value.id, requirement} := by
    intro requirement member
    exact containsLocalSchemeTemplate_of_retainedLet
      ⟨continuation.original_retained, rfl⟩ (TypingSourceExtends.refl _) member
  exact unannotatedInitializedLetCertificate_of_finalBarrier_retained selected.body.resources
    (source := selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
    (state := continuation.receipt.ready) (final := continuation.receipt.binding.2)
    (name := continuation.receipt.name) (generalized := continuation.receipt.generalized)
    rfl rfl rfl invariant.signaturesEq invariant.assumptionsMono invariant.solvedRequirementsEq
    retained templates barrier
    (continuation.finalPredicates checked invariant.signatures_eq_whole invariant.typeParametersEq owner invariant.residual)
    prior (continuation.initializerTyping typed)

def initializerBinding (continuation : InitializerContinuation selected source) : InitializedLetBinding :=
  ⟨continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution,
    .expression continuation.receipt.value.id⟩

/-- The same actual let occurrence opens its exact initializer scope at the
state used by the real child call. This step does not assume source monomorphism. -/
theorem enter (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1)) :
    RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry.allocateStatementId.2
      (localSchemeInitializerContext target continuation.initializerBinding.binder) ∧
    ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized (frames ++ [continuation.initializerBinding])
      (localSchemeInitializerContext target continuation.initializerBinding.binder) ∧
    ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
      (.expression continuation.receipt.value.id) := by
  have allocated : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry.allocateStatementId.2 target := {
    invariant with
    active := invariant.active.allocateStatementId rfl
    ready := invariant.ready.allocateStatementId
    bindersBelow := State.allocateStatementId_preserves_localBindersBelowNextLocal _ invariant.bindersBelow
    nodesBelow := State.allocateStatementId_preserves_nodesBelowNextOccurrence _ invariant.nodesBelow
    schemeIsolation := activeSchemeQuantifierIsolation_allocateStatementId invariant.schemeIsolation rfl }
  let statement : StatementNode := {
    id := continuation.entry.allocateStatementId.1
    span := source.span
    type := .unit
    form := .letDecl continuation.receipt.binding.1 (some continuation.receipt.value.id) }
  have recorded : ContainsStatement selected.body.finalized.typedSource statement.id
      (statement.applySubstitution selected.body.finalized.substitution) := by
    rw [selected.body.resources.source_eq]
    exact FlexibleSubstitution.ContainsStatement.applySubstitution _
      ⟨continuation.original_retained, rfl⟩
  have retained : continuation.initializerBinding ∈ initializedLetBindings selected.body.finalized.typedSource := by
    apply List.mem_flatMap.mpr
    refine ⟨.statement (statement.applySubstitution selected.body.finalized.substitution), recorded.1, ?_⟩
    simp [statement, StatementNode.applySubstitution, StatementForm.applySubstitution,
      statementInitializedLetBindings, initializerBinding]
  have edge : DirectChild selected.body.finalized.typedSource
      (.statement continuation.entry.allocateStatementId.1) continuation.initializerBinding.initializer := by
    apply directChild_statement_reference recorded
    simp [statement, StatementNode.applySubstitution, StatementForm.applySubstitution,
      StatementForm.references, initializerBinding]
  exact ⟨allocated.generalizedInitializer continuation.initializerBinding.binder,
    actual.enter covered continuation.initializerBinding retained edge⟩

/-- Apply the concrete child typing step after opening the actual receipt's
scope, then assemble the existing generalized-let certificate. The callback is
restricted to this one child, so it can be the smaller recursive typing case. -/
theorem certificate_of_child (continuation : InitializerContinuation selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (invariant : RecursiveExpressionInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (prior : PriorQuantifiersBlockedAt continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type) target)
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    UnannotatedInitializedLetCertificate
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
      target selected.body.finalized.substitution continuation.receipt.binding.1 continuation.receipt.value.id := by
  have entry := continuation.enter invariant actual covered
  exact continuation.certificate checked invariant barrier prior (child entry.1 entry.2.1 entry.2.2)

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerRequirementFormation
/-! The selected initializer's actual continuation and finalizer discharge the
normalization assumptions of retained requirement formation. Only the genuine
issuance formation remains to be supplied by the recursive source traversal. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.Statement}

theorem retained_formation (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (binders : TypeParameterBindersWellFormed (localSchemeInitializerContext target
      (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.body.declaration.id)
    (residual : target.residualTypeVariables = true)
    (issued : ∀ requirement ∈ continuation.receipt.ready.requirements,
      requirement.id ∈ localSchemeTemplateIds continuation.receipt.binding.1 →
        PredicateAdmissible (localSchemeInitializerContext target
          (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
          requirement.predicate) :
    RetainedRequirementPredicateFormationAt continuation.receipt.ready
      continuation.receipt.binding.1 selected.body.finalized.substitution target := by
  exact SourceInferenceRequirementFormation.retained_formation_of_issuances
    selected.body.resources binders signatures parameters owner residual
    continuation.substitution continuation.no_capture issued

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceCompiledInitializerNormalizedRequirementFormation
/-! Selected actual continuation discharges normalization for prior local reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

/-- The same selected initializer receipt and finalizer provide continuation
and no-capture for normalized issuances from earlier generalized binders. -/
theorem retained_normalized_formation
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel} {source : Syntax.Statement}
    (continuation : InitializerContinuation selected source)
    {target : SourceSemantics.Context}
    (issued : ∀ requirement ∈ continuation.receipt.ready.requirements,
      requirement.id ∈ localSchemeTemplateIds continuation.receipt.binding.1 →
      PredicateAdmissible (localSchemeInitializerContext target
        (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution))
        (TypedTraitResolution.applySubstitution selected.body.finalized.substitution requirement.predicate)) :
    RetainedRequirementPredicateFormationAt continuation.receipt.ready
      continuation.receipt.binding.1 selected.body.finalized.substitution target := by
  exact SourceInferenceRequirementFormation.retained_formation_of_normalized_issuances
    continuation.substitution continuation.no_capture issued

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerContinuation
end
