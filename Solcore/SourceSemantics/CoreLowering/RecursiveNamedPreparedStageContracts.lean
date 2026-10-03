import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection

/-! Actual public compilation retains the codebook used by its cached callable
policy. These receipts connect that factory to the existing independent guard
proofs. They contain no execution law or body induction hypothesis.

The current compatible compiler retains runtime branches and emits callable
guards; it does not call the separate DirectLinking staged evaluator. Original
generic specialization meaning, source callable representation and whole staged
body closure remain separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
open Frontend SourceInference CoreLowering

/-- The exact compatible projection and its original error mapping. -/
def projectType (checked : SourceCoreCompatibleCatalog.Checked) (type : TypeSystem.Ty) :
    Except SourceCoreLocalPolymorphism.Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError fun
    | .catalog error => .projection error
    | .metadata _ => .projection (.unsupportedType type)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ}
    {output : α} (accepted : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

/-- A present callable context comes from the actual codebook branch. Empty
roots and disabled callable contracts cannot supply such a context. -/
theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (present : base.callableContext = some native) :
    SourceCoreStageCodebook.prepareWithProjection base.sourceProgram base.plan (projectType checked) = .ok native.table := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted; cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, tableAccepted, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases Option.some.inj present
      exact mapError_ok tableAccepted
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted; cases present

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.callableContext = some native) :
    SourceCoreStageCodebook.prepareWithProjection automatic.prepared.sourceProgram automatic.prepared.plan
      (projectType automatic.checked) = .ok native.table := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared present

/-- Every field identifies the actual cached artifact and its original pass. -/
structure Prepared (compiled : SourceCoreUnifiedCompilation.Compiled)
    (native : SourceCoreGeneralFunctions.CallableContext) : Prop where
  present : compiled.indexed.base.callableContext = some native
  accepted : SourceCoreStageCodebook.prepareWithProjection compiled.sourceProgram compiled.indexed.base.plan
    (projectType compiled.compatible.checked) = .ok native.table

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (present : compiled.indexed.base.callableContext = some native) : Prepared compiled native := by
  have base := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  have own : compiled.compatible.prepared.callableContext = some native := by rwa [base] at present
  have accepted := of_automatic compiled.compatiblePrepared own
  have source := (SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1
  refine ⟨present, ?_⟩
  rw [base] at source ⊢
  rwa [source] at accepted

/-- A proposition about the facade's retained recipe, without a runtime getter. -/
def PublicRecipe (compiled : SourceCompiler.Compiled) (recipe : SourceCoreIndexedSession.Recipe) : Prop :=
  SourceCoreExecution.Compiled.casesOn (motive := fun _ => Prop) compiled
    (fun _ actual _ => actual = some recipe)

theorem public_preparation {source : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    {compiled : SourceCompiler.Compiled}
    (selected : source.artifact? = some cached)
    (issued : SourceCoreIndexedSession.Recipe.prepare cached = .ok recipe)
    (accepted : SourceCoreExecution.prepare source = .ok compiled) : PublicRecipe compiled recipe := by
  unfold SourceCoreExecution.prepare at accepted
  split at accepted
  · rename_i absent
    rw [selected] at absent
    cases absent
  · rename_i actual present
    cases Option.some.inj (present.symm.trans selected)
    split at accepted
    · rename_i error failed
      rw [issued] at failed
      cases failed
    · rename_i actualRecipe actualIssued
      have same := Except.ok.inj (actualIssued.symm.trans issued)
      cases accepted
      cases same
      rfl

/-- The public success equation recovers both real factories and their same
cached artifact. The facade preparation is pure; opening its IO artifact is
not used as a proof of preparation. -/
theorem public_compilation {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (selected : PublicRecipe compiled recipe) :
    ∃ source : SourceCoreCompiler.Compiled,
      SourceCoreCompiler.compileChecked program seeds options = .ok source ∧
      source.artifact? = some recipe.compiled ∧
      SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe := by
  unfold SourceCoreExecution.compileChecked at accepted
  obtain ⟨source, sourceAccepted, accepted⟩ := bind_ok accepted
  have sourceAccepted := mapError_ok sourceAccepted
  unfold SourceCoreExecution.prepare at accepted
  split at accepted
  · cases accepted; cases selected
  · rename_i cached cachedSelected
    split at accepted
    · cases accepted
    · rename_i actualRecipe recipeAccepted
      cases accepted
      have same : actualRecipe = recipe := Option.some.inj selected
      subst recipe
      have cachedEq := SourceCoreIndexedSession.Recipe.prepare_compiled recipeAccepted
      exact ⟨source, sourceAccepted, by rwa [← cachedEq] at cachedSelected,
        by rwa [cachedEq]⟩

theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {native : SourceCoreGeneralFunctions.CallableContext}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (selected : PublicRecipe compiled recipe)
    (present : recipe.compiled.indexed.base.callableContext = some native) :
    Prepared recipe.compiled native ∧ recipe.compiled.sourceProgram = program := by
  obtain ⟨source, sourceAccepted, cachedSelected, _⟩ := public_compilation accepted selected
  exact ⟨of_compiled recipe.compiled present,
    (SourceCoreCompiler.Compiled.artifact_fields source cachedSelected).1.trans
      (SourceCoreCompiler.compileChecked_program sourceAccepted)⟩

/-- Every entry keeps its full original source contract and descriptor ID. -/
theorem Prepared.entries_authenticated {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native) :
    CallEntryCertificates.AllAuthenticated compiled.indexed.base.plan native.table.entries :=
  CallEntryCertificates.prepareWithProjection_authenticates prepared.accepted

/-- The original callable policy emits the same retained callsite. -/
theorem indirect_call_eq {native : SourceCoreGeneralFunctions.CallableContext}
    {active : TypeSystem.Substitution} {context : SourceCoreFunctions.Context} {source : TypedSource}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution} {site : SourceCoreCallableContracts.Callsite}
    (form : node.form = .call callee arguments (.indirect metadata))
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (result : Core.Ty) (calleeCode argumentsCode : Core.Expr) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      context source node result calleeCode argumentsCode =
        .ok (site.lower native.diagnostics.unknown result calleeCode argumentsCode) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form, issued, Except.mapError,
    pure, Except.pure, bind, Except.bind]

private theorem callsite_fields {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call reasonAt = .ok site) :
    site.table = table ∧ site.caller = caller ∧ site.call = call := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; exact ⟨rfl, rfl, rfl⟩
  · cases issued

/-- Ordered source rows are derived from the actual table and callsite factory;
no arbitrary selected guard or verdict is supplied. -/
theorem Prepared.rows {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {context : SourceCoreFunctions.Context} {site : SourceCoreCallableContracts.Callsite}
    {sidecar : SourceCoreStageContracts.Sidecar} {node : ExpressionNode}
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (issued : SourceCoreCallableContracts.prepareCallsite native.table context.owner node.id
      native.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata)) :
    CallableLedger.Rows sidecar site node.id arguments := by
  obtain ⟨table, owner, call⟩ := callsite_fields issued
  have accepted := prepared.accepted
  rw [← table] at accepted
  have caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar := by
    rwa [owner]
  have contains : ContainsExpression sidecar.source site.call node := by rwa [call]
  simpa only [call] using CallCodebookCertificates.rows_of_prepareWithProjection accepted caller contains form

/-- Existing source-value representation and the real sidecar identify the
dispatch. Native callable typing alone supplies neither of these facts. -/
theorem Prepared.covers {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiled native)
    {catalog : SourceCoreDataCatalog.Catalog} (underlying : GenericHeap.PayloadModel catalog)
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId}
    {metadata : IndirectCallResolution}
    (sameTable : site.table = native.table)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source site.call node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Core.Ty) :
    CallStageBoundary.Covers (CallableLedger.model underlying compiled.indexed.base.plan site.table)
      (CallableLedger.frame sidecar) site site.call arguments sourceType type := by
  have accepted := prepared.accepted
  rw [← sameTable] at accepted
  intro mapping world source carrier contract represented bound
  exact RecursiveStageProjection.covers_of_prepare underlying accepted caller contains form sourceType type represented bound

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
