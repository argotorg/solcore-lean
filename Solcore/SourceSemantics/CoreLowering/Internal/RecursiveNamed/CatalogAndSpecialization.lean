import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.Frontend.SourceCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.SourceStageAnalysisSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins

/-!
# Recursive named rows: the catalog and specialization

The finite named-call inventory `RecursiveNamedCatalog.Header`, prepared named rows `RecursiveNamedPublicSpecializationMeaning.Prepared`, stage contracts and Source frames, and the validity of specialization.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
/-! Pointwise finite-trace contracts. Source preservation uses an independent
source size; reflection consumes the original Core size and constructs a source
trace with its own size. Below only restricts an existing pointwise family.
Administrative authority and runtime environment typing stay separate inputs.
These contracts do not add meaning fields to a static catalog or profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep ResultRepresents)
open ProtectedExpressionMeaning (Entry)

/-- A strict outer bound selects only the smaller pointwise obligations. -/
def Below (budget : Nat) (contract : Nat → Prop) : Prop :=
  ∀ size, size < budget → contract size

theorem Below.restrict {contract : Nat → Prop} {small large : Nat}
    (meaning : Below large contract) (bounded : small ≤ large) : Below small contract := by
  intro size smaller
  exact meaning size (Nat.lt_of_lt_of_le smaller bounded)

theorem Below.child {contract : Nat → Prop} {budget child : Nat}
    (meaning : Below budget contract) (smaller : child < budget) : contract child :=
  meaning child smaller

def PreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
def ReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

/-! Body contracts have the same independent source statement typing boundary
as the existing body interface, with an additional actual typed environment and
protected entry. A source body trace is never an input to reflection. -/
def BodyPreservesAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (body.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after
def BodyReflectsAt (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (function : Dynamic.Closure) (certificate : FunctionCode.BodyCertificate)
    (faults : FaultRep) (entry : Entry) : Prop :=
  ∀ {scope type body}, certificate function.source scope function.body type body →
  ∀ {context staticFinal facts}, StatementsHaveType function.source
    {returnType := function.resultType, loopDepth := 0} context function.body staticFinal facts →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    entry scope mapping world before store canonical →
    EvaluationSize size actual store (body.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld function.resultType type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep} {entry : Entry}
  {function : Dynamic.Closure} {bodyCertificate : FunctionCode.BodyCertificate}

/-- Restriction of a proved unrestricted expression theorem. -/
theorem preserves_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (size : Nat) : PreservesAt size model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed installed trace
  exact meaning certified found environments heaps locals agrees typed installed trace.sound

theorem reflects_at_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (size : Nat) : ReflectsAt size model program context evidence source certificate faults entry := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed installed evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed installed evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_below_of_unbounded
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    (budget : Nat) : Below budget (fun size => PreservesAt size model program context evidence source certificate faults entry) := by
  intro size _
  exact preserves_at_of_unbounded meaning size

theorem reflects_below_of_unbounded
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    (budget : Nat) : Below budget (fun size => ReflectsAt size model program context evidence source certificate faults entry) := by
  intro size _
  exact reflects_at_of_unbounded meaning size

/-- Existing unrestricted body meaning can be restricted without changing the
source/static code or any canonical/actual environment relationship. -/
theorem body_preserves_at_of_unbounded
    (meaning : FunctionCalls.BodyPreserves model program function bodyCertificate faults)
    (entry : Entry) (size : Nat) : BodyPreservesAt size model program function bodyCertificate faults entry := by
  intro scope type body certified context staticFinal facts typed mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees _ _ trace
  exact meaning certified typed environments heaps locals agrees trace.sound

theorem body_reflects_at_of_unbounded
    (meaning : FunctionCalls.BodyReflects model program function bodyCertificate faults)
    (entry : Entry) (size : Nat) : BodyReflectsAt size model program function bodyCertificate faults entry := by
  intro scope type body certified context staticFinal facts typed mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees _ _ evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified typed environments heaps locals agrees evaluated.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem body_preserves_below_of_unbounded
    (meaning : FunctionCalls.BodyPreserves model program function bodyCertificate faults)
    (entry : Entry) (budget : Nat) :
    Below budget (fun size => BodyPreservesAt size model program function bodyCertificate faults entry) := by
  intro size _
  exact body_preserves_at_of_unbounded meaning entry size

theorem body_reflects_below_of_unbounded
    (meaning : FunctionCalls.BodyReflects model program function bodyCertificate faults)
    (entry : Entry) (budget : Nat) :
    Below budget (fun size => BodyReflectsAt size model program function bodyCertificate faults entry) := by
  intro size _
  exact body_reflects_at_of_unbounded meaning entry size

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
/-! The actual accepted specialization constructs the independent canonical
body instantiation. Static validity, invocation evidence, statement roots and
captured environment remain separate conditions. Reversed occurrence metadata
requires its own substitution correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
open Frontend SourceInference TypeSystem

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}

/-- The accepted guards identify the original cataloged declaration, its raw
body owner, and the complete specialized declaration record. -/
theorem identities
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    signature.id = generic.declaration ∧ generic.typedBody.owner = generic.declaration ∧
      specialized.declaration = generic.declaration := by
  unfold SourceSpecialization.specializeFunction at accepted
  by_cases declaration : signature.id = generic.declaration
  · simp only [declaration, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
    by_cases owner : generic.typedBody.owner = generic.declaration
    · simp only [owner, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
      have accepted := reject_ok accepted
      have accepted := reject_ok accepted
      have accepted := reject_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases analysis : SourceStageAnalysis.analyzeFunction
          (SourceSpecialization.applyCheckedFunction canonical generic) with
      | error error => simp only [analysis] at accepted; cases accepted
      | ok stages =>
        simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
        subst specialized
        exact ⟨declaration, owner, rfl⟩
    · simp [owner, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [declaration, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

theorem body
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.typedBody = StructuralSubstitution.applyTypedSource
      specialized.parameterSubstitution generic.typedBody := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1,
    StructuralSubstitution.applyTypedSource_frontend_eq]
  rfl

/-- Every solved row, its identity and full recursive evidence are retained in
the original order by the independent structural substitution. -/
theorem ledger
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.solvedRequirements = generic.solvedRequirements.map
      (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution) := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
  simp only [SourceSpecialization.applyCheckedFunction]
  congr 1
  funext requirement
  exact (StructuralSubstitution.applySolvedRequirement_frontend_eq _ _).symm

theorem result
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    specialized.function.inferredBodyType =
      specialized.parameterSubstitution.apply generic.inferredBodyType := by
  rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
  rfl

/-- The body view uses canonical metadata and the real full solved ledger.
The declaration context keeps residual type variables enabled. -/
def bodyInstance (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) :
    Dynamic.BodyInstance where
  context := declarationContext program.signatures specialized.declaration []
    specialized.assumptions specialized.function.solvedRequirements
  source := specialized.function.typedBody
  resultType := specialized.function.inferredBodyType

theorem context {program : CheckedProgram}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    (bodyInstance program specialized).context =
      declarationContext program.signatures generic.declaration []
        (signature.scheme.predicates.map
          (ProgramPredicate.applyParameters specialized.parameterSubstitution))
        (generic.solvedRequirements.map
          (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution)) := by
  simp only [bodyInstance, (identities accepted).2.2,
    (CallableCoercionBodyProvenance.specialization_fields accepted).2, ledger accepted]

/-- This derives the dynamic instantiation judgment from the actual compiler
pass and catalog membership. It requires independent validity of the complete
canonical metadata, including unused substitution ranges. -/
theorem instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized)) :
    Dynamic.FunctionInstantiates (Program.ofChecked program)
      (CallableNamedMetadata.instantiation specialized) (bodyInstance program specialized) := by
  obtain ⟨declaration, _, specializedDeclaration⟩ := identities accepted
  apply Dynamic.FunctionInstantiates.intro
    (signature := signature) (definition := FunctionDefinition.ofChecked generic)
  · exact signatureMember
  · exact List.mem_map.mpr ⟨generic, genericMember, rfl⟩
  · exact specializedDeclaration.trans declaration.symm
  · exact declaration.symm
  · exact valid
  · exact body accepted
  · exact result accepted
  · simpa only [Program.ofChecked, FunctionDefinition.ofChecked, BodyDefinition.ofChecked,
      CallableNamedMetadata.instantiation,
      (CallableCoercionBodyProvenance.specialization_fields accepted).2] using
      context (program := program) accepted

/-- The remaining closure facts come from the actual source invocation view;
they are never inferred from Core types, decoding, or successful execution. -/
theorem source_frame {program : CheckedProgram} {function : Dynamic.Closure}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized))
    (source : function.source = specialized.function.typedBody)
    (context : function.context = (bodyInstance program specialized).context)
    (parameters : function.parameters = specialized.function.typedBody.inputs)
    (result : function.resultType = specialized.function.inferredBodyType)
    (captured : function.captured = [])
    (roots : Dynamic.StatementRoots specialized.function.typedBody.roots function.body)
    (covers : function.evidence.Covers (bodyInstance program specialized).context) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (bodyInstance program specialized) function :=
  ⟨instantiated signatureMember genericMember accepted valid,
    source, context, parameters, result, captured, roots, covers⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
/-! Retained declaration substitutions use the reverse of canonical order.
Their records stay distinct; unique keys make their structural actions agree.
Every raw field and recursive evidence row is retained. These are syntax and
instantiation facts, with no execution or authority premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
open Frontend SourceInference TypeSystem StructuralSubstitution

/-- First-match lookup is invariant under reversal when every key is unique.
No condition on replacement types or their use is required. -/
theorem lookup_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup)
    (parameter : TypeParameterId) :
    TypeSystem.ParameterSubstitution.lookup? substitution.reverse parameter = substitution.lookup? parameter := by
  have reversedUnique : (SourceSemantics.ParameterSubstitution.domain substitution.reverse).Nodup := by
    simpa [SourceSemantics.ParameterSubstitution.domain, List.map_reverse] using
      (List.reverse_perm _).nodup_iff.mpr unique
  cases found : substitution.lookup? parameter with
  | none =>
    cases reversed : TypeSystem.ParameterSubstitution.lookup? substitution.reverse parameter with
    | none => rfl
    | some replacement =>
      have member := List.mem_reverse.mp (StructuralSubstitution.ParameterSubstitution.mem_of_lookup?_eq_some reversed)
      have actual := StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup unique member
      rw [found] at actual
      cases actual
  | some replacement =>
    exact StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup reversedUnique
      (List.mem_reverse.mpr (StructuralSubstitution.ParameterSubstitution.mem_of_lookup?_eq_some found))

/-- Raw equality uses full lookup values, before any runtime type erasure. -/
theorem apply_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (type : TypeSystem.Ty) :
    left.apply type = right.apply type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply]

private theorem apply_function {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : left.apply = right.apply :=
  funext (apply_congr same)

private theorem predicate_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    ProgramPredicate.applyParameters left = ProgramPredicate.applyParameters right := by
  funext predicate
  simp only [ProgramPredicate.applyParameters, apply_function same]

private theorem binder_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : applyBinder left = applyBinder right := by
  have requirements : LocalSchemeRequirement.applyParameters left = LocalSchemeRequirement.applyParameters right := by
    funext requirement
    simp only [LocalSchemeRequirement.applyParameters, predicate_congr same]
  funext binder
  simp only [applyBinder, applyScheme, apply_function same, requirements]

private theorem declaration_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyDeclarationInstantiation left = applyDeclarationInstantiation right := by
  funext instantiation
  simp only [applyDeclarationInstantiation, apply_function same, predicate_congr same]

private theorem constructor_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyDataConstructorInstantiation left = applyDataConstructorInstantiation right := by
  funext instantiation
  simp only [applyDataConstructorInstantiation, apply_function same]

private theorem integer_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyIntegerLiteralResolution left = applyIntegerLiteralResolution right := by
  funext resolution
  simp only [applyIntegerLiteralResolution, apply_function same]

private theorem instruction_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchPatternInstruction left = applyMatchPatternInstruction right := by
  funext instruction
  cases instruction <;> simp only [applyMatchPatternInstruction, integer_congr same, binder_congr same, constructor_congr same]

private theorem pattern_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchPatternResolution left = applyMatchPatternResolution right := by
  funext pattern
  cases pattern <;> simp only [applyMatchPatternResolution, integer_congr same, binder_congr same,
    constructor_congr same, instruction_congr same]

private theorem match_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyMatchResolution left = applyMatchResolution right := by
  have casesEq : applyTypedMatchCase left = applyTypedMatchCase right := by
    funext arm
    simp only [applyTypedMatchCase, applyTypedMatchPattern, pattern_congr same, apply_function same]
  funext resolution
  simp only [applyMatchResolution, casesEq]

private theorem reference_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyReferenceResolution left = applyReferenceResolution right := by
  funext resolution
  cases resolution <;> simp only [applyReferenceResolution, declaration_congr same]

private theorem call_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyCallResolution left = applyCallResolution right := by
  funext resolution
  cases resolution <;> simp only [applyCallResolution, applyIndirectCallResolution, declaration_congr same, apply_function same]

private theorem expression_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyExpressionForm left = applyExpressionForm right := by
  funext form
  cases form <;> simp only [applyExpressionForm, integer_congr same, reference_congr same,
    call_congr same, constructor_congr same, binder_congr same, apply_function same]

private theorem assignment_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyAssignmentResolution left = applyAssignmentResolution right := by
  funext assignment
  simp only [applyAssignmentResolution, applyPlaceResolution, apply_function same]

private theorem forItem_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyForItemForm left = applyForItemForm right := by
  funext item
  cases item <;> simp only [applyForItemForm, binder_congr same, assignment_congr same]

private theorem statement_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) :
    applyStatementForm left = applyStatementForm right := by
  funext form
  cases form <;> simp only [applyStatementForm, binder_congr same, assignment_congr same,
    match_congr same, forItem_congr same]

private theorem node_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) : applyNode left = applyNode right := by
  have coercions : applyCoercionStep left = applyCoercionStep right := by
    funext step
    simp only [applyCoercionStep, apply_function same]
  funext node
  cases node <;> simp only [applyNode, applyExpressionNode, applyStatementNode, coercions,
    expression_congr same, statement_congr same, apply_function same]

/-- All retained source fields, including nested raw substitution rows, are
mapped in their original order under extensionally equal substitutions. -/
theorem typedSource_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (source : TypedSource) :
    applyTypedSource left source = applyTypedSource right source := by
  simp only [applyTypedSource, binder_congr same, node_congr same]

mutual
  private theorem evidence_congr {left right : TypeSystem.ParameterSubstitution}
      (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter)
      (evidence : TypedTraitResolution.Evidence) : applyEvidence left evidence = applyEvidence right evidence := by
    cases evidence with
    | byImpl goal implementation premises =>
      simp only [applyEvidence, predicate_congr same, evidences_congr same premises]

  private theorem evidences_congr {left right : TypeSystem.ParameterSubstitution}
      (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter)
      (evidences : List TypedTraitResolution.Evidence) : applyEvidences left evidences = applyEvidences right evidences := by
    cases evidences with
    | nil => rfl
    | cons head tail => simp only [applyEvidences, evidence_congr same head, evidences_congr same tail]
end

/-- Complete recursive evidence is transported; requirement IDs and order
remain exactly those of the original ledger. -/
theorem solvedRequirement_congr {left right : TypeSystem.ParameterSubstitution}
    (same : ∀ parameter, left.lookup? parameter = right.lookup? parameter) (row : SolvedRequirement) :
    applySolvedRequirement left row = applySolvedRequirement right row := by
  have evidenceEq : applyPredicateEvidence left row.evidence = applyPredicateEvidence right row.evidence := by
    cases row.evidence <;> simp only [applyPredicateEvidence, predicate_congr same, evidence_congr same]
  simp only [applySolvedRequirement, predicate_congr same, evidenceEq]

theorem typedSource_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup) (source : TypedSource) :
    applyTypedSource substitution.reverse source = applyTypedSource substitution source :=
  typedSource_congr (lookup_reverse unique) source

theorem ledger_reverse {substitution : TypeSystem.ParameterSubstitution}
    (unique : (SourceSemantics.ParameterSubstitution.domain substitution).Nodup) (rows : List SolvedRequirement) :
    rows.map (applySolvedRequirement substitution.reverse) = rows.map (applySolvedRequirement substitution) := by
  exact List.map_congr_left (fun row _ => solvedRequirement_congr (lookup_reverse unique) row)

/-- Exactness is permutation invariant and keeps every original range row. -/
theorem exact_reverse {substitution : TypeSystem.ParameterSubstitution} {parameters : List TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters) :
    SourceSemantics.ParameterSubstitution.Exact substitution.reverse parameters := by
  refine ⟨exact.parameters_nodup, ?_⟩
  simpa only [SourceSemantics.ParameterSubstitution.domain, List.map_reverse] using
    (List.reverse_perm _).trans exact.domain_permutation

/-- Reversal preserves full declaration validity, including unused ranges.
The source record's substitution order is retained as the reversed list. -/
theorem valid_reverse {context : Context} {instantiation : DeclarationInstantiation}
    (valid : SourceSemantics.DeclarationInstantiation.Valid context instantiation) :
    SourceSemantics.DeclarationInstantiation.Valid context (CallableNamedReversal.instantiation instantiation) := by
  cases valid with
  | intro signature member declaration exact range typeEq predicates parameters result =>
    refine .intro signature member declaration (exact_reverse exact) ?_ ?_ ?_ parameters result
    · intro parameter replacement member
      exact range parameter replacement (List.mem_reverse.mp member)
    · exact typeEq.trans (apply_congr (lookup_reverse exact.domain_nodup) signature.scheme.body).symm
    · simpa only [CallableNamedReversal.instantiation, predicate_congr (lookup_reverse exact.domain_nodup)] using predicates

/-- A valid function instantiation supplies its own domain uniqueness. The
same body instance is retained without constructing an execution trace. -/
theorem instantiates_reverse {program : Program} {instantiation : DeclarationInstantiation} {body : Dynamic.BodyInstance}
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    Dynamic.FunctionInstantiates program (CallableNamedReversal.instantiation instantiation) body := by
  cases instantiated with
  | intro signature definition declaration owner valid source result context =>
    have unique : (SourceSemantics.ParameterSubstitution.domain instantiation.parameterSubstitution).Nodup := by
      cases valid with | intro _ _ _ exact _ _ _ _ _ => exact exact.domain_nodup
    refine .intro signature definition declaration owner (valid_reverse valid) ?_ ?_ ?_
    · exact source.trans (typedSource_reverse unique _).symm
    · exact result.trans (apply_congr (lookup_reverse unique) _).symm
    · simpa only [CallableNamedReversal.instantiation, ledger_reverse unique] using context

/-- The compiler's canonical and source-retained records use the same body,
while their complete parameter lists keep their respective order. -/
theorem retained_instantiates {program : Program} {specialized : SourceSpecialization.SpecializedFunction}
    {body : Dynamic.BodyInstance}
    (instantiated : Dynamic.FunctionInstantiates program (CallableNamedMetadata.instantiation specialized) body) :
    Dynamic.FunctionInstantiates program (CallableNamedCanonicalOrder.retainedInstantiation specialized) body :=
  instantiates_reverse instantiated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
/-! Ordinary named invocation views come from actual compiled roots and input
preparation. Their empty lexical capture and dictionary are defined at source
entry; source instantiation still requires independent full metadata validity.
No native execution or runtime authority is used to construct the view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
open Frontend SourceInference TypeSystem
open RecursiveNamedSpecializationBodyFacts

private theorem roots_of_map {source : TypedSource} {statements : List StatementId}
    (accepted : source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) = .ok statements) :
    Dynamic.StatementRoots source.roots statements := by
  generalize source.roots = roots at accepted ⊢
  induction roots generalizing statements with
  | nil => cases accepted; exact .nil
  | cons head rest ih =>
    cases head with
    | expression id => cases accepted
    | statement id =>
      simp only [List.mapM_cons, pure, Except.pure, bind, Except.bind] at accepted
      cases lowered : List.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun x => match x with
        | .statement id => Except.ok id
        | .expression id => throw (SourceCoreGeneralFunctions.Error.expectedStatementRoot id)) rest with
      | error error => simp only [lowered] at accepted; cases accepted
      | ok tail =>
        simp only [lowered] at accepted
        cases accepted
        exact .cons (ih lowered)

/-- The proof view starts a global body from its actual source declaration,
full solved ledger, empty lexical capture and empty ordinary dictionary. -/
def view (program : CheckedProgram) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) : Dynamic.Closure where
  parameters := named.specialized.function.typedBody.inputs
  resultType := named.specialized.function.inferredBodyType
  body := statements
  source := named.specialized.function.typedBody
  captured := []
  context := (bodyInstance program named.specialized).context
  evidence := []

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}

theorem compiled_roots
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    Dynamic.StatementRoots named.specialized.function.typedBody.roots compiled.statements :=
  roots_of_map compiled.roots

private theorem roots_eq {roots : List NodeId} {statements : List StatementId}
    (extracted : Dynamic.StatementRoots roots statements) : roots = statements.map NodeId.statement := by
  induction extracted with
  | nil => rfl
  | cons _ ih => exact congrArg (List.cons _) ih

theorem compiled_roots_eq
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    named.specialized.function.typedBody.roots = compiled.statements.map NodeId.statement := by
  exact roots_eq (compiled_roots compiled)

theorem empty_covers {program : CheckedProgram}
    (closed : named.specialized.assumptions = []) :
    Dynamic.EvidenceEnvironment.Covers (bodyInstance program named.specialized).context [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    change predicate ∈ named.specialized.assumptions at member
    rw [closed] at member
    cases member

/-- Preparation supplies the complete ordered input binders, while the real
second compiler pass supplies the exact source statement roots. -/
theorem agreement {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction}
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) := by
  obtain ⟨same, binders, _⟩ := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs inputs
  refine ⟨rfl, compiled_roots_eq compiled, ?_, rfl⟩
  change named.specialized.function.typedBody.inputs = named.inputs.map Prod.fst
  rw [same]
  exact binders.symm

/-- Accepted specialization, independent canonical validity and real compiled
roots construct the source frame. There is no source body trace premise. -/
theorem canonical_frame {program : CheckedProgram} {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨instantiated signatureMember genericMember accepted valid,
    rfl, rfl, rfl, rfl, rfl, compiled_roots compiled, empty_covers closed⟩

/-- The actual first and second compiler passes supply both source agreement
and the independent ordinary invocation frame. -/
theorem of_compilation {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨agreement inputs compiled, canonical_frame signatureMember genericMember accepted valid closed compiled⟩

/-- Source inference's full reversed metadata invokes the same independently
instantiated body and ordinary source view. Domain uniqueness comes from Valid. -/
theorem retained_frame {program : CheckedProgram} {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) := by
  have canonical := canonical_frame signatureMember genericMember accepted valid closed compiled
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates canonical.instantiated,
    canonical.source, canonical.context, canonical.parameters, canonical.result,
    canonical.captured, canonical.roots, canonical.covers⟩

theorem retained_of_compilation {program : CheckedProgram}
    {representation : SourceCoreGeneralFunctions.Representation}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨agreement inputs compiled, retained_frame signatureMember genericMember accepted valid closed compiled⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
/-! Canonical declaration validity from actual specialization. The real guards
and ordered canonical domain provide the redundant metadata fields. Every raw
replacement, including unused nominal rows, still needs independent formation
in the source context. No body execution or native authority is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
open Frontend SourceInference TypeSystem

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}

/-- These three equalities come from the actual leading guards, before any
specialized body is produced. The flags are not recovered from erased types. -/
theorem guards
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    signature.scheme.body = generic.type ∧
      signature.parameterComptime = generic.typedBody.inputs.map (·.comptime) ∧
      signature.returnComptime = generic.returnComptime := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  by_cases typeSame : signature.scheme.body = generic.type
  · simp only [typeSame, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
    by_cases parametersSame : signature.parameterComptime = generic.typedBody.inputs.map (·.comptime)
    · simp only [parametersSame, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at accepted
      by_cases returnSame : signature.returnComptime = generic.returnComptime
      · exact ⟨typeSame, parametersSame, returnSame⟩
      · simp [returnSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    · simp [parametersSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · simp [typeSame, bne_iff_ne, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

/-- The complete domain is the original declaration order, including unused
parameters. No used-type filtering is performed. -/
theorem exact
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) :
    SourceSemantics.ParameterSubstitution.Exact specialized.parameterSubstitution signature.scheme.parameters := by
  refine ⟨unique, ?_⟩
  change (specialized.parameterSubstitution.map Prod.fst).Perm signature.scheme.parameters
  rw [SourceSpecialization.specializeFunction_parameterDomain accepted]

/-- Full raw range formation is the only context-dependent input beyond the
original signature's membership. The context's residual flag is unchanged. -/
theorem canonical_valid {context : Context}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (member : signature ∈ context.signatures.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid context (CallableNamedMetadata.instantiation specialized) := by
  obtain ⟨typeSame, parametersSame, returnSame⟩ := guards accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  refine .intro signature member (identities.2.2.trans identities.1.symm)
    (exact accepted unique) range ?_ fields.2 ?_ ?_
  · change specialized.function.type = specialized.parameterSubstitution.apply signature.scheme.body
    rw [fields.1]
    change specialized.parameterSubstitution.apply generic.type = _
    rw [typeSame]
  · change specialized.function.typedBody.inputs.map (·.comptime) = signature.parameterComptime
    rw [fields.1]
    simpa only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
      List.map_map, SourceSpecialization.applyBinder, Function.comp_def] using parametersSame.symm
  · change specialized.function.returnComptime = signature.returnComptime
    rw [fields.1]
    exact returnSame.symm

/-- Program validity supplies parameter uniqueness at the same cataloged
signature; it does not replace the full replacement-range obligation. -/
theorem valid_of_program {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (member : signature ∈ program.signatures.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized) :=
  canonical_valid accepted member (wellFormed.signatures.function_parameters signature member).1 range

theorem instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  RecursiveNamedSpecializationBodyFacts.instantiated signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range)

theorem retained_instantiated {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  RecursiveNamedRetainedSubstitutionFacts.retained_instantiates
    (instantiated signatureMember genericMember accepted unique range)

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}

/-- The computed validity discharges the full canonical-validity input to the
actual two-pass source-frame factory. Ordinary evidence and every raw range
row remain explicit static conditions. -/
theorem of_compilation
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  RecursiveNamedPreparedSourceFrames.of_compilation signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range) closed inputs compiled

/-- Reversed occurrence metadata retains exactly the same independent body
and prepared source view; substitution records themselves keep their order. -/
theorem retained_of_compilation
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  RecursiveNamedPreparedSourceFrames.retained_of_compilation signatureMember genericMember accepted
    (canonical_valid accepted signatureMember unique range) closed inputs compiled
end Prepared

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
/-! The stored specialization analysis is the actual successful stage pass.
Independent graph and local identity properties move from the original body
through structural substitution, so the real specialized body has a source
stage derivation. This is classification, not comptime evaluation correctness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
open Frontend SourceInference TypeSystem

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}

/-- Every field of the actual stage pass result is kept by specialization. -/
theorem analyzed
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    SourceStageAnalysis.analyzeFunction specialized.function = .ok specialized.stageAnalysis := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact analysis

theorem graph_closed
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed generic.typedBody) :
    OccurrenceGraphClosed specialized.function.typedBody := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact StructuralSubstitution.OccurrenceGraphClosed.applyParameters specialized.parameterSubstitution closed

theorem local_identities
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (owned : LocalIdentityOwnership generic.typedBody) :
    LocalIdentityOwnership specialized.function.typedBody := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact StructuralSubstitution.LocalIdentityOwnership.applyParameters specialized.parameterSubstitution owned

/-- The original independent structural properties and actual stage pass
supply the normative whole-function stage classification. -/
theorem has_stages
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    (closed : OccurrenceGraphClosed generic.typedBody)
    (owned : LocalIdentityOwnership generic.typedBody) :
    Staging.FunctionHasStages specialized.function :=
  SourceStageAnalysisSoundness.analyzeFunction_success_hasStages_of_wellFormed
    specialized.function specialized.stageAnalysis (graph_closed accepted closed)
    (local_identities accepted owned) (analyzed accepted)

/-- Independent program body typing supplies the original graph and local
identity properties. The forgeable checked carrier alone does not do so. -/
theorem has_stages_of_program {program : CheckedProgram}
    (programTyped : ProgramWellFormed (Program.ofChecked program))
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    Staging.FunctionHasStages specialized.function := by
  have definition := programTyped.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases definition with
  | intro _ _ typed =>
    exact has_stages accepted (StructuralSubstitution.BodyDefinitionHasType.graphClosed typed)
      (StructuralSubstitution.BodyDefinitionHasType.localIdentityOwnership typed)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationStageFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
/-! The real public worklist supplies complete specialization carriers and their
original generic definitions. Executable-plan growth and the actual preparation
pass supply ordered inputs, statement roots and the full resolved dictionary.
Independent program typing, every raw substitution range and invocation arity
remain explicit. The source call correspondence does not construct runtime
Entry/Authority/profiles, extend the ordinary closed Header, or prove recursive
staging and contextual local-evidence transformation semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α}
    {map : ε → δ} {value : α} (accepted : action.mapError map = .ok value) :
    action = .ok value := by
  cases action <;> cases accepted
  rfl

/-- Static provenance contains the actual request, complete source definition
and success equation. It has no execution or body-law field. -/
def Origin (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) : Prop :=
  ∃ request signature generic,
    signature ∈ program.signatures.functions ∧ generic ∈ program.functions ∧
    resolveRequest program request = .ok specialized ∧
    SourceSpecialization.specializeFunction signature generic request.parameterSubstitution = .ok specialized

theorem resolve_origin {program : CheckedProgram} {request : Request}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : resolveRequest program request = .ok specialized) : Origin program specialized := by
  have resolved := accepted
  unfold resolveRequest at accepted
  obtain ⟨declaration, _, accepted⟩ := bind_ok accepted
  split at accepted
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  · obtain ⟨signature, selectedSignature, accepted⟩ := bind_ok accepted
    obtain ⟨generic, selectedGeneric, accepted⟩ := bind_ok accepted
    have signatureMember : signature ∈ program.signatures.functions := by
      change (match program.signatures.functions.filter (fun signature =>
        decide (signature.id = request.declaration)) with
        | [] => .error (.missingSignature request.declaration)
        | [signature] => .ok signature
        | signatures => .error (.duplicateSignatures request.declaration signatures.length) : Except SourceSpecializationWorklist.Error ProgramFunctionSignature) =
          .ok signature at selectedSignature
      split at selectedSignature
      · cases selectedSignature
      · rename_i entry same
        cases selectedSignature
        exact (List.mem_filter.mp (same ▸ List.mem_cons_self)).1
      · cases selectedSignature
    have genericMember : generic ∈ program.functions := by
      change (match program.functions.filter (fun generic =>
        decide (generic.declaration = request.declaration)) with
        | [] => .error (.missingFunction request.declaration)
        | [generic] => .ok generic
        | functions => .error (.duplicateFunctions request.declaration functions.length) : Except SourceSpecializationWorklist.Error CheckedFunction) =
          .ok generic at selectedGeneric
      split at selectedGeneric
      · cases selectedGeneric
      · rename_i entry same
        cases selectedGeneric
        exact (List.mem_filter.mp (same ▸ List.mem_cons_self)).1
      · cases selectedGeneric
    cases specializedEq : SourceSpecialization.specializeFunction signature generic
        request.parameterSubstitution with
    | error error => simp [specializedEq, throw, throwThe, MonadExceptOf.throw] at accepted
    | ok output =>
      simp only [specializedEq, pure, Except.pure, Except.ok.injEq] at accepted
      subst output
      exact ⟨request, signature, generic, signatureMember, genericMember, resolved, specializedEq⟩

private theorem next_resolved {program : CheckedProgram} {seen : List SourceSpecialization.SpecializationKey}
    {queue rest : List Request} {request : Request} {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : nextUnseen program seen queue = .ok (some (request, specialized, rest))) :
    resolveRequest program request = .ok specialized := by
  induction queue with
  | nil => cases accepted
  | cons head tail ih =>
    unfold nextUnseen at accepted
    obtain ⟨value, resolved, accepted⟩ := bind_ok accepted
    split at accepted
    · exact ih accepted
    · cases accepted
      exact resolved

private theorem runAux_origins {program : CheckedProgram}
    {seedKeys seen : List SourceSpecialization.SpecializationKey} {queue : List Request}
    {entries : List SourceSpecialization.SpecializedFunction} {calls : List CallEdge}
    {references : List ReferenceEdge} {budget : Nat} {outcome : Outcome}
    (initial : ∀ row ∈ entries, Origin program row)
    (accepted : runAux program seedKeys queue seen entries calls references budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Origin program row := by
  induction budget generalizing queue seen entries calls references outcome with
  | zero =>
    unfold runAux at accepted
    obtain ⟨next, _, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact initial
    | some item => rcases item with ⟨request, selected, rest⟩; cases accepted; exact initial
  | succ budget ih =>
    unfold runAux at accepted
    obtain ⟨next, found, accepted⟩ := bind_ok accepted
    cases next with
    | none => cases accepted; exact initial
    | some item =>
      rcases item with ⟨request, selected, rest⟩
      obtain ⟨⟨requests, newCalls, newReferences⟩, _, accepted⟩ := bind_ok accepted
      apply ih (accepted := accepted)
      intro row member
      rcases List.mem_append.mp member with old | added
      · exact initial row old
      · have same : row = selected := by simpa using added
        subst row
        exact resolve_origin (next_resolved found)

/-- Only carriers actually appended by the successful queue are covered. The
unprocessed candidate at budget exhaustion is not made a retained row. -/
theorem worklist_origins {program : CheckedProgram} {requests : List Request}
    {budget : Nat} {outcome : Outcome} (accepted : run program requests budget = .ok outcome) :
    ∀ row ∈ outcome.plan.specializations, Origin program row := by
  unfold run at accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  exact runAux_origins (by simp) accepted

/-- Success of the current pure compiler retains the original complete plan
from the actual worklist, before detached method preparation extends it. -/
theorem compiler_plan {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled) :
    ∃ requests, run program requests options.specializationBudget = .ok (.complete compiled.plan) := by
  unfold SourceCoreCompiler.compileChecked at accepted
  obtain ⟨requests, _, accepted⟩ := bind_ok accepted
  obtain ⟨outcome, worklist, accepted⟩ := bind_ok accepted
  have worklist := mapError_ok worklist
  cases outcome with
  | budgetExhausted plan next pending =>
    change Except.error (SourceCoreCompiler.Error.specializationBudgetExhausted next pending.length) = .ok compiled at accepted
    cases accepted
  | complete plan =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · split at accepted
      · split at accepted
        · cases accepted; exact ⟨requests, worklist⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
      · split at accepted
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
        · split at accepted
          · obtain ⟨roots, _, accepted⟩ := bind_ok accepted
            split at accepted
            · cases accepted; exact ⟨requests, worklist⟩
            · simp [throw, throwThe, MonadExceptOf.throw] at accepted
          · simp [throw, throwThe, MonadExceptOf.throw] at accepted

theorem public_origins {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe) :
    recipe.compiled.sourceProgram = program ∧
      ∀ row ∈ recipe.compiled.validationPlan.specializations, Origin program row := by
  obtain ⟨source, generated, cached, _⟩ := RecursiveNamedPreparedStageContracts.public_compilation accepted issued
  obtain ⟨programEq, planEq, _⟩ := SourceCoreCompiler.Compiled.artifact_fields source cached
  obtain ⟨requests, worklist⟩ := compiler_plan generated
  refine ⟨programEq.trans (SourceCoreCompiler.compileChecked_program generated), ?_⟩
  rw [planEq]
  exact worklist_origins worklist

private theorem mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {input : α}
    (accepted : inputs.mapM action = .ok outputs) (member : input ∈ inputs) :
    ∃ output ∈ outputs, action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => cases member
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨first, by simp, generated⟩
    · obtain ⟨output, outputMember, generated⟩ := ih remaining member
      exact ⟨output, by simp [outputMember], generated⟩

/-- A retained original row survives method-plan growth as the same complete
carrier. Reversed mapM preparation supplies its real physical named slot. -/
theorem cached_row (compiled : SourceCoreUnifiedCompilation.Compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.validationPlan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function), compiled.indexed.base.functions[index]? = some named ∧ named.specialized = row := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled
  obtain ⟨growth, _⟩ := CallableCoercionPreparation.of_accepted prepared
  have retained := growth.entries.subset member
  have generated := RecursiveNamedPreparedParameterProjections.automatic_functions compiled.compatiblePrepared
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared] at retained
  obtain ⟨named, namedMember, accepted⟩ := mapM_member generated (List.mem_reverse.mpr retained)
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp namedMember
  refine ⟨index, named, ?_, (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1⟩
  rwa [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]

/-- Every field is an actual static factory receipt. The dictionary keeps
all recursive evidence and the compiler's original list order. -/
structure Prepared (compiled : SourceCoreUnifiedCompilation.Compiled)
    (row : SourceSpecialization.SpecializedFunction) where
  index : Nat
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Core.Expr
  compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  selected : compiled.indexed.base.functions[index]? = some named
  same : named.specialized = row
  cached : compiled.indexed.secondPass.closures[index]? = some code
  origin : Origin compiled.sourceProgram row
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram row.key row.assumptions =
    .ok available

theorem of_public_compile {program : CheckedProgram} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {compiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompiler.compileChecked program seeds options = .ok compiled)
    (issued : RecursiveNamedPreparedStageContracts.PublicRecipe compiled recipe)
    (member : row ∈ recipe.compiled.validationPlan.specializations) :
    Nonempty (Prepared recipe.compiled row) := by
  obtain ⟨programEq, origins⟩ := public_origins accepted issued
  obtain ⟨index, named, selected, same⟩ := cached_row recipe.compiled member
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := CallableIndexedNamedGeneration.compiled_at recipe.compiled.indexed selected
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled
  obtain ⟨growth, covered⟩ := CallableCoercionPreparation.of_accepted prepared
  obtain ⟨available, resolved, _⟩ := covered row (growth.entries.subset member)
  exact ⟨⟨index, named, diagnostics, code, compilation, available, selected, same, cached,
    by simpa only [programEq] using origins row member, resolved⟩⟩

/-- This global source view has empty lexical capture and the actual resolved
dictionary, including nonempty constraints. No native closure is inferred. -/
def Prepared.view {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row) : Dynamic.Closure :=
  { RecursiveNamedPreparedSourceFrames.view compiled.sourceProgram prepared.named prepared.compilation.statements with
    evidence := CallableNamedMetadata.environment prepared.available }

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

include prepared

theorem instantiated (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationBodyFacts.instantiated signatureMember genericMember accepted
    (RecursiveNamedSpecializationValidity.valid_of_program wellFormed signatureMember accepted range)

theorem source_frame (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  refine ⟨prepared.instantiated wellFormed range, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact congrArg (fun row => row.function.typedBody) prepared.same
  · exact congrArg (fun row => (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context) prepared.same
  · exact congrArg (fun row => row.function.typedBody.inputs) prepared.same
  · exact congrArg (fun row => row.function.inferredBodyType) prepared.same
  · change Dynamic.StatementRoots row.function.typedBody.roots prepared.compilation.statements
    simpa only [prepared.same] using RecursiveNamedPreparedSourceFrames.compiled_roots prepared.compilation
  · exact CallableEvidenceEnvironment.resolved_covers rfl prepared.resolved

theorem agreement : CompatibleNamedBody.NamedAgreement prepared.named prepared.view := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have original := RecursiveNamedPreparedSourceFrames.agreement accepted prepared.compilation
  exact ⟨original.source, original.roots, original.parameters, original.result⟩

theorem has_stages (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Staging.FunctionHasStages row.function := by
  obtain ⟨request, signature, generic, _, genericMember, _, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationStageFacts.has_stages_of_program wellFormed genericMember accepted

/-- Actual ordered evidence is valid and covers the full specialized source
context. Equality of predicate keys alone is not used as a dictionary proof. -/
theorem dictionary :
    (CallableNamedMetadata.environment prepared.available).Valid compiled.sourceProgram.signatures.resolutionRules ∧
    (CallableNamedMetadata.environment prepared.available).map Prod.fst = row.assumptions :=
  CallableEvidenceEnvironment.resolved_valid prepared.resolved

/-- Authentication fixes the complete recursive dictionary, including unused
rows. It does not compare only goals or infer an arbitrary source dictionary. -/
theorem authenticated_dictionary {actual : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence
      compiled.sourceProgram.signatures row.key row.assumptions actual = .ok ()) :
    actual = prepared.available :=
  CallableNamedMetadata.authenticated_evidence_eq authenticated prepared.resolved

theorem retained_frame (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  have frame := prepared.source_frame wellFormed range
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates frame.instantiated,
    frame.source, frame.context, frame.parameters, frame.result, frame.captured, frame.roots, frame.covers⟩

/-- The generic program's independent global call and its actual specialized
body use the same dictionary, outcome and whole heap in both directions. -/
theorem call_outcome_iff (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : row.function.typedBody.inputs.length = arguments.length) :
    FunctionCallBody.Outcome (Program.ofChecked compiled.sourceProgram) context caller prepared.view.evidence before
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) arguments outcome after ↔
    NamedCalls.BodyOutcome (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      prepared.view.evidence before arguments outcome after := by
  have frame := prepared.source_frame wellFormed range
  exact ⟨BuiltinNamedCalls.source_dispatch wellFormed.function_ids frame (by rwa [frame.parameters]), frame.call⟩

end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
/-! A finite named-call inventory contains source attribution, actual compiler
and cached hook receipts. Body profiles are kept separately, so recursive
catalog membership does not require recursive semantic evidence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedParameterCertificates
abbrev ValuesContext := SourceCoreCompatibleValues.Context

structure Header {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)


abbrev Inventory {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) :=
  List (Header prepared values definitions program)

/-- Construct a header from the complete actual static receipts and the
runtime validity of its actual source context. -/
abbrev Header.of_dictionary_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)) :
    Header prepared values definitions program :=
  { function := function
    instantiation := instantiation
    sourceBody := sourceBody
    frame := frame
    named := named
    agreement := agreement
    ordinaryReturn := ordinaryReturn
    ordinaryParameters := ordinaryParameters
    target := target
    context := context
    types := types
    bindings := bindings
    parameters := parameters
    inputs := inputs
    extended := extended
    solved := solved
    reasonAt := reasonAt
    readFuel := readFuel
    output := output
    policy := policy
    fuel := fuel
    fellThrough := fellThrough
    escaped := escaped
    body := body
    parameterCode := parameterCode
    code := code
    layouts := layouts
    owner := owner
    active := active
    globals := globals
    onError := onError
    acceptedPrefix := acceptedPrefix
    hook := hook
    definitions_eq := definitions_eq
    registered := registered
    valid := valid
    unique := unique
    parameterType := parameterType
    resultType := resultType
    representation := representation
    compiledFuel := compiledFuel
    compiled := compiled
    slot := slot
    selected := selected
    cached := cached }

abbrev Header.of_runtime_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (closed : named.specialized.assumptions = [])
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)) :
    Header prepared values definitions program :=
  let _ := closed
  Header.of_dictionary_body
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (valid := valid)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)

/-- Independent source typing supplies runtime ledger validity and the
actual SourceFrame supplies coverage, including retained unused rows. -/
def Header.of_dictionary_frame {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code))
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved) :
    Header prepared values definitions program :=
  Header.of_dictionary_body
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)
    (valid := CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger)

def Header.of_source_frame {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (function : Dynamic.Closure)
    (instantiation : DeclarationInstantiation)
    (sourceBody : Dynamic.BodyInstance)
    (frame : NamedCalls.SourceFrame program instantiation sourceBody function)
    (named : SourceCoreGeneralFunctions.Function)
    (agreement : CompatibleNamedBody.NamedAgreement named function)
    (closed : named.specialized.assumptions = [])
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key)
    (context : SourceSemantics.Context)
    (types : List TypeSystem.Ty)
    (bindings : List Binding)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word)
    (readFuel : Nat)
    (output : Ty)
    (policy : SourceCoreLoops.Policy)
    (fuel : Nat)
    (fellThrough : Word)
    (escaped : Word)
    (body : Expr)
    (parameterCode : Expr)
    (code : Expr)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution)
    (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
    (definitions_eq : layouts.definitions = definitions)
    (registered : prepared.layout.frame.Registered definitions)
    (unique : NodeOccurrencesUnique function.source)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
    (resultType : named.signature.resultType = output)
    (representation : SourceCoreGeneralFunctions.Representation)
    (compiledFuel : Nat)
    (compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel)
    (slot : Nat)
    (selected : base.functions[slot]? = some named)
    (cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code))
    (programTyped : ProgramWellFormed program)
    (sameLedger : function.context.solvedRequirements = solved) :
    Header prepared values definitions program :=
  let _ := closed
  Header.of_dictionary_frame
    (function := function)
    (instantiation := instantiation)
    (sourceBody := sourceBody)
    (frame := frame)
    (named := named)
    (agreement := agreement)
    (ordinaryReturn := ordinaryReturn)
    (ordinaryParameters := ordinaryParameters)
    (target := target)
    (context := context)
    (types := types)
    (bindings := bindings)
    (parameters := parameters)
    (inputs := inputs)
    (extended := extended)
    (solved := solved)
    (reasonAt := reasonAt)
    (readFuel := readFuel)
    (output := output)
    (policy := policy)
    (fuel := fuel)
    (fellThrough := fellThrough)
    (escaped := escaped)
    (body := body)
    (parameterCode := parameterCode)
    (code := code)
    (layouts := layouts)
    (owner := owner)
    (active := active)
    (globals := globals)
    (onError := onError)
    (acceptedPrefix := acceptedPrefix)
    (hook := hook)
    (definitions_eq := definitions_eq)
    (registered := registered)
    (unique := unique)
    (parameterType := parameterType)
    (resultType := resultType)
    (representation := representation)
    (compiledFuel := compiledFuel)
    (compiled := compiled)
    (slot := slot)
    (selected := selected)
    (cached := cached)
    (programTyped := programTyped)
    (sameLedger := sameLedger)

/-- Forget the old body profile while retaining every actual compilation and
source selection receipt. -/
def Header.of_body {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (body : BuiltinNamedCalls.Body prepared values definitions program) :
    Header prepared values definitions program :=
  Header.of_runtime_body
    (function := body.function)
    (instantiation := body.instantiation)
    (sourceBody := body.sourceBody)
    (frame := body.frame)
    (named := body.named)
    (agreement := body.agreement)
    (closed := body.closed)
    (ordinaryReturn := body.ordinaryReturn)
    (ordinaryParameters := body.ordinaryParameters)
    (target := body.target)
    (context := body.context)
    (types := body.types)
    (bindings := body.bindings)
    (parameters := body.parameters)
    (inputs := body.inputs)
    (extended := body.extended)
    (solved := body.solved)
    (reasonAt := body.reasonAt)
    (readFuel := body.readFuel)
    (output := body.output)
    (policy := body.policy)
    (fuel := body.fuel)
    (fellThrough := body.fellThrough)
    (escaped := body.escaped)
    (body := body.body)
    (parameterCode := body.parameterCode)
    (code := body.code)
    (layouts := body.layouts)
    (owner := body.owner)
    (active := body.active)
    (globals := body.globals)
    (onError := body.onError)
    (acceptedPrefix := body.acceptedPrefix)
    (hook := body.hook)
    (definitions_eq := body.definitions_eq)
    (registered := body.registered)
    (unique := body.unique)
    (parameterType := body.parameterType)
    (resultType := body.resultType)
    (representation := body.representation)
    (compiledFuel := body.compiledFuel)
    (compiled := body.compiled)
    (slot := body.slot)
    (selected := body.selected)
    (cached := body.cached)
    (valid := CompatibleRuntimeContextValidity.of_ordinary body.valid)

theorem Header.of_body_slot {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (body : BuiltinNamedCalls.Body prepared values definitions program) :
    (Header.of_body body).slot = body.slot := rfl

/-- Empty legacy invocation evidence forces empty source predicates through the
actual SourceFrame coverage; general headers retain their full dictionary. -/
theorem Header.predicates_of_empty {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program)
    (empty : header.function.evidence = []) : header.instantiation.predicates = [] := by
  have assumptions : header.sourceBody.context.assumptions = header.instantiation.predicates := by
    cases header.frame.instantiated with
    | intro _ _ _ _ _ _ _ contextEq => rw [contextEq]; rfl
  have supplies := header.frame.covers.2
  rw [empty] at supplies
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro predicate member
  obtain ⟨evidence, found⟩ := supplies predicate (assumptions.symm ▸ member)
  cases found

/-- A real cached row includes its signature, code and ordered slot. -/
theorem Header.cached_code {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program) :
    header.compiled.closures[header.slot]? = some (.lambda header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) header.code) := header.cached

/-- Owner uniqueness fixes independent source dispatch; it is not inferred
from a native signature or a selected slot. -/
theorem Header.source_unique {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (header : Header prepared values definitions program)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    {actual : Dynamic.BodyInstance} (instantiated : Dynamic.FunctionInstantiates program header.instantiation actual) :
    actual = header.sourceBody :=
  BuiltinNamedCalls.instantiation_unique owners instantiated header.frame.instantiated

/-- One actual cached closure ledger can certify every finite header. The
ordered slots and source owner uniqueness remain explicit static obligations. -/
structure Ledger {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {definitions : DataEnvironment} {program : Program}
    (headers : Inventory prepared values definitions program) (closures : List Expr) : Prop where
  slots : (headers.map (·.slot)).Nodup
  owners : (program.functions.map (fun definition => definition.body.owner)).Nodup
  cached : ∀ header, header ∈ headers → closures[header.slot]? = some
    (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
/-! Named source bodies retain the declaration's residual-variable scope.
These facts use structural source instantiation and binder installation only;
no native type, runtime trace, or change to the source context is involved. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

/-- Instantiated declarations have no lexical inference-variable binders and
retain the independent residual-occurrence scope. -/
theorem frame_fields {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
    (frame : NamedCalls.SourceFrame program instantiation body function) :
    function.context.typeVariables = [] ∧ function.context.residualTypeVariables = true := by
  rw [frame.context]
  cases frame.instantiated with
  | intro _ _ _ _ _ _ _ contextEq =>
    rw [contextEq]
    exact ⟨rfl, rfl⟩

/-- Monomorphic parameters preserve both flexible-variable scope fields. -/
theorem mono_fields {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context binders types final) :
    final.typeVariables = context.typeVariables ∧
      final.residualTypeVariables = context.residualTypeVariables := by
  induction extended with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ head _ ih =>
    exact ⟨ih.1.trans head.typeVariables_eq, ih.2.trans head.residualTypeVariables_eq⟩

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The actual catalog header uses the source declaration context after its
real monomorphic input binders have been installed. -/
theorem header_fields (header : Header prepared values definitions program) :
    header.context.typeVariables = [] ∧ header.context.residualTypeVariables = true := by
  have inherited := mono_fields header.extended
  have declaration := frame_fields header.frame
  exact ⟨inherited.1.trans declaration.1, inherited.2.trans declaration.2⟩

theorem header_typeVariables (header : Header prepared values definitions program) :
    header.context.typeVariables = [] := (header_fields header).1

theorem header_residual (header : Header prepared values definitions program) :
    header.context.residualTypeVariables = true := (header_fields header).2

/-- A factory fixed to `false` cannot serve a legitimate named source header. -/
theorem header_not_false (header : Header prepared values definitions program) :
    header.context.residualTypeVariables ≠ false := by
  rw [header_residual header]
  decide

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
end
