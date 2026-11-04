import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.SourceBodyTemplateScope
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.CallableOrdinarySpecializationStageCoherence
import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.SourceBodyResultAnnotation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.CallableOrdinaryMethodCatalogSeparation
import Solcore.SourceSemantics.CoreLowering.CallableSelectedCanonicalSourceErasure
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources

/-!
# Selected compilations: indirect dispatch

Dispatch of indirect calls over retained callees and builtins, in both directions, with the binding, scope and syntax-table facts of ordinary rows that the dispatch reads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
/-! Actual compilation retains the source declaration of every native binding,
including bindings with no prepared instances. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalBindingOrigins

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {value : α} (accepted : action.mapError change = .ok value) : action = .ok value := by
  cases action with
  | error => cases accepted
  | ok result => cases accepted; rfl

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    CatalogOrigins base.plan base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have origins := PreparedLocalBindingOrigins.of_preparation (mapError_ok prepared)
  change CatalogOrigins executable.val locals at origins
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact origins
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have origins := PreparedLocalBindingOrigins.with_contracts origins (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogOrigins automatic.prepared.plan automatic.prepared.locals := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CatalogOrigins compiled.indexed.base.plan compiled.indexed.base.locals := by
  have origins := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact origins

/-- The selected binding is tied to an actual row and complete source collector entry. -/
theorem at_binding (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding) :
    BindingOrigin compiled.indexed.base.plan binding ∧
      binding.caller = caller ∧ binding.binder.id = binder :=
  PreparedLocalBindingOrigins.at_binding (of_compiled compiled) located

theorem statement_at_binding (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding) :
    ∃ statement, Node.statement statement ∈ binding.source.nodes ∧
      statement.form = .letDecl binding.binder (some binding.initializer) :=
  (at_binding compiled located).1.statement

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBindingOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
/-! Actual compiled rows supply the residual-scope validator receipt, including
method and late-added rows. Contextual sources retain the same original row and
the actual cumulative substitution; a header comparison is not used here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
open Frontend SourceInference SourceSpecialization TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

private theorem exact_member {plan : SourceSpecializationWorklist.Plan}
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan owner = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected
  · cases selected
  · next candidate only =>
    cases selected
    have member : row ∈ [row] := by simp
    rw [← only] at member
    exact (List.mem_filter.mp member).1
  · cases selected

/-- This consumes the actual full preparation result, rather than initial plan
membership, so implementation methods and later ordinary rows are included. -/
theorem row_supported (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row) :
    ∀ node ∈ row.function.typedBody.nodes, ResidualNodeSupported row.function.typedBody node := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_node_support specialized

structure ValidatedSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : SourceCompilationPlan.Key) (active : Substitution) (source : TypedSource) where
  original : SpecializedFunction
  selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok original
  source_eq : source = original.function.typedBody.applySubstitution active
  supported : ∀ node ∈ original.function.typedBody.nodes,
    ResidualNodeSupported original.function.typedBody node

/-- The real original or contextual factory fixes the source row. -/
theorem of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram
      compiled.indexed.base.plan owner active source) :
    Nonempty (ValidatedSource compiled owner active source) := by
  cases receipt with
  | original selected =>
      exact ⟨⟨_, selected, (EmptySourceSubstitution.source _).symm, row_supported compiled selected⟩⟩
  | contextual accepted =>
      obtain ⟨row, selected, _, _, source⟩ := LambdaSourceAlignment.prepared_source accepted
      exact ⟨⟨row, selected, source, row_supported compiled selected⟩⟩

theorem invocation_source {compiled : SourceCoreUnifiedCompilation.Compiled}
    {relation : ActualBodyInvocation.BodyRelation}
    (index : ActualBodyInvocation.Index compiled relation) :
    Nonempty (ValidatedSource compiled index.owner index.active index.compilerSource) :=
  of_receipt index.compiler_source_receipt

/-- The accepted Packet and actual catalog binding identify the original
source whose node supports were checked. No candidate Source equality is an
independent premise. -/
theorem binding_supported {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    ∀ node ∈ binding.source.nodes, ResidualNodeSupported binding.source node := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have supported := row_supported compiled selected
  rw [original, source] at supported
  exact supported

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes

/-! The runtime row uses the exact residual scope of each supplied path. -/
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
open Frontend SourceInference SourceSpecialization TypeSystem
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

theorem row_scope_unique (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath row.function.typedBody node left)
    (second : ResidualScopePath row.function.typedBody node right) : left = right := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_scope_unique specialized first second

theorem row_path_support (compiled : SourceCoreUnifiedCompilation.Compiled)
    {owner : SourceCompilationPlan.Key} {row : SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan owner = .ok row)
    {node : Node} (member : node ∈ row.function.typedBody.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath row.function.typedBody node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) := by
  obtain ⟨signature, original, supplied, specialized⟩ :=
    CallablePreparedFinalSpecializationOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row (exact_member selected)
  exact specializeFunction_residual_path_support specialized member path

theorem ValidatedSource.scope_unique {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (validated : ValidatedSource compiled owner active source)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath validated.original.function.typedBody node left)
    (second : ResidualScopePath validated.original.function.typedBody node right) : left = right :=
  row_scope_unique compiled validated.selected first second

theorem ValidatedSource.path_support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (validated : ValidatedSource compiled owner active source)
    {node : Node} (member : node ∈ validated.original.function.typedBody.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath validated.original.function.typedBody node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) :=
  row_path_support compiled validated.selected member path

/-- The stored bundle's actual catalog entry supplies the same original row;
no independent source equality or arbitrary scope agreement is needed. -/
theorem binding_scope_unique {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : NodeId} {left right : List TypeVarId}
    (first : ResidualScopePath binding.source node left)
    (second : ResidualScopePath binding.source node right) : left = right := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have sameSource := original.trans source
  rw [← sameSource] at first second
  exact row_scope_unique compiled selected first second

theorem binding_path_support {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : Node} (present : node ∈ binding.source.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath binding.source node.id variables) :
    (∀ type ∈ residualNodeTypes node, ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables) ∧
    (∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified) := by
  obtain ⟨owner, source, _, _⟩ := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨row, selected, original, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, owner] at selected
  have sameSource := original.trans source
  rw [← sameSource] at present path
  exact row_path_support compiled selected present path

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
/-! The actual final plan's preparation supplies a physical cache position
and the checker body for every retained row, including late-added rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
open Frontend SourceInference SourceSpecializationWorklist
open SourceCompiledLocalFinalization

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

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
      · obtain ⟨output, present, generated⟩ := ih remaining member
        exact ⟨output, by simp [present], generated⟩

theorem row_position (cached : SourceCoreUnifiedCompilation.Compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ cached.indexed.base.plan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧ named.specialized = row := by
  have generated :=
    RecursiveNamedPreparedParameterProjections.automatic_functions cached.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base cached.indexedPrepared
  rw [same] at member
  obtain ⟨named, present, accepted⟩ :=
    mapM_member generated (List.mem_reverse.mpr member)
  obtain ⟨index, position⟩ := List.mem_iff_getElem?.mp present
  refine ⟨index, named, ?_,
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1⟩
  rwa [same]

/-- This selects the body of the same complete row. No initial-plan membership
or independently supplied body typing is needed. -/
theorem row_selection
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ cached.indexed.base.plan.specializations) :
    ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function),
      cached.indexed.base.functions[index]? = some named ∧
      named.specialized = row ∧ Nonempty (BodySelection compiled row fuel) := by
  obtain ⟨index, named, position, same⟩ := row_position cached member
  obtain ⟨selected, _⟩ := SourceBodyTemplateScope.cached_selection_scope artifact checked position
  exact ⟨index, named, position, same, ⟨same ▸ selected⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCachedSources
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectValuesPrefix
/-! Source preservation constructs the callee and ordered argument prefix
at their actual reached states. It retains callee typing and its complete
post for builtin and user application. The application itself follows later. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectValuesPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


/-- Both native prefix actions use the same represented callee and argument
packet. The callee post is retained before the argument effects are composed. -/
def ValuesPrefix (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeStore calleeMap calleeWorld carrier values argumentsStore finalMap finalWorld
      originalNode originalMetadata,
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore ∧
    Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes
      (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes ∧
    Dynamic.HeapMetadataExtend calleeHeap argumentsHeap ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached

include positive prepared sourceEq certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict callee preservation and the real ordered argument fold construct
the full prefix once. The returned admission belongs to the argument endpoint. -/
theorem preserves_values (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {sources : List Dynamic.Value}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    ValuesPrefix (functionModel := functionModel) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      rename_i carrier
      have post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := calleeNode) bridge functions compiler initial
          sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      have sourceValueTyped : Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type :=
        calleeAdmission.at_value.1
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      obtain ⟨rawParameter, rawResult, functionType, argumentsTyped, bundle, resultType⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, finalMap, finalWorld, argumentsEvaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.first_gate
        (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeStore, calleeMap, calleeWorld,
        carrier, values, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
        post, sourceValueTyped, gate, argumentsEvaluated, represented,
        GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, postAdmission.values_typed, heapMetadata, reached, callerProtocol.trans calleeRelated related,
        postAdmission.at_values⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectValuesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectSourcePrefixDispatch
/-! The original recursively staged indirect parent selects its actual executed
prefix. Faults construct full native parent results from strict child hypotheses;
successful arguments retain the original application trace and real native
prefix. No application execution law is supplied to the classifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectSourcePrefixDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

private inductive SourcePrefix (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (call callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | calleeFault {childSize failure after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault failure) after
  | notCallable {childSize value after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (invalid : ¬ Dynamic.CallableValue value) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.semantic .notCallable)) after
  | rejected {childSize value after reason}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards call ids value reason) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.stage invocation call reason)) after
  | argumentsFault {childSize argumentsSize value middle after failure}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize]) (.fault failure) after
  | sourceArity {childSize argumentsSize value middle after values}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.values values) after)
      (mismatch : ids.length ≠ metadata.argumentCount) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize])
        (.fault (.semantic (.argumentArityMismatch metadata.argumentCount ids.length))) after
  | applied {childSize argumentsSize applicationSize value calleeHeap argumentsHeap after values outcome}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) calleeHeap)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment calleeHeap ids (.values values) argumentsHeap)
      (called : Staging.Recursive.Size.Applies program stages applicationSize invocation context
        argumentsHeap value values outcome after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize, applicationSize]) outcome after

private theorem source_prefix
    {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (trace : Staging.Recursive.Size.Expression program stages size invocation context
      environment before id outcome after) :
    SourcePrefix program stages invocation context environment before id callee ids metadata size outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements →
      actualForm = .call callee ids (.indirect metadata) := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at actualForm
      cases actualForm
  | calleeFault occurrence child =>
      cases occurrence_form occurrence
      exact .calleeFault child
  | notCallable occurrence child invalid =>
      cases occurrence_form occurrence
      exact .notCallable child invalid
  | rejected occurrence child rejected =>
      cases occurrence_form occurrence
      exact .rejected child rejected
  | argumentsFault occurrence child accepted arguments =>
      cases occurrence_form occurrence
      exact .argumentsFault child accepted arguments
  | sourceArity occurrence child accepted arguments mismatch =>
      cases occurrence_form occurrence
      exact .sourceArity child accepted arguments mismatch
  | applied occurrence _uncoerced child accepted arguments _arity called =>
      cases occurrence_form occurrence
      exact .applied child accepted arguments called
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ => cases occurrence_form occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

/-- The actual failed Source parent already supplies its original grade,
outcome and heap. This is the native result and complete caller post at that
same endpoint, constructed by strict child preservation. -/
def NativeResultAt (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type
      lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

/-- The successful prefix keeps the actual Source application and its strict
grade, together with the constructed original native callee/arguments and
complete reached admission. It contains no native application law. -/
def ApplicationAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      sourceValue calleeHeap argumentsHeap sources

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver in
/-- The literal original Source trace selects a branch once. Its three prefix
failure constructors produce the complete native parent. The actual successful
argument endpoint is retained for the independent application producer. -/
theorem preserves_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    NativeResultAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after ∨
    ApplicationAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget size outcome after := by
  have parentFound : invocation.source.lookupExpression? id = some compiler.original := by
    rw [sourceEq]
    exact compiler.found
  have selected := source_prefix unique parentFound compiler.originalForm trace
  cases selected with
  | calleeFault child =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectCalleeFaultBounds.preserves_callee_fault
        bridge functions compiler prepared sourceEq occurrence certified found sourceTyped
        environments heaps locals agrees typed initial admitted budget children child within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | @notCallable childSize sourceValue after child invalid =>
    have smaller : childSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := childSize) (children := [childSize]) (by simp)) within
    have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
    have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
      children _ smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
    cases represented with
    | value payload =>
      obtain ⟨_originalNode, _originalMetadata, _contains, _form, _view, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique
          ⟨evaluated, payload, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
      cases boundary with
      | user dispatch _ =>
        have callable := (CallableLedger.frame sidecar).userCallable dispatch.bound
        cases callable <;> exact False.elim (invalid trivial)
      | builtin _ => exact False.elim (invalid trivial)
  | rejected child rejected =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.preserves_rejected
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame
        profile certified found sourceTyped environments heaps locals agrees typed admitted
        caller originalUnique sourceParent tree unique parentTyped budget children child within rejected
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | argumentsFault child accepted arguments =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.preserves_argument_fault
        bridge profile compiler prepared sourceEq occurrence certified found sourceTyped environments heaps locals
        agrees typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
        budget children child accepted arguments within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | sourceArity _ _ _ mismatch => exact False.elim (mismatch sourceParent.arity)
  | @applied calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap after sources outcome child accepted arguments called =>
    have prefixBound : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget := by
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    have strict : applicationSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := applicationSize) (children := [calleeSize, argumentsSize, applicationSize]) (by simp)) within
    have constructedPrefix := SelectedCompilationIndirectValuesPrefix.preserves_values
      bridge profile compiler prepared sourceEq certified found sourceTyped environments heaps locals agrees
      typed initial admitted caller view originalUnique guardFrame sourceParent tree unique parentTyped
      budget children child accepted arguments prefixBound
    exact .inr ⟨_, _, _, _, _, _, _, rfl, strict, child, accepted, arguments, called, constructedPrefix⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectSourcePrefixDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeArgumentPrefix
/-! Successful ordered arguments retain the actual successful callee post and Source value typing from the same strict child proof. The authentic original fault branches and reached argument state stay unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)


open CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix (StageRejectedPrefix ArgumentFaultPrefix)

/-- Successful arguments retain the literal successful callee receipt before the original producer erases it. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap calleeStore calleeMap calleeWorld sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes ∧
    Dynamic.HeapMetadataExtend calleeHeap argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

omit positive in
/-- The original application suffix is recovered by forgetting only the additional callee receipt. -/
theorem ApplicationPrefix.to_original {budget : Nat} {value : Value} {finalStore : Store}
    (retained : ApplicationPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, sourceValue, calleeHeap, _calleeStore, _calleeMap, _calleeWorld,
    sources, values, carrier, argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode,
    originalMetadata, _calleePost, _valueTyped, tail⟩ := retained
  obtain ⟨calleeTrace, accepted, argumentsTrace, represented, related, callView, boundary, heaps, maps, worlds, frame, metadata, _typed, _argumentMetadata, reached, suffix⟩ := tail
  exact ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, argumentsHeap,
    argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, calleeTrace, accepted, argumentsTrace, represented, related, callView, boundary, heaps, maps, worlds, frame, metadata, reached, suffix⟩

private theorem argument_fault_post {types : List TypeSystem.Ty} {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : SelectedCompilationExpressionSequence.PostAdmission bridge types
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include positive prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CallableIndexedOwnedPreparedStagedIndirectNativePrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore ∨
    ArgumentFaultPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CallableIndexedOwnedPreparedStagedIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed initial admitted
      budget children completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        have retainedCalleePost := calleePost
        obtain ⟨_calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              SelectedCompilationExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              SelectedCompilationExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld,
                  sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, retainedCalleePost, calleeAdmission.at_value.1,
                  calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, post.values_typed, heapMetadata, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeArgumentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeFaultDispatch
/-! The actual whole native parent retains its successful callee receipt through ordered arguments. Fault branches preserve the original result; the successful branch exposes the same reached suffix and callee typing to its application producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedIndirectFaultDispatch (FaultResult)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (functionModel)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include positive receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    SelectedCompilationIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases SelectedCompilationIndirectRetainedCalleeArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CallableIndexedOwnedPreparedStagedIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectRetainedCalleeFaultDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinPreservationDispatch
/-! The constructed successful callee and argument prefix supplies builtin
parent preservation at its actual reached state. The selected physical count
is decided internally. A user callee retains the same full prefix for its
body producer. No complete application or body law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinPreservationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


/-- The exact original Source parent and its native result share the actual
reached caller endpoint. The two traces have independent sizes. -/
def ParentAt (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
    invocation context environment before id outcome after ∧
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached

variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)

include positive sourceParent occurrence preparedStages receiver actualFunctionType observations in
/-- The authentic prefix is classified once. Successful builtin execution
uses its original primitive; physical mismatch uses the actual receiving
arity word. Both branches construct the whole native parent without replay. -/
theorem preserves_builtin_or_user
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (prefixResult : SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    (Staging.CallBoundary.UserCallable sourceValue ∧
      SelectedCompilationIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
        (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
        (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
        (calleeNode := calleeNode) (sidecar := sidecar)
        bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) ∨
    ParentAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  have originalPrefix := prefixResult
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, valueTyped, _gate, argumentsNative,
    representedValues, representedCallee, _callView, boundary, finalHeaps, maps, worlds,
    frame, heapMetadata, _argumentsTyped, _argumentMetadata, reached, related, admitted⟩ := prefixResult
  cases boundary with
  | user dispatch selected =>
      exact .inl ⟨(CallableLedger.frame sidecar).userCallable dispatch.bound, originalPrefix⟩
  | builtin receipt =>
      rename_i function row
      by_cases count : row.entry.parameterCount = ids.length
      · rw [functionType] at valueTyped representedCallee
        have completeParent :
            Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
              (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
              invocation context environment before id outcome after ∧
            ∃ value,
              Evaluates actual store (lowered.expression.rename ξ) value argumentsStore ∧
              RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
                compiler.original.type lowered.type callFaults outcome value ∧
              after = argumentsHeap ∧
              GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
              LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
              AdministrativePreserved mapping store finalMap argumentsStore ∧
              Dynamic.HeapMetadataExtend before argumentsHeap ∧
              callerProtocol.Relates initial reached ∧
              CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type outcome reached :=
          CallableIndexedOwnedPreparedStagedBuiltinParentPreservation.preserves_parent
            (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
            (registry := completion.result.context.registry) (semanticFaults := semanticFaults)
            (profile := profile) (faults := callFaults)
            (context := context) (stages := stages) (invocation := invocation)
            (environment := environment) (actual := actual) (ξ := ξ)
            (mapping := mapping) (finalMap := finalMap) (world := world) (finalWorld := finalWorld)
            (before := before) (calleeHeap := calleeHeap) (argumentsHeap := argumentsHeap)
            (store := store) (argumentsStore := argumentsStore) (canonical := canonical)
            (identities := identities) (function := function) (carrier := carrier) (row := row)
            (sources := sources) (values := values) (sourceTypes := sourceTypes)
            (parameter := rawParameter) (result := rawResult) (sidecar := sidecar)
            (originalNode := originalNode) (originalMetadata := originalMetadata)
            (calleeSize := calleeSize) (argumentsSize := argumentsSize) (applicationSize := applicationSize)
            (outcome := outcome) (after := after) (calleeStore := calleeStore)
            bridge compiler prepared sourceParent occurrence initial reached related admitted
            finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
            valueTyped (SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile) representedCallee) representedValues bundle resultType calleeTrace argumentsTrace
            called calleePost.1 argumentsNative
        obtain ⟨parentSource, value, native, representation, sameHeap, heaps,
          keptMaps, keptWorlds, keptFrame, keptMetadata, keptRelated, post⟩ := completeParent
        cases sameHeap
        exact .inr ⟨parentSource, value, argumentsStore, finalMap, finalWorld,
          native, representation, heaps, keptMaps, keptWorlds, keptFrame, keptMetadata,
          reached, keptRelated, post⟩
      · have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have physical : function.id.parameterTypes.length ≠ ids.length := by
          simpa only [receipt.parameter_count] using count
        cases called with
        | builtin primitive =>
            have originalCount := Dynamic.BuiltinApplies.argument_count primitive
            exact False.elim (physical (valuesCount.symm.trans originalCount).symm)
        | builtinType arity mismatch =>
            exact False.elim (physical (arity.trans valuesCount))
        | builtinArity mismatch =>
            have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
                (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
                (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
              simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
                using argumentsNative
            have native := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_native_preserves
              (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
              (result := compiler.resultType) receipt physical calleePost.1 argumentsWeaken
            change Evaluates actual store
              (CallableContract.call prepared.site.gates
                compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
                (compiler.calleeCode.expression.rename ξ)
                ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
            rw [← prepared.lowered_rename compiler ξ] at native
            obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
              CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
                compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
                (sourceResult := compiler.original.type) (resultCore := lowered.type) count
            cases sameState
            have loweredType : lowered.type = compiler.resultType :=
              (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
            have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
            have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
                compiler.original.type
                (.fault (.semantic (.argumentArityMismatch function.id.parameterTypes.length sources.length))) reached :=
              ⟨admitted.rows, by intro value impossible; cases impossible⟩
            refine .inr ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
              argumentsTrace sourceParent.arity (.builtinArity mismatch),
              .inLeft lowered.type (.word (prepared.site.reasonAt row.caller row.call row.entry.id
                .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length))),
              argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
              heapMetadata, reached, related, post⟩
            · simpa only [loweredType] using native
            · simpa only [receipt.parameter_count, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinPreservationDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinApplicationDispatch
/-! The actual retained argument prefix classifies its selected payload once.
Builtin physical mismatch produces the receiving semantic arity post; equal
count uses the original primitive at the same argument endpoint. A user
payload keeps its authentic callee, ordered arguments and application suffix.
The strict prefix producer remains responsible for constructing this input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinApplicationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- The user predicate concerns the same retained callee and suffix witness.
Its body, global provenance and physical-count decision remain future work. -/
def UserApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceValue, Staging.CallBoundary.UserCallable sourceValue ∧
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize calleeHeap calleeStore calleeMap calleeWorld sources values carrier
      argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functions compiler initial sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes ∧
    Dynamic.HeapMetadataExtend calleeHeap argumentsHeap ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ suffixSize, EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ suffixSize < budget

omit positive in
/-- Forgetting only the positive user classification keeps the original full
retained callee post and every transient argument effect. -/
theorem UserApplicationPrefix.to_retained {budget : Nat} {value : Value} {finalStore : Store}
    (user : UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    SelectedCompilationIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  obtain ⟨sourceValue, _user, rawParameter, rawResult, functionType, bundle, resultType,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩

/-- Full parent meaning is constructed only after the actual builtin row has
been classified. The reached caller and both independent grades stay literal. -/
def ParentResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id outcome after ∧
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome reached

section Classification
variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (functionModel) identities)

include positive sourceParent occurrence preparedStages receiver actualFunctionType observations in
/-- No callee or argument is replayed. The genuine prefix's selected BoundaryAt
either retains its user suffix, or decides builtin physical arity internally.
An accepted builtin uses the original complete parent reflection once. -/
theorem reflects_builtin_or_user {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (retained : SelectedCompilationIndirectRetainedCalleeArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore) :
    UserApplicationPrefix (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore ∨
    ParentResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
    sourceValue, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, valueTyped, child, accepted, arguments, representedValues, representedCallee,
    callView, boundary, finalHeaps, maps, worlds, frame, heapMetadata, argumentsTyped, argumentMetadata,
    ⟨reached, related, admitted⟩, suffixSize, suffix, strict⟩ := retained
  cases boundary with
  | user dispatch selected =>
    exact .inl ⟨sourceValue, (CallableLedger.frame sidecar).userCallable dispatch.bound,
      rawParameter, rawResult, functionType, bundle, resultType, calleeSize, argumentsSize,
      calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier, argumentsHeap,
      argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, calleePost, valueTyped,
      child, accepted, arguments, representedValues, representedCallee, callView, .user dispatch selected,
      finalHeaps, maps, worlds, frame, heapMetadata, argumentsTyped, argumentMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩
  | builtin receipt =>
    rename_i function row
    by_cases count : row.entry.parameterCount = ids.length
    · rw [functionType] at valueTyped representedCallee
      obtain ⟨sourceResult, parentTrace, resultRep, sameStore, heaps, keptMaps, keptWorlds,
        keptFrame, keptMetadata, keptRelated, post⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinParentBounds.reflects_suffix
          bridge compiler prepared sourceParent occurrence initial reached related admitted
          finalHeaps maps worlds frame heapMetadata observations receipt count actualFunctionType
          valueTyped (SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual.erase (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := semanticFaults) (profile := profile) representedCallee) representedValues bundle resultType child arguments suffix (Nat.le_of_lt strict)
      cases sameStore
      exact .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .value sourceResult, argumentsHeap, finalMap, finalWorld, parentTrace, completed.sound, resultRep,
        heaps, keptMaps, keptWorlds, keptFrame, keptMetadata, reached, keptRelated, post⟩
    · obtain ⟨raw, shape⟩ := receipt.shape
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          shape receipt.selected receipt.selected.found count suffix
      cases sameStore
      have physical : function.id.parameterTypes.length ≠ ids.length := by
        simpa only [receipt.parameter_count] using count
      have sourceFault := CallableIndexedOwnedPreparedSecondCallGateRejection.builtin_source
        occurrence compiler.argumentCoercions sourceParent.arity arguments child physical
      obtain ⟨represented, keptHeaps, keptState, sameState, _keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages receipt.selected receiver initial functions reached related finalHeaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      have valueShape : value = .inLeft lowered.type (.word
          (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
            (.argumentArityMismatch row.entry.parameterCount ids.length))) := by
        simpa only [loweredType] using sameValue
      have faultRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
          compiler.original.type lowered.type callFaults
          (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) value := by
        rw [valueShape]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented
      refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)), argumentsHeap,
        finalMap, finalWorld, ?_, completed.sound, faultRep, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, related, ?_⟩
      · simpa only [receipt.parameter_count] using sourceFault
      · exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

end Classification
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationIndirectBuiltinApplicationDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
open Frontend SourceInference TypeSystem

private def instructionBinders : MatchPatternInstruction → List TypedBinder
  | .binder binder => [binder]
  | _ => []

private def patternBinders : MatchPatternResolution → List TypedBinder
  | .binder binder => [binder]
  | .constructor _ instructions | .tuple instructions => instructions.flatMap instructionBinders
  | _ => []

private def allowed (source : TypedSource) (binder : TypedBinder)
    (initializer : Option ExpressionId) : Bool :=
  !binder.scheme.quantified.isEmpty && initializer.any (SourceSpecialization.isDirectLambdaInitializer source)

private def rejectedBinders (source : TypedSource) : Node → List TypedBinder
  | .expression node => match node.form with
    | .lambda parameters _ _ => parameters.filter fun binder => !binder.scheme.quantified.isEmpty
    | _ => []
  | .statement node => match node.form with
    | .letDecl binder initializer =>
      if binder.scheme.quantified.isEmpty || allowed source binder initializer then [] else [binder]
    | .forLoop initializer _ post _ => (initializer ++ post).filterMap fun
      | .letDecl binder _ => if binder.scheme.quantified.isEmpty then none else some binder
      | _ => none
    | .matchWith resolution => resolution.cases.flatMap fun arm =>
      (patternBinders arm.pattern.resolution).filter fun binder => !binder.scheme.quantified.isEmpty
    | _ => []

private def positionCheck (source : TypedSource) : Except SourceSpecialization.Error Unit :=
  match ((source.inputs.filter fun binder => !binder.scheme.quantified.isEmpty) ++
      source.nodes.flatMap (rejectedBinders source)).head? with
  | some binder => .error (.polymorphicBinder binder.id binder.scheme.quantified)
  | none => .ok ()

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) : action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted

private theorem positions_of_specialization {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized) :
    positionCheck specialized.function.typedBody = .ok () := by
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
  obtain ⟨_, residuals, accepted⟩ := bind_ok accepted
  obtain ⟨position, positions, _⟩ := bind_ok residuals
  change positionCheck (SourceSpecialization.applyCheckedFunction canonical generic).typedBody = .ok position at positions
  cases position
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
    simp only [analysis, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at accepted
    subst specialized
    exact positions

private theorem no_rejected {source : TypedSource} (accepted : positionCheck source = .ok ()) :
    source.nodes.flatMap (rejectedBinders source) = [] := by
  unfold positionCheck at accepted
  split at accepted
  next binder found => cases accepted
  next absent =>
    have empty := List.head?_eq_none_iff.mp absent
    exact (List.append_eq_nil_iff.mp empty).2

/-- The successful original specialization checks every stored let, including
statements after a return. A quantified binder must name a direct lambda. -/
theorem initialized_direct_lambda {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    {node : StatementNode} {binder : TypedBinder} {initializer : Option ExpressionId}
    (member : Node.statement node ∈ specialized.function.typedBody.nodes)
    (form : node.form = .letDecl binder initializer)
    (polymorphic : binder.scheme.quantified ≠ []) :
    ∃ expression, initializer = some expression ∧
      SourceSpecialization.isDirectLambdaInitializer specialized.function.typedBody expression = true := by
  have empty := no_rejected (positions_of_specialization accepted)
  have localEmpty : rejectedBinders specialized.function.typedBody (.statement node) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro actual present
    have all : actual ∈ specialized.function.typedBody.nodes.flatMap
        (rejectedBinders specialized.function.typedBody) := List.mem_flatMap.mpr ⟨_, member, present⟩
    rw [empty] at all
    cases all
  have nonempty : binder.scheme.quantified.isEmpty = false := by
    cases same : binder.scheme.quantified with
    | nil => exact False.elim (polymorphic same)
    | cons => rfl
  simp only [rejectedBinders, form, nonempty, Bool.false_or, allowed, Bool.not_false, Bool.true_and] at localEmpty
  split at localEmpty
  next accepted =>
    cases initializer with
    | none => simp at accepted
    | some expression => exact ⟨expression, rfl, accepted⟩
  next => cases localEmpty

/-- This source-wide endpoint also accounts for initialized `for` header
binders, which the original specialization requires to be monomorphic. -/
theorem initialized_position {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
    {binder : TypedBinder} (member : binder ∈ specialized.function.typedBody.initializedLetBinders)
    (polymorphic : binder.scheme.quantified ≠ []) :
    ∃ node initializer, Node.statement node ∈ specialized.function.typedBody.nodes ∧
      node.form = .letDecl binder (some initializer) ∧
      SourceSpecialization.isDirectLambdaInitializer specialized.function.typedBody initializer = true := by
  obtain ⟨node, present, binderMember⟩ := List.mem_flatMap.mp member
  cases node with
  | expression node => cases binderMember
  | statement node =>
    change binder ∈ node.form.initializedLetBinders at binderMember
    cases form : node.form <;> simp only [form, StatementForm.initializedLetBinders] at binderMember
    case letDecl actual initializer =>
      cases initializer with
      | none => cases binderMember
      | some initializer =>
        have same : binder = actual := by simpa using binderMember
        subst actual
        obtain ⟨expression, same, direct⟩ := initialized_direct_lambda accepted present form polymorphic
        cases Option.some.inj same
        exact ⟨node, initializer, present, form, direct⟩
    case forLoop initializer condition post body =>
      have inItems : binder ∈ (initializer ++ post).flatMap ForItemForm.initializedLetBinders := by
        simpa only [List.flatMap_append] using binderMember
      obtain ⟨item, itemMember, localMember⟩ := List.mem_flatMap.mp inItems
      have nonempty : binder.scheme.quantified.isEmpty = false := by
        cases same : binder.scheme.quantified with
        | nil => exact False.elim (polymorphic same)
        | cons => rfl
      have rejected : binder ∈ rejectedBinders specialized.function.typedBody (.statement node) := by
        simp only [rejectedBinders, form]
        apply List.mem_filterMap.mpr
        refine ⟨item, itemMember, ?_⟩
        cases item <;> simp only [ForItemForm.initializedLetBinders] at localMember
        case letDecl actual initializer =>
          cases initializer with
          | none => cases localMember
          | some initializer =>
            have same : binder = actual := by simpa using localMember
            subst actual
            simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
        all_goals cases localMember
      have all : binder ∈ specialized.function.typedBody.nodes.flatMap
          (rejectedBinders specialized.function.typedBody) := List.mem_flatMap.mpr ⟨_, present, rejected⟩
      rw [no_rejected (positions_of_specialization accepted)] at all
      cases all
    all_goals cases binderMember

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSpecializationBinders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
/-! Actual cache eligibility requires the original signature catalog. Unselected
ordinary and method bodies do not enter this executable table scan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
open Frontend SourceInference
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible)
open CallableIndexedOwnedPreparedOrdinarySyntaxTable (range? Table)

def eligible? (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (fuel : Nat) {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named) :
    Option (PLift (Eligible compiled named.specialized)) := do
  match found : compiled.sourceProgram.signatures.functions.find?
      (fun signature => decide (named.specialized.declaration = signature.id)) with
  | none => none
  | some signature =>
      let ⟨range⟩ ← range? compiled.sourceProgram.signatures fuel named.specialized.parameterSubstitution
      if ordinaryReturn : named.specialized.function.returnComptime = false then
        if ordinaryParameters : named.specialized.function.typedBody.inputs.all
            (fun binder => !binder.comptime) = true then
          pure ⟨{
            origin := SelectedCompilationCatalog.ordinary_origin compiled signatures
              (RecursiveNamedPreparedFinalPlanOrigins.final_member compiled selected rfl)
              (List.mem_of_find?_eq_some found)
              (by simpa only [decide_eq_true_eq] using (List.find?_some found))
            range := range
            ordinaryReturn := ordinaryReturn
            ordinaryParameters := by
              intro binder member
              have checked := List.all_eq_true.mp ordinaryParameters binder member
              cases same : binder.comptime <;> simp_all }⟩
        else none
      else none

def collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (fuel : Nat) : Table compiled :=
  let rec go (remaining : List (Fin compiled.indexed.base.functions.length)) : Table compiled :=
    match remaining with
    | [] => ⟨[], by intro row member; cases member⟩
    | index :: rest =>
        let named := compiled.indexed.base.functions[index.val]
        have selected : compiled.indexed.base.functions[index.val]? = some named :=
          List.getElem?_eq_getElem index.isLt
        let tail := go rest
        match eligible? compiled signatures fuel named selected with
        | none => tail
        | some ⟨accepted⟩ =>
            { rows := named.specialized :: tail.rows
              admitted := by
                intro row member
                rcases List.mem_cons.mp member with same | member
                · subst row; exact ⟨index.val, named, selected, rfl, accepted⟩
                · exact tail.admitted row member }
  go (List.finRange compiled.indexed.base.functions.length)

/-- Existing accepted programs retain the identical eligible rows. -/
theorem eligible_eq (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) {index : Nat} (named : SourceCoreGeneralFunctions.Function)
    (selected : compiled.indexed.base.functions[index]? = some named) :
    eligible? compiled wellFormed.signatures fuel named selected =
      CallableIndexedOwnedPreparedOrdinarySyntaxTable.eligible? compiled wellFormed fuel named selected := by
  rfl

/-- Signature-only scanning preserves the original table and physical order. -/
theorem collect_eq (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) (fuel : Nat) :
    collect compiled wellFormed.signatures fuel =
      CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel := by
  unfold collect CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect
  generalize List.finRange compiled.indexed.base.functions.length = remaining
  induction remaining with
  | nil => rfl
  | cons first rest ih =>
      simp only [collect.go, CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect.go,
        ih]
      rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinarySyntaxTable
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
/-! Ordinary origins keep their original identity using catalog uniqueness. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
open Frontend SourceInference TypeSystem CallableAncestryMetadata

private theorem rigid_profile (substitution : ParameterSubstitution) (source : TypedSource) :
    requirementProfile (SourceSpecialization.applyTypedSource substitution source) =
      requirementProfile source := by
  simp only [requirementProfile, SourceSpecialization.applyTypedSource, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

private theorem generic_eq_of_erased {program : CheckedProgram}
    {leftSignature rightSignature : ProgramFunctionSignature}
    {leftGeneric rightGeneric : CheckedFunction}
    {leftSupplied rightSupplied : ParameterSubstitution}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (leftMember : leftGeneric ∈ program.functions)
    (rightMember : rightGeneric ∈ program.functions)
    (leftAccepted : SourceSpecialization.specializeFunction
      leftSignature leftGeneric leftSupplied = .ok left)
    (rightAccepted : SourceSpecialization.specializeFunction
      rightSignature rightGeneric rightSupplied = .ok right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using owners
  have owners := congrArg TypedSource.owner erased
  change left.function.typedBody.owner = right.function.typedBody.owner at owners
  rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1] at owners
  change leftGeneric.typedBody.owner = rightGeneric.typedBody.owner at owners
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    ((RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1.symm.trans
      (owners.trans (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1))

/-- The original ordinary function supplies both requirement profiles. Neither
profile equality nor equality of the original templates is assumed. -/
theorem contextual_source_eq_of_erased {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (erased : eraseRequirements (left.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.function.typedBody.applySubstitution rightLocal)) :
    left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, _leftSignatureMember,
    leftMember, _leftResolved, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, _rightSignatureMember,
    rightMember, _rightResolved, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_erased owners leftMember rightMember
    leftAccepted rightAccepted erased
  subst rightGeneric
  apply FiniteProfiles.source_unique erased
  rw [CallableAncestryProfiles.profile_substitute, CallableAncestryProfiles.profile_substitute,
    (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1,
    (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
  change requirementProfile (SourceSpecialization.applyTypedSource
      left.parameterSubstitution leftGeneric.typedBody) =
    requirementProfile (SourceSpecialization.applyTypedSource
      right.parameterSubstitution leftGeneric.typedBody)
  rw [rigid_profile, rigid_profile]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryErasure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity
/-! Ordinary origins keep their original identity using catalog uniqueness. -/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity

open Frontend SourceInference TypeSystem

/-- Source-owner preservation and the genuine ordinary catalog identify the
entire original checker record even when the two full specialization keys differ. -/
theorem generic_eq_of_sources {program : CheckedProgram}
    {leftSignature rightSignature : ProgramFunctionSignature}
    {leftGeneric rightGeneric : CheckedFunction}
    {leftSupplied rightSupplied : ParameterSubstitution}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (leftMember : leftGeneric ∈ program.functions)
    (rightMember : rightGeneric ∈ program.functions)
    (leftAccepted : SourceSpecialization.specializeFunction
      leftSignature leftGeneric leftSupplied = .ok left)
    (rightAccepted : SourceSpecialization.specializeFunction
      rightSignature rightGeneric rightSupplied = .ok right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    leftGeneric = rightGeneric := by
  have unique : (program.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using owners
  have leftOwner : (left.function.typedBody.applySubstitution leftLocal).owner =
      leftGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields leftAccepted).1]
    change leftGeneric.typedBody.owner = leftGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1
  have rightOwner : (right.function.typedBody.applySubstitution rightLocal).owner =
      rightGeneric.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields rightAccepted).1]
    change rightGeneric.typedBody.owner = rightGeneric.declaration
    exact (RecursiveNamedSpecializationBodyFacts.identities rightAccepted).2.1
  exact StructuralSubstitution.eq_of_mem_of_mapped_nodup unique leftMember rightMember
    (leftOwner.symm.trans ((congrArg TypedSource.owner sameSource).trans rightOwner))

/-- The actual ordinary producer witnesses supply membership and both accepted
specializer equations internally. No common-template equation is an input. -/
theorem common_generic_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    ∃ leftSignature rightSignature generic leftSupplied rightSupplied,
      leftSignature ∈ program.signatures.functions ∧
      rightSignature ∈ program.signatures.functions ∧ generic ∈ program.functions ∧
      SourceSpecialization.specializeFunction leftSignature generic leftSupplied = .ok left ∧
      SourceSpecialization.specializeFunction rightSignature generic rightSupplied = .ok right := by
  obtain ⟨leftRequest, leftSignature, leftGeneric, leftSignatureMember,
    leftMember, _, leftAccepted⟩ := leftOrigin
  obtain ⟨rightRequest, rightSignature, rightGeneric, rightSignatureMember,
    rightMember, _, rightAccepted⟩ := rightOrigin
  have same := generic_eq_of_sources owners leftMember rightMember
    leftAccepted rightAccepted sameSource
  subst rightGeneric
  exact ⟨leftSignature, rightSignature, leftGeneric, leftRequest.parameterSubstitution,
    rightRequest.parameterSubstitution, leftSignatureMember, rightSignatureMember,
    leftMember, leftAccepted, rightAccepted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryIdentity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
/-!
Ordinary stage coherence follows from the original body's stored result
annotation. Raw replacement types need no separate formation premise: equal
rigid sources already contain every annotation used by that result.
-/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
open Frontend SourceInference TypeSystem CallableAncestryMetadata

/-- Typing is required only for the original definition at this selected owner. -/
def AtOwner (program : CheckedProgram) (owner : Resolved.DeclarationId) : Prop :=
  ∀ generic, generic ∈ program.functions → generic.declaration = owner →
    FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked generic)

/-- A real cached preparation identifies the unique original checker body. -/
theorem at_prepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row) :
    AtOwner compiled.sourceProgram row.function.typedBody.owner := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, _resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have unique : (compiled.sourceProgram.functions.map (fun function => function.declaration)).Nodup := by
    simpa only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using bodies.function_ids
  have owner : row.function.typedBody.owner = generic.declaration := by
    rw [(CallableCoercionBodyProvenance.specialization_fields accepted).1]
    exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1
  intro candidate member identity
  have same := StructuralSubstitution.eq_of_mem_of_mapped_nodup unique member genericMember
    (identity.trans owner)
  simpa only [same] using valid

private theorem original_body {program : CheckedProgram} {generic : CheckedFunction}
    (valid : FunctionDefinition.Valid program.signatures (FunctionDefinition.ofChecked generic)) :
    ∃ context facts, BodyHasType generic.typedBody context generic.inferredBodyType facts ∧
      facts.type = generic.inferredBodyType := by
  cases valid with
  | intro _ _ typed =>
      cases typed with
      | @intro lexicalContext _ _ _ _ _ resultType _ _ _ _ _ _ _ _ bodyTyped annotation =>
          refine ⟨lexicalContext, _, ?_, annotation.trans resultType.symm⟩
          rw [← resultType] at bodyTyped
          exact bodyTyped

/-- Actual ordinary origins and their equal contextual sources identify the
rigid source, annotated result and original return flag. -/
theorem source_and_result_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.function.typedBody.owner)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.function.declaration = right.function.declaration ∧
      left.function.typedBody = right.function.typedBody ∧
      left.function.inferredBodyType = right.function.inferredBodyType ∧
      left.function.returnComptime = right.function.returnComptime := by
  obtain ⟨leftSignature, rightSignature, generic, leftSupplied, rightSupplied,
    _leftMember, _rightMember, genericMember, leftAccepted, rightAccepted⟩ :=
    SelectedCompilationOrdinaryIdentity.common_generic_of_origins
      owners leftOrigin rightOrigin sameSource
  have leftFields := (CallableCoercionBodyProvenance.specialization_fields leftAccepted).1
  have rightFields := (CallableCoercionBodyProvenance.specialization_fields rightAccepted).1
  have rigidSame : left.function.typedBody = right.function.typedBody := by
    rw [leftFields, rightFields]
    exact CorrelatedTypedSourceInstances.apply_source_eq_of_equal_local_instances
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          leftAccepted parameter replacement found)
      (fun parameter replacement found =>
        SourceSpecializationAcceptance.specializeFunction_parameterReplacement_flexibleClosed
          rightAccepted parameter replacement found)
      generic.typedBody leftLocal rightLocal
      (by simpa only [leftFields, rightFields, SourceSpecialization.applyCheckedFunction] using sameSource)
  obtain ⟨context, facts, typed, annotation⟩ := original_body (bodies generic genericMember (by
    rw [leftFields]
    exact (RecursiveNamedSpecializationBodyFacts.identities leftAccepted).2.1.symm))
  have sameAnnotation := SourceBodyResultAnnotation.parameter_instances_result_eq typed
    left.parameterSubstitution right.parameterSubstitution
    (by simpa only [RecursiveNamedSpecializationBodyFacts.body leftAccepted,
      RecursiveNamedSpecializationBodyFacts.body rightAccepted] using rigidSame)
  have resultSame : left.function.inferredBodyType = right.function.inferredBodyType := by
    rw [RecursiveNamedSpecializationBodyFacts.result leftAccepted,
      RecursiveNamedSpecializationBodyFacts.result rightAccepted]
    simpa only [annotation] using sameAnnotation
  refine ⟨?_, rigidSame, resultSame, ?_⟩
  · rw [leftFields, rightFields]; rfl
  · rw [leftFields, rightFields]; rfl

/-- Both successful analyzers therefore return the same complete analysis. -/
theorem analysis_eq_of_origins {program : CheckedProgram}
    {left right : SourceSpecialization.SpecializedFunction}
    {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.function.typedBody.owner)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right)
    (sameSource : left.function.typedBody.applySubstitution leftLocal =
      right.function.typedBody.applySubstitution rightLocal) :
    left.stageAnalysis = right.stageAnalysis := by
  obtain ⟨declarationEq, sourceEq, resultEq, returnEq⟩ :=
    source_and_result_of_origins owners bodies leftOrigin rightOrigin sameSource
  obtain ⟨_, _, _, _, _, _, leftAccepted⟩ := leftOrigin
  obtain ⟨_, _, _, _, _, _, rightAccepted⟩ := rightOrigin
  exact SourceStageAnalysisCongruence.analysis_eq_of_success declarationEq sourceEq
    (by rw [resultEq, returnEq])
    (RecursiveNamedSpecializationStageFacts.analyzed leftAccepted)
    (RecursiveNamedSpecializationStageFacts.analyzed rightAccepted)

/-- The full ledger frames agree, including when the sources are supplied
only through the actual requirement-erasure boundary. -/
theorem ledger_frame_eq_of_erased {program : CheckedProgram}
    {left right : SourceCoreStageContracts.Sidecar} {leftLocal rightLocal : Substitution}
    (owners : ((Program.ofChecked program).functions.map fun definition => definition.body.owner).Nodup)
    (bodies : AtOwner program left.caller.function.typedBody.owner)
    (samePlan : left.plan = right.plan)
    (leftOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program left.caller)
    (rightOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program right.caller)
    (sameSource : eraseRequirements (left.caller.function.typedBody.applySubstitution leftLocal) =
      eraseRequirements (right.caller.function.typedBody.applySubstitution rightLocal)) :
    CallableLedger.frame left = CallableLedger.frame right := by
  have exactSource :=
    SelectedCompilationOrdinaryErasure.contextual_source_eq_of_erased
      owners leftOrigin rightOrigin sameSource
  obtain ⟨_, _, resultEq, returnEq⟩ :=
    source_and_result_of_origins owners bodies leftOrigin rightOrigin exactSource
  have analysisEq := analysis_eq_of_origins owners bodies leftOrigin rightOrigin exactSource
  have stagesEq : CallStageGuard.frame left.caller = CallStageGuard.frame right.caller := by
    simp only [CallStageGuard.frame, resultEq, returnEq, analysisEq]
  simp only [CallableLedger.frame, stagesEq, samePlan]

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOrdinaryAnnotationCoherence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
/-! Every actual named or anonymous selection at an ordinary Source owner has
its canonical guard frame. Original compiler origins and equal annotated Source
justify frame equality even when specialization keys differ. This identifies
neither the selected sidecar nor the complete invocation scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
open Core Frontend SourceInference
open CallableAncestryMetadata (eraseRequirements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

private theorem sidecar_member {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreStageContracts.prepareSidecar plan owner = .ok sidecar) :
    sidecar.caller ∈ plan.specializations := by
  have found := LambdaSourceAlignment.sidecar_lookup issued
  have filtered := CallableIndexedOwnedContextualDiagnosticSources.selected_filter found
  have member : sidecar.caller ∈ plan.specializations.filter
      (fun row => decide (row.key = owner)) := by
    rw [filtered]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp member).1

/-- The combined registry also has a named selection. Its literal prepared
source supplies the same erasure boundary; an anonymous selection keeps the
existing authenticated ancestry proof. -/
theorem selected_canonical {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    ∃ sidecar active,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan sidecar.caller.key = .ok sidecar ∧
      invocation = RecursiveStageRegistry.scope sidecar active function ∧
      eraseRequirements function.source =
        eraseRequirements (sidecar.source.applySubstitution active) := by
  cases selected with
  | anonymous receipt =>
      exact CallableSelectedCanonicalSourceErasure.selected_canonical receipt
  | named prepared sidecar issued same =>
      have sourceEq : prepared.view.source = sidecar.source := by
        change prepared.named.specialized.function.typedBody = sidecar.caller.function.typedBody
        rw [prepared.same, same]
      exact ⟨sidecar, [], by simpa only [same] using issued, rfl,
        by simpa using congrArg eraseRequirements sourceEq⟩
  | method selection statements sidecar issued same =>
      have sourceEq := congrArg (fun row : SourceSpecialization.SpecializedFunction => row.function.typedBody) same
      change sidecar.source = _ at sourceEq
      exact ⟨sidecar, [], by simpa only [same] using issued, rfl,
        by simpa [Staging.Recursive.methodView, Staging.Recursive.globalView, CallableCoercionMethodInstantiation.bodyInstance] using congrArg eraseRequirements sourceEq.symm⟩

theorem selected_frame {function : Dynamic.Closure}
    {invocation : Staging.Recursive.Scope}
    {canonical : SourceCoreStageContracts.Sidecar} {owner : SourceCompilationPlan.Key}
    {active : TypeSystem.Substitution} {signature : ProgramFunctionSignature}
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map
      fun definition => definition.body.owner).Nodup)
    (atOwner : SelectedCompilationOrdinaryAnnotationCoherence.AtOwner
      compiled.sourceProgram function.source.owner)
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan owner = .ok canonical)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      owner active function.source)
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation) :
    invocation.guards = CallableLedger.frame canonical := by
  obtain ⟨sidecar, selectedActive, issued, scopeEq, erased⟩ :=
    selected_canonical stagePrepared selected
  have canonicalSourceEq := canonicalSource.source canonicalIssued
  have selectedOwner : sidecar.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner erased
    change function.source.owner = sidecar.caller.function.typedBody.owner at same
    exact same.symm.trans sourceOwner
  have canonicalOwner : canonical.caller.function.typedBody.owner = signature.id := by
    have same := congrArg TypedSource.owner canonicalSourceEq
    exact same.symm.trans sourceOwner
  have selectedOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted signatures signatureMember _ (sidecar_member issued) selectedOwner
  have canonicalOrigin := CallableOrdinaryMethodCatalogSeparation.of_preparation_at_ordinary_owner
    accepted signatures signatureMember _ (sidecar_member canonicalIssued) canonicalOwner
  have samePlan : sidecar.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted issued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  rw [scopeEq]
  exact SelectedCompilationOrdinaryAnnotationCoherence.ledger_frame_eq_of_erased
    owners (by
      intro generic member identity
      exact atOwner generic member (identity.trans (selectedOwner.trans sourceOwner.symm)))
    samePlan selectedOrigin canonicalOrigin
    (erased.symm.trans (congrArg eraseRequirements canonicalSourceEq))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationScopeCoherence
end
