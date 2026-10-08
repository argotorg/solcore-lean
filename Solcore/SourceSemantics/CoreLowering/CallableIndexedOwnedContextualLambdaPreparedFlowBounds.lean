import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaAssignmentReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogProducers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaBodyContinuations

/-! Genuine Source sites and the actual prepared eliminator supply all finite
head and loop operations internally. The only runtime children are strict
members of the same admitted expression family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateTransition ProtectedStateImperativeCatalogReady
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {owner : SourceSpecialization.SpecializationKey}
  (issued : IssuedSource compiled owner source)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {protocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ambient : AmbientDefinitions compiled.compatible.checked.catalog.definitions}
  (functions : FunctionModel compiled.compatible.checked.catalog ambient)
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (evidence : Dynamic.EvidenceEnvironment)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (condition : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer protocol compiled.indexed.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (transport : AdministrativeTransport protocol) (bindings : Bindings protocol)
  (unique : NodeOccurrencesUnique source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {solved : List SolvedRequirement} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source issued.invalidOperand}
  {table : SourceCoreFaultSites.Table}
  (rebuilt : issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep issued.assignments reason token → faults reason token)

/-- The lambda's complete ledger travels with independent Source validity. -/
def Validity (context : SourceSemantics.Context) : Prop :=
  CompatibleRuntimeContextValidity.Valid solved context evidence ∧
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source

theorem validity_extend {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : Validity (compiled := compiled) (source := source) (solved := solved) evidence context)
    (extended : BinderExtends source.owner context binder next) :
    Validity (compiled := compiled) (source := source) (solved := solved) evidence next :=
  ⟨valid.1.extend extended, valid.2.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)⟩

theorem signatures {context : SourceSemantics.Context}
    (valid : Validity (compiled := compiled) (source := source) (solved := solved) evidence context) :
    context.signatures = compiled.compatible.checked.signatures :=
  valid.2.signatures.trans (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm

include unique in
private theorem assignment_sites : AssignmentSites
    (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (SourceAssignmentHasType source) (SourceBitNotAssignmentValid source) source where
  assignment := by
    intro context id expected node resolution operator rhs facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.assignment unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form
  snapshot := by
    intro context id expected node resolution facts found form
    obtain ⟨mode, rest, _syntax, typed⟩ := facts
    exact ProtectedStateImperativeTypedSourceSites.bit_not unique
      (ProtectedStateImperativeTypedSourceSites.head typed) found form


variable (interprets : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
  CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
    (context := context) (certificates := certificates) (administrative := administrative)
    (factory := factory) (faults := faults) (registry := registry) issued bridge functions table)

include definitions registered extension faithful observations producer acquire transport bindings wellFormed unique rebuilt operandIncluded unaryIncluded interprets in
theorem preserves_flow (budget : Nat) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (meaning : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedHeaderContracts.AtMost budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size))
    (eliminator : GenericImperativeMatch.Structural.Eliminates
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) context scope position expected type flow) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
      functions (Program.ofChecked compiled.sourceProgram) evidence (Validity (compiled := compiled) (source := source) (solved := solved) evidence) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      context scope position expected type flow := by
  have below : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size) :=
    fun context valid child smaller => meaning context valid child (Nat.le_of_lt smaller)
  let assignments : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt protocol (readiness bridge)
        (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (ambient := ambient) functions (registry := registry) (Program.ofChecked compiled.sourceProgram)
        evidence source (certificates context) context administrative faults budget ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) := by
    intro context valid
    exact CallableIndexedOwnedContextualLambdaAssignmentReadiness.assignment_fault
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (registry := registry) (faults := faults)
      issued bridge functions extension evidence transport faithful observations unique wellFormed
      rebuilt (interprets context valid) operandIncluded (signatures evidence valid)
      valid.2 valid.1.covers budget (below context valid)
  exact RecursiveNamedImperativeFor.Stateful.WithReady.preservesAt_match_with_eliminator
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
    (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
    (administrative := administrative) (functions := functions)
    (definitions := definitions) (registered := registered) (program := Program.ofChecked compiled.sourceProgram)
    (evidence := evidence) (protocol := protocol) (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
    (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := (Validity (compiled := compiled) (source := source) (solved := solved) evidence)) (extend := fun valid extended => validity_extend evidence valid extended)
    (budget := budget)
    (sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram) evidence runtime.graph)
    (assignmentSites := assignment_sites unique)
    (initializerSites := ProtectedStateImperativeInitializerSourceSites.sites)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed (Validity (compiled := compiled) (source := source) (solved := solved) evidence)
      (fun _ valid => valid.2) (fun _ valid => valid.1.covers))
    (observations := observations)
    (assignments := fun context valid => CallableIndexedOwnedAdmittedForHeaderReadiness.assignment_prefix
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (certificate := certificates context) (administrative := administrative) (faults := faults)
      bridge functions extension evidence transport faithful observations unique wellFormed
      valid.2 valid.1.covers budget (below context valid))
    (meaningMost := fun context valid child within => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning context valid child within))
    ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head))) (ProtectedStateImperativeCatalogPayload.structural_header_algebra ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
    (fun {context scope assignment} {head} receipt => GenericForHeader.Structural.PreparedUnary.errors receipt issued.typing.1 issued.assignmentsPrepared unaryIncluded)
    (fun _ _ fields => ⟨CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed, fields⟩)
    assignments unique
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence faithful observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy (fun _ valid => valid.1) issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.preserving_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence faithful observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    eliminator

include definitions registered extension faithful observations producer acquire transport bindings wellFormed unique rebuilt operandIncluded unaryIncluded interprets in
theorem reflects_flow (budget : Nat) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {flow : Expr}
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (functionTypes : FunctionRuntimeViews functions)
    (meaning : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context → RecursiveNamedBoundedContracts.Below budget
      (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        context evidence source (certificates context) faults size))
    (eliminator : GenericImperativeMatch.Structural.Eliminates
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) context scope position expected type flow) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol (readiness bridge) condition
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
      functions (Program.ofChecked compiled.sourceProgram) evidence (Validity (compiled := compiled) (source := source) (solved := solved) evidence) budget (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      context scope position expected type flow := by
  have below := meaning
  let assignments : ∀ context, (Validity (compiled := compiled) (source := source) (solved := solved) evidence) context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt protocol (readiness bridge)
        (SourceAssignmentHasType source) (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        (ambient := ambient) functions (registry := registry) (Program.ofChecked compiled.sourceProgram)
        evidence source (certificates context) context administrative faults budget ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) := by
    intro context valid
    exact CallableIndexedOwnedContextualLambdaAssignmentReadiness.assignment_reflection
      (context := context) (certificates := certificates) (administrative := administrative)
      (factory := factory) (registry := registry) (faults := faults)
      issued bridge functions extension evidence transport faithful observations unique wellFormed
      rebuilt (interprets context valid) operandIncluded (signatures evidence valid)
      valid.2 valid.1.covers budget functionTypes (below context valid)
  exact RecursiveNamedImperativeFor.Stateful.WithReady.reflectsAt_match_with_eliminator
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
    (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
    (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
    (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates)
    (administrative := administrative) (functions := functions)
    (definitions := definitions) (registered := registered) (program := Program.ofChecked compiled.sourceProgram)
    (evidence := evidence) (protocol := protocol) (readiness := readiness bridge) (conditionGate := condition)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (headFacts := ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (loopFacts := CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
    (initializerFacts := ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
    (assignmentFacts := SourceAssignmentHasType source) (snapshotFacts := SourceBitNotAssignmentValid source)
    (producer := producer) (stateTransport := transport) (stateBindings := bindings) (acquire := acquire)
    (validity := (Validity (compiled := compiled) (source := source) (solved := solved) evidence)) (extend := fun valid extended => validity_extend evidence valid extended)
    (budget := budget)
    (sites := ProtectedStateImperativeTypedSourceSites.sites (Program.ofChecked compiled.sourceProgram) evidence runtime.graph)
    (assignmentSites := assignment_sites unique)
    (initializerSites := ProtectedStateImperativeInitializerSourceSites.sites)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    (snapshots := CallableIndexedOwnedAdmittedForHeaderReadiness.snapshot_transfers bridge evidence wellFormed (Validity (compiled := compiled) (source := source) (solved := solved) evidence)
      (fun _ valid => valid.2) (fun _ valid => valid.1.covers))
    (observations := observations)
    (reflection := fun context valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning context valid child smaller))
    ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)) ((fun tree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault) (invalidUnary := issued.invalidUnary) tree)) ((fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)) (ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
  (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source := source)
  (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head))) (ProtectedStateImperativeCatalogPayload.structural_header_algebra ((fun head => GenericForHeader.Structural.PreparedAssignment factory issued.invalidProjection issued.missingDefault head)) ((fun head => GenericForHeader.Structural.PreparedUnary true source issued.invalidUnary head)))
    (fun {context scope assignment} {head} receipt => GenericForHeader.Structural.PreparedUnary.errors receipt issued.typing.1 issued.assignmentsPrepared unaryIncluded)
    (fun _ _ fields => ⟨CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed, fields⟩)
    assignments unique
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_heads
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered extension evidence observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy (fun _ valid => valid.1) issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    (CallableIndexedOwnedPreparedCatalogProducers.reflecting_loops
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := ambient)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (factory := factory) (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      (layouts := compiled.indexed.layouts) (owner := owner) (active := active)
      (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length) (onError := onError)
      (registry := registry) (faults := faults)
      bridge functions definitions registered evidence observations condition producer acquire transport bindings unique wellFormed
      (Validity (compiled := compiled) (source := source) (solved := solved) evidence) (fun _ valid => valid.2) (fun _ valid => valid.1.covers)
      (fun valid extended => validity_extend evidence valid extended)
      budget diagnosticPolicy issued.typing.1 issued.assignmentsPrepared unaryIncluded below assignments)
    eliminator

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedFlowBounds
