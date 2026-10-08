import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.EmittedMatchCatalogCoupledExtraction

/-! Prepared Catalog endpoints construct their structural eliminator from the
actual joint Tree/Plan receipt and its own tokens. Match catalog and context
provenance is supplied at the actual selected compiler receipt. Initializer
and post-header payloads keep their exact emitted code and tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
open RecursiveNamedHeaderContracts (AtMost)
open RecursiveNamedBoundedContracts (Below)
open TypedImperativeFor (Position)
section preservesCoupled

universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerSites : InitializerSites initializerFacts loopFacts source)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)
  (assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts source)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (transfers : AllocationTransfers protocol readiness stateBindings source)
  (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
  (assignments : ∀ context, validity context → Assignment.AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative budget)
  (assignmentFaults : ∀ context, validity context → Assignment.AssignmentFaultPreservesAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative faults budget)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (meaningMost : ∀ context, validity context →
  AtMost budget (fun size => ExpressionPreservesAt protocol readiness program evidence
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
    (context := context) (source := source) (faults := faults) size))
variable {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}

local notation "PreparedAP" => (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
local notation "PreparedUP" => (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)
local notation "PreparedHP" => (fun postTree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := invalidProjection) (missingDefault := missingDefault)
  (invalidUnary := fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) postTree)
local notation "PreparedMP" => (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)
local notation "PreparedR" => ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
  (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
  (administrative := administrative) PreparedAP PreparedUP

include definitions registered stateTransport stateBindings producer acquire meaningMost observations extend sites transfers assignmentSites initializerSites snapshots assignments in
theorem preservesAt_match_coupled
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (matchSupplier : GenericImperativeMatch.Structural.MatchSupplier (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values)
      (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context))
    (assignmentFaultsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => PreparedAP head))
    (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : PreservingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR))
    (loopFor : ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR) PreparedHP)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericImperativeMatch.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) plan) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget PreparedR
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact preservesAt_match_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (assignments := assignments) (meaningMost := meaningMost)
    PreparedAP PreparedUP PreparedHP PreparedMP PreparedR
    (ProtectedStateImperativeCatalogPayload.structural_header_algebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) PreparedAP PreparedUP)
    (fun receipt => receipt.errors unaryTyped issued unaryIncluded)
    (fun _ _ fields => ⟨catalog, fields⟩)
    assignmentFaultsWithPayload unique headFor loopFor
    (GenericImperativeMatch.Structural.of_coupled PreparedMP matchSupplier coupled tokens)

include definitions registered stateTransport stateBindings producer acquire meaningMost observations extend sites transfers assignmentSites initializerSites snapshots assignments in
theorem preservesAt_match_catalog_coupled
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (assignmentFaultsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => PreparedAP head))
    (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : PreservingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR))
    (loopFor : ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR) PreparedHP)
    (receipt : GenericImperativeMatch.CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
      factory (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) invalidProjection missingDefault
      expressionSyntax certificates ambient.definitions administrative solved context scope position expected type code)
    (ledger : context.solvedRequirements = solved) :
    ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget PreparedR
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact preservesAt_match_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (assignments := assignments) (meaningMost := meaningMost)
    PreparedAP PreparedUP PreparedHP PreparedMP PreparedR
    (ProtectedStateImperativeCatalogPayload.structural_header_algebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) PreparedAP PreparedUP)
    (fun receipt => receipt.errors unaryTyped issued unaryIncluded)
    (fun _ _ fields => ⟨catalog, fields⟩)
    assignmentFaultsWithPayload unique headFor loopFor
    (receipt.eliminate ledger)

end preservesCoupled

section reflectsCoupled

universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerSites : InitializerSites initializerFacts loopFacts source)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)
  (assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts source)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (transfers : AllocationTransfers protocol readiness stateBindings source)
  (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
  (assignments : ∀ context, validity context → Assignment.AssignmentReflectsAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative faults budget)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (reflection : ∀ context, validity context →
  Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
    (context := context) (source := source) (faults := faults) size))
variable {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {factory : AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}

local notation "PreparedAP" => (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
local notation "PreparedUP" => (fun head => GenericForHeader.Structural.PreparedUnary true source (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) head)
local notation "PreparedHP" => (fun postTree => GenericImperativeMatch.Structural.PreparedHeader (factory := factory)
  (invalidProjection := invalidProjection) (missingDefault := missingDefault)
  (invalidUnary := fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) postTree)
local notation "PreparedMP" => (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context)
local notation "PreparedR" => ProtectedStateImperativeCatalogPayload.StructuralHeaderReceipt
  (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
  (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
  (administrative := administrative) PreparedAP PreparedUP

include definitions registered stateTransport stateBindings producer acquire reflection observations extend sites transfers assignmentSites initializerSites snapshots in
theorem reflectsAt_match_coupled
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (matchSupplier : GenericImperativeMatch.Structural.MatchSupplier (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values)
      (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (fun compilation context => GenericImperativeMatch.Tree.MatchContextFields compilation context))
    (assignmentsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => PreparedAP head))
    (_unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : ReflectingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR))
    (loopFor : ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR) PreparedHP)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code) {plan : EmittedDiagnosticPlan.Plan factory}
    (coupled : GenericImperativeMatch.Coupled factory invalidProjection missingDefault tree plan)
    (tokens : EmittedDiagnosticTokenPlan.TokensFor factory (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) plan) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget PreparedR
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact reflectsAt_match_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (reflection := reflection)
    PreparedAP PreparedUP PreparedHP PreparedMP PreparedR
    (ProtectedStateImperativeCatalogPayload.structural_header_algebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) PreparedAP PreparedUP)
    (fun receipt => receipt.errors unaryTyped issued unaryIncluded)
    (fun _ _ fields => ⟨catalog, fields⟩)
    assignmentsWithPayload _unique headFor loopFor
    (GenericImperativeMatch.Structural.of_coupled PreparedMP matchSupplier coupled tokens)

include definitions registered stateTransport stateBindings producer acquire reflection observations extend sites transfers assignmentSites initializerSites snapshots in
theorem reflectsAt_match_catalog_coupled
    (unaryTyped : EmittedDiagnosticTokenPlan.UnaryTyped source)
    (issued : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep table reason token → faults reason token)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (assignmentsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => PreparedAP head))
    (_unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : ReflectingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR))
    (loopFor : ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget PreparedR) PreparedHP)
    (receipt : GenericImperativeMatch.CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
      factory (fun site root => table.reasonAt site root SourceCoreAssignmentFaultSites.Kind.bitNot) invalidProjection missingDefault
      expressionSyntax certificates ambient.definitions administrative solved context scope position expected type code)
    (ledger : context.solvedRequirements = solved) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget PreparedR
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact reflectsAt_match_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (reflection := reflection)
    PreparedAP PreparedUP PreparedHP PreparedMP PreparedR
    (ProtectedStateImperativeCatalogPayload.structural_header_algebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions)
      (administrative := administrative) PreparedAP PreparedUP)
    (fun receipt => receipt.errors unaryTyped issued unaryIncluded)
    (fun _ _ fields => ⟨catalog, fields⟩)
    assignmentsWithPayload _unique headFor loopFor
    (receipt.eliminate ledger)

end reflectsCoupled

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady
