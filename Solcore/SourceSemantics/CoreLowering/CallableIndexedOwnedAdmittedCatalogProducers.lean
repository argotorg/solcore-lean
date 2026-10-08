import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPostReceiptOperations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForHeaderBounds

/-! Authentic finite catalog recipes consume only their actual smaller child
results. Source facts identify visited contexts; the existing loop and post
producers keep the exact reached pools and independent Source/native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open TypedLexicalWhile (Scope ValuesContext)
open ProtectedStateImperativeCatalogReady
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open CallableIndexedOwnedAdmittedLexicalReadiness (readiness)
theorem match_child_syntax {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context childContext : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode} {expected : TypeSystem.Ty}
    {request : GenericMatchChildren.Request} {hiddenIds : List Resolved.LocalId}
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (related : GenericMatchChildren.ScopedContextFor source context hiddenIds scrutinee.type
      resolution.cases resolution.defaultBody request childContext) :
    GenericImperativeMatch.Syntax source expressionSyntax childContext (.statements false request.statements) expected := by
  obtain ⟨mode, rest, syntaxTree, _typed⟩ := facts
  cases syntaxTree
  case matchWith _found _form _sourceType _scrutineeFound _scrutineeTyped _scrutineeSyntax _casesTyped _defaultTyped _hiddenOrdinary _armsOrdinary children _remaining =>
    simp_all
    apply_assumption
    exact related.forget
  case terminalMatch _unique _found _form _sourceType _scrutineeFound _scrutineeTyped _scrutineeSyntax _casesTyped _defaultTyped _hiddenOrdinary _armsOrdinary children _stops =>
    simp_all
    apply_assumption
    exact related.forget
  case body syntaxTree => cases syntaxTree <;> simp_all
  all_goals simp_all

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : AdministrativeTransport callerProtocol) (stateBindings : Bindings callerProtocol)
  (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
  (validity : SourceSemantics.Context → Prop)
  (runtime : ∀ context, validity context → Dynamic.SourceRuntimeValid program context source)
  (covers : ∀ context, validity context → evidence.Covers context)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
  {solved : List SolvedRequirement}
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)

abbrev PreservingGoal := RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity) (certificates := certificates) (diagnosticPolicy := diagnosticPolicy)
  functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
  (frame := frame) (globals := globals) (onError := onError) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

abbrev ReflectingGoal := RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity) (certificates := certificates) (diagnosticPolicy := diagnosticPolicy)
  functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
  (frame := frame) (globals := globals) (onError := onError) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

open ProtectedStateImperativeCatalogPayload (HeaderReceiptFamily)

abbrev PreservingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.PreservesAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

abbrev ReflectingGoalWithReceipt (R : HeaderReceiptFamily) := ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt
  callerProtocol (readiness bridge) guard
  (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
  (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
  (ProtectedStateImperativeInitializerSourceSites.Facts source expressionSyntax)
  (validity := validity)
  functions program evidence budget R
  (frame := frame) (globals := globals) (source := source)
  (administrative := administrative) (registry := registry) (faults := faults)

include stateTransport unique in
theorem preserving_loops_with_receipts
    (R : HeaderReceiptFamily)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (postSuccess : CallableIndexedOwnedPostReceiptOperations.PrefixAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) bridge functions evidence guard validity budget HP)
    (postFault : CallableIndexedOwnedPostReceiptOperations.FaultAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget HP)
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ProtectedStateImperativeCatalogPayload.PreservingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      HP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    obtain ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩ := loopFacts
    have packet : CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax context condition post statements expected :=
      ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩
    intro size bounded valid
    refine (CallableIndexedOwnedAdmittedForBounds.loop_preserves_bounded_for bridge guard functions evidence stateTransport validity budget
      (meaning context valid) packet conditionFound conditionTree typed unique
      (fun size smaller => child size (Nat.le_of_lt smaller)) ?_ ?_) size bounded valid
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before after store finalContext finalEnvironment state native read guarded ready continued trace
      exact postSuccess postTree postErrors valid postTyped agrees reference
        state read guarded ready continued trace (Nat.le_of_lt smaller)
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before after store finalContext reason state native read guarded ready continued trace
      exact postFault postTree postErrors
        valid postTyped agrees reference state read guarded ready continued trace (Nat.le_of_lt smaller)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem preserving_loops
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingLoops callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      diagnosticPolicy (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    exact preserving_loops_with_receipts (stateTransport := stateTransport) (unique := unique) bridge functions evidence guard validity budget
      (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree)
      (CallableIndexedOwnedPostReceiptOperations.prefixat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_PrefixAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning))
      (CallableIndexedOwnedPostReceiptOperations.faultat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_FaultAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning))
      meaning
      (.mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child) loopFacts

include stateTransport unique in
theorem reflecting_loops_with_receipts
    (R : HeaderReceiptFamily)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative))
    (postReflection : CallableIndexedOwnedPostReceiptOperations.ReflectsAt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget HP)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      HP (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    obtain ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩ := loopFacts
    have packet : CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax context condition post statements expected :=
      ⟨control, bodyFinal, bodyFacts, postFinal, conditionTyped, bodySyntax, bodyTyped, postTyped, postSyntax⟩
    intro size bounded valid
    refine (CallableIndexedOwnedAdmittedForBounds.loop_reflects_bounded_from_tree_for bridge guard functions evidence stateTransport validity budget
      (reflection context valid) packet conditionFound conditionTree typed unique child ?_ bodyTree) size bounded valid
    · intro actualContext environment canonical actual ξ contextLocation location agrees reference valid size smaller
      intro mapping world before store finalStore value state native read guarded ready continued evaluated
      exact postReflection postTree postErrors
        valid postTyped agrees reference state read guarded ready continued evaluated (Nat.le_of_lt smaller)

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend in
theorem reflecting_loops (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingLoops callerProtocol (readiness bridge) guard
      (CallableIndexedOwnedAdmittedForBounds.LoopFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      diagnosticPolicy (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope condition post statements expected type code recipe loopFacts
  cases recipe with
  | mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child =>
    exact reflecting_loops_with_receipts (stateTransport := stateTransport) (unique := unique) bridge functions evidence guard validity budget
      (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults) (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree)
      (CallableIndexedOwnedPostReceiptOperations.reflectsat_of_header_receipt (source := source) (certificates := certificates) (administrative := administrative) (faults := faults)
        bridge functions evidence guard validity budget (fun tree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree) (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
        (fun tree errors => ⟨tree, errors⟩)
        (CallableIndexedOwnedHeaderReceiptOperations.legacy_ReflectsAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy functionTypes reflection))
      reflection
      (.mk conditionFound conditionType conditionTree bodyTree postTree postErrors typed child) loopFacts

include definitions registered extension producer acquire stateTransport stateBindings unique extend runtimeOf in
theorem preserving_heads_with_receipts
    (R : HeaderReceiptFamily)
    (headerPrefix : CallableIndexedOwnedHeaderReceiptOperations.PrefixAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) bridge functions evidence guard validity budget R)
    (headerFault : CallableIndexedOwnedHeaderReceiptOperations.FaultAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope id expected type code recipe
  cases recipe with
  | whileLoop found form conditionFound conditionType conditionTree bodyTree typed child =>
    intro size bounded valid
    exact (CallableIndexedOwnedAdmittedWhileBounds.preserves_bounded_for bridge guard functions evidence stateTransport validity budget
      (meaning context valid) found form conditionFound conditionTree typed unique
      (fun childSize less => child childSize (Nat.le_of_lt less))) size bounded valid
  | forLoop found form child =>
    exact CallableIndexedOwnedAdmittedForHeadBounds.header_preserves_with_receipt
      (unique := unique) bridge functions evidence guard validity budget R headerPrefix headerFault found form child
  | @matchWith node resolution scrutineeNode _expected _type _code selfReason originalControl caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalog patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded valid parentFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
      environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
    have parentTyped : ProtectedStateImperativeTypedSourceSites.Head source context id := by
      obtain ⟨mode, rest, _syntax, typed⟩ := parentFacts
      exact ProtectedStateImperativeTypedSourceSites.head typed
    obtain ⟨lowered, certified, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
    refine CallableIndexedOwnedAdmittedMatchBounds.preserves_bounded_for (expected := expected) (faults := faults) (administrative := administrative)
      bridge onError allocator functions definitions registered extension evidence restricted
      (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique validity
      (CompatibleMatchRuntimeSelection.LiteralRows _) patternContext.signatures
      (fun numeric selected => ?_) (CompatibleMatchRuntimeSelection.of_certificate restricted)
      (fun extended valid => RecursiveNamedImperativeFor.ContextTransport.binders validity extend valid extended)
      catalog found form scrutineeFound (fun _ singleton => singleton.2.2) guard producer stateBindings acquire
      budget size bounded ?_ ?_ ?_ valid
      parentTyped environments heaps locals agrees actualTyped reference read unmapped initial guarded ready trace
    · obtain ⟨implementation, selected⟩ := selected
      exact selected.proves patternContext.ledger (runtimeOf context valid).runtime
    · intro valid childSize less actualScope actualId actualCode singleton node found sourceTyped mapping world administrativeContext inputEnvironment canonical actual actualContext before store ξ outcome after operandEnvs heaps locals agrees typed state admission trace
      rcases singleton with ⟨rfl, rfl, rfl⟩
      exact meaning context valid childSize less certified found sourceTyped (mapping := mapping) (world := world) (administrativeContext := administrativeContext) (environment := inputEnvironment) (canonical := canonical) (actual := actual) (actualContext := actualContext) (before := before) (store := store) (ξ := ξ) operandEnvs heaps locals agrees typed state admission trace
    · intro control sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        armContext staticFinal facts extended bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before after store ξ contextLocation native outcome finalContext
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := GenericMatchChildren.selected_arm_ids bodySelected
      rw [sameScope] at scopeIds
      cases bodySelected with
      | arm binders allocated certified =>
        have selectedContext := GenericMatchChildren.ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended
        exact child ⟨_, statements, body⟩ certified armContext selectedContext childSize (Nat.le_of_lt less) valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace
    · intro control sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        staticFinal facts bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before after store ξ contextLocation native outcome finalContext
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := (GenericMatchChildren.selected_default_ids bodySelected).trans sameScope
      cases bodySelected with
      | default certified =>
        have selectedContext : GenericMatchChildren.ScopedContextFor source context
            (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody ⟨_, statements, body⟩ context :=
          .default selected.defaultBody_eq scopeIds
        exact child ⟨_, statements, body⟩ certified context selectedContext childSize (Nat.le_of_lt less) valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend runtimeOf in
theorem preserving_heads
    (meaning : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    PreservingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (PreservingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact preserving_heads_with_receipts bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_PrefixAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_FaultAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy meaning)
    meaning

include definitions registered extension producer acquire stateTransport stateBindings unique extend runtimeOf in
theorem reflecting_heads_with_receipts
    (R : HeaderReceiptFamily)
    (headerReflection : CallableIndexedOwnedHeaderReceiptOperations.ReflectsAt (source := source) (frame := frame) (globals := globals) (administrative := administrative) (registry := registry) (faults := faults) bridge functions evidence guard validity budget R)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoalWithReceipt bridge functions evidence guard validity budget R (frame := frame) (globals := globals) (source := source) (expressionSyntax := expressionSyntax) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  intro context scope id expected type code recipe
  cases recipe with
  | whileLoop found form conditionFound conditionType conditionTree bodyTree typed child =>
    intro size bounded valid
    exact (CallableIndexedOwnedAdmittedWhileBounds.reflects_bounded_from_tree_for bridge guard functions evidence stateTransport validity budget
      (reflection context valid) found form conditionFound conditionTree typed unique
      (fun childSize less => child childSize less) bodyTree) size (Nat.le_of_lt bounded) valid
  | forLoop found form child =>
    exact CallableIndexedOwnedAdmittedForHeadBounds.header_reflects_with_receipt
      (unique := unique) bridge functions evidence guard validity budget R headerReflection found form child
  | @matchWith node resolution scrutineeNode _expected _type _code selfReason originalControl caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalog patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro size bounded valid parentFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
      environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
    have parentTyped : ProtectedStateImperativeTypedSourceSites.Head source context id := by
      obtain ⟨mode, rest, _syntax, typed⟩ := parentFacts
      exact ProtectedStateImperativeTypedSourceSites.head typed
    obtain ⟨lowered, certified, restricted⟩ := GenericImperativeMatch.Certificate.singleton receipt
    refine CallableIndexedOwnedAdmittedMatchBounds.reflects_bounded_for (expected := expected) (faults := faults) (administrative := administrative)
      bridge onError allocator functions definitions registered extension evidence restricted
      (show CompatibleMatchSelectionPrefix.Ordinary restricted from ordinary) unique validity
      (CompatibleMatchRuntimeSelection.LiteralRows _) patternContext.signatures
      (fun numeric selected => ?_) (CompatibleMatchRuntimeSelection.of_certificate restricted)
      (fun extended valid => RecursiveNamedImperativeFor.ContextTransport.binders validity extend valid extended)
      catalog found form scrutineeFound (fun _ singleton => singleton.2.2) guard producer stateBindings acquire
      budget size (Nat.le_of_lt bounded) ?_ ?_ ?_ valid
      parentTyped environments heaps locals agrees actualTyped reference read unmapped initial guarded ready evaluated
    · obtain ⟨implementation, selected⟩ := selected
      exact selected.proves patternContext.ledger (runtimeOf context valid).runtime
    · intro valid childSize less actualScope actualId actualCode singleton node found sourceTyped mapping world administrativeContext inputEnvironment canonical actual actualContext before store ξ value finalStore operandEnvs heaps locals agrees typed state admission trace
      rcases singleton with ⟨rfl, rfl, rfl⟩
      exact reflection context valid childSize less certified found sourceTyped (mapping := mapping) (world := world) (administrativeContext := administrativeContext) (environment := inputEnvironment) (canonical := canonical) (actual := actual) (actualContext := actualContext) (before := before) (store := store) (ξ := ξ) operandEnvs heaps locals agrees typed state admission trace
    · intro control sourceValue hiddenScope environment heap statements bindings finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        armContext staticFinal facts extended bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := GenericMatchChildren.selected_arm_ids bodySelected
      rw [sameScope] at scopeIds
      cases bodySelected with
      | arm binders allocated certified =>
        have selectedContext := GenericMatchChildren.ScopedContextFor.selected_arm_at ⟨_, statements, body⟩ rfl scopeIds casesTyped selected extended
        exact child ⟨_, statements, body⟩ certified armContext selectedContext childSize less valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace
    · intro control sourceValue hiddenScope environment heap statements finalScope finalEnvironment finalHeap body sameScope selected bodySelected
        staticFinal facts bodyTyped childSize less valid _static
      intro mapping world actualContext inputEnvironment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees typed reference read unmapped state gated ready trace
      have scopeIds := (GenericMatchChildren.selected_default_ids bodySelected).trans sameScope
      cases bodySelected with
      | default certified =>
        have selectedContext : GenericMatchChildren.ScopedContextFor source context
            (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody ⟨_, statements, body⟩ context :=
          .default selected.defaultBody_eq scopeIds
        exact child ⟨_, statements, body⟩ certified context selectedContext childSize less valid
          ⟨match_child_syntax parentFacts found form scrutineeFound selectedContext, ⟨control, staticFinal, facts, bodyTyped⟩⟩ environments heaps locals agrees typed reference read unmapped state gated ready trace

include definitions registered extension faithful observations producer acquire stateTransport stateBindings unique wellFormed runtime covers extend runtimeOf in
theorem reflecting_heads (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, validity context → Below budget (fun size =>
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (certificates context) faults size)) :
    ReflectingHeads callerProtocol (readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      functions program evidence validity budget
      (ReflectingGoal bridge functions evidence guard validity budget diagnosticPolicy (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative) (registry := registry) (faults := faults))
      (administrative := administrative) (layouts := layouts) (owner := owner)
      (active := active) (frame := frame) (globals := globals) (onError := onError)
      (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults) := by
  exact reflecting_heads_with_receipts bridge functions definitions registered extension evidence guard producer acquire stateTransport stateBindings unique validity extend budget runtimeOf
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (CallableIndexedOwnedHeaderReceiptOperations.legacy_ReflectsAt bridge functions definitions registered extension evidence faithful observations guard producer.toOrdinary acquire stateTransport stateBindings unique wellFormed validity runtime covers extend budget diagnosticPolicy functionTypes reflection)
    reflection

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCatalogProducers
