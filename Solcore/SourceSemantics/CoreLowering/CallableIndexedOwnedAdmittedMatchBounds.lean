import Solcore.SourceSemantics.CoreLowering.CompatibleMatchPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchReadiness

/-! Original Source match typing supplies the scrutinee and selected bodies.
Admitted children run at the exact states from the shared match proofs, including
the combined marked prefix and the actual body post restored to its caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates

/-- Raw Source typing is normalized only through its actual stored node. The
native projection and marker binder type do not determine these judgments. -/
theorem sites {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typed : ProtectedStateImperativeTypedSourceSites.Head source context id)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee) :
    ∃ control caseFacts,
      ProtectedStateLexicalSourceSites.ExpressionFacts source context resolution.scrutinee scrutinee ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      ∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts := by
  obtain ⟨control, rawType, caseFacts, expressionTyped, casesTyped, defaultTyped⟩ :=
    CallableIndexedOwnedMatchAdmission.typing_of_head unique typed found form
  obtain ⟨original, contains, sameType⟩ := expressionTyped.stored_type
  have sameNode : original = scrutinee :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans scrutineeFound)
  subst original
  exact ⟨control, caseFacts,
    by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using expressionTyped,
    by simpa only [sameType] using casesTyped,
    defaultTyped⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {compilation : SourceCoreCompatibleDataMatches.Context}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError)))
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
  (functions : FunctionModel compilation.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}
  (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {scope : Scope} {id : StatementId} {resolution : MatchResolution} {expected : TypeSystem.Ty} {type : Ty} {reason : Word}
  {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
  (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution type reason
    expressionCertificate bodyCertificate code)
  (ordinary : CompatibleMatchSelectionPrefix.Ordinary certificate)
  (unique : NodeOccurrencesUnique source)
  (validity : SourceSemantics.Context → Prop) (literals : IntegerLiteralResolution → Prop)
  (signatures : context.signatures = compilation.signatures)
  (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
  (literalSites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
  (validity_binders : ∀ {binders target}, BindersExtend source.owner context binders target → validity context → validity target)
  (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
  {statementNode : StatementNode} (statementFound : source.lookupStatement? id = some statementNode)
  (statementForm : statementNode.form = .matchWith resolution)
  {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
  {lowered : SourceCoreBasic.LoweredExpr}
  (uniqueExpression : ∀ other, expressionCertificate scope resolution.scrutinee other → other = lowered)
  {administrative : Core.Context} {faults : FunctionCalls.FaultRep}
  (guard : Location → NativeFrame → Prop)
  (producer : MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
  (stateBindings : Bindings callerProtocol)
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer.toOrdinary location native)

include allocator definitions registered extended certificate ordinary unique signatures numericRequirements literalSites
  validity_binders catalogValid statementFound statementForm found uniqueExpression producer stateBindings acquire in
theorem preserves_bounded_for (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : validity context → ∀ child, child < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        context evidence source expressionCertificate faults child)
    (armMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.ArmPreservesBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults))
    (defaultMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.DefaultPreservesBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults)) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (fun context id _ => ProtectedStateImperativeTypedSourceSites.Head source context id)
      functions program evidence validity (values := compilation.values) (source := source) (context := context)
      (administrative := administrative) (frameLayout := frame) (globals := globals) (registry := registry)
      (faults := faults) size (scope := scope) id expected type code := by
  intro valid parentTyped
  obtain ⟨control, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
    sites unique parentTyped statementFound statementForm found
  exact CompatibleMatchPreservation.Stateful.WithReady.Certificate.preserves_bounded_for
    onError allocator functions definitions registered extended certificate ordinary unique validity literals signatures
    numericRequirements literalSites validity_binders catalogValid found uniqueExpression casesTyped (fun {statements} present => defaultTyped statements present) budget size bounded
    callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (CallableIndexedOwnedAdmittedMatchReadiness.prefix_transfers bridge source)
    (ProtectedStateLexicalSourceSites.ExpressionFacts source) scrutineeTyped guard producer stateBindings acquire
    (fun valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (expressionMeaning valid child smaller))
    (armMeaning control) (defaultMeaning control) valid True.intro

include allocator definitions registered extended certificate ordinary unique signatures numericRequirements literalSites
  validity_binders catalogValid statementFound statementForm found uniqueExpression producer stateBindings acquire in
theorem reflects_bounded_for (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : validity context → ∀ child, child < budget →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        context evidence source expressionCertificate faults child)
    (armMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.ArmReflectsBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults))
    (defaultMeaning : ∀ control,
      RecursiveNamedMatchSourceBounds.Stateful.WithReady.DefaultReflectsBelowFor callerProtocol
        (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard functions program context control evidence
        resolution bodyCertificate expected type budget validity scope
        (source := source) (administrative := administrative) (frame := frame) (globals := globals)
        (registry := registry) (faults := faults)) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith callerProtocol
      (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (fun context id _ => ProtectedStateImperativeTypedSourceSites.Head source context id)
      functions program evidence validity (values := compilation.values) (source := source) (context := context)
      (administrative := administrative) (frameLayout := frame) (globals := globals) (registry := registry)
      (faults := faults) size (scope := scope) id expected type code := by
  intro valid parentTyped
  obtain ⟨control, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
    sites unique parentTyped statementFound statementForm found
  exact CompatibleMatchReflection.Stateful.WithReady.Certificate.reflects_bounded_for
    onError allocator functions definitions registered extended certificate ordinary validity literals signatures
    numericRequirements literalSites validity_binders catalogValid found uniqueExpression casesTyped (fun {statements} present => defaultTyped statements present) budget size bounded
    callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (CallableIndexedOwnedAdmittedMatchReadiness.prefix_transfers bridge source)
    (ProtectedStateLexicalSourceSites.ExpressionFacts source) scrutineeTyped guard producer stateBindings acquire
    (fun valid child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (expressionMeaning valid child smaller))
    (armMeaning control) (defaultMeaning control) valid True.intro

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMatchBounds
