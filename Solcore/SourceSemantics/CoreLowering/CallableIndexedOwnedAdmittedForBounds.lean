import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.ProtectedForGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape

/-! Genuine Source loop facts at the visited initializer context supply the
condition, body, and ordered post sites. The existing measured for endpoint
keeps the actual retained states and independent Source and native grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedForContracts (Below)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open TypedLexicalWhile (Scope ValuesContext)

/-- Source control and post-item typing remain attached to the same authentic
body syntax and typing at this exact loop context. -/
def LoopFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (condition : ExpressionId) (post : List ForItemForm)
    (statements : List StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ (control : SourceSemantics.ControlContext) (bodyFinal : SourceSemantics.Context)
    (bodyFacts : SourceSemantics.BodyFacts) (postFinal : SourceSemantics.Context),
    ExpressionHasType source context condition .bool ∧
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements false statements) expected ∧
    StatementsHaveType source control.enterLoop context statements bodyFinal bodyFacts ∧
    ForItemsHaveType source control.enterLoop context post postFinal ∧
    GenericForHeader.Syntax source expressionSyntax context post

namespace LoopFacts

theorem of_done {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    {control : SourceSemantics.ControlContext} {bodyFinal postFinal : SourceSemantics.Context}
    {bodyFacts : SourceSemantics.BodyFacts}
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context
      (.initializers [] condition post statements) expected)
    (bodyTyped : StatementsHaveType source control.enterLoop context statements bodyFinal bodyFacts)
    (postTyped : ForItemsHaveType source control.enterLoop context post postFinal) :
    LoopFacts source expressionSyntax context condition post statements expected := by
  cases syntaxTree with
  | initializersDone _found conditionType typed _conditionSyntax bodySyntax postSyntax =>
    exact ⟨control, bodyFinal, bodyFacts, postFinal,
      by simpa only [conditionType] using typed, bodySyntax, bodyTyped, postTyped, postSyntax⟩

/-- Only this genuine parent Source judgment and actual initializer trace
identify the visited loop context. The normalized syntax is the authentic
remaining initializer site from the same compiler fold. -/
theorem after_initializer {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context loopContext : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
    {expected : TypeSystem.Ty} {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (parent : ProtectedStateImperativeTypedSourceSites.Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop items condition post statements)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (executed : Dynamic.ForItemsExecute program context evidence source environment before
      items loopContext next after)
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax loopContext
      (.initializers [] condition post statements) expected) :
    LoopFacts source expressionSyntax loopContext condition post statements expected := by
  obtain ⟨control, staticContext, postContext, bodyFinal, bodyFacts,
    itemsTyped, _conditionTyped, bodyTyped, postTyped⟩ :=
    ProtectedStateImperativeTypedSourceSites.for_loop unique parent found form
  have same := (executed.preserved wellFormed runtime covers locals heapTyped itemsTyped).1
  subst loopContext
  exact of_done syntaxTree bodyTyped postTyped

theorem sites {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (facts : LoopFacts source expressionSyntax context condition post statements expected)
    (found : source.lookupExpression? condition = some conditionNode) :
    ProtectedStateLexicalSourceSites.ExpressionFacts source context condition conditionNode ∧
      ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax context false statements expected := by
  obtain ⟨control, bodyFinal, bodyFacts, _postFinal, typed, bodySyntax, bodyTyped, _postTyped, _postSyntax⟩ := facts
  obtain ⟨original, contains, sameType⟩ := typed.stored_type
  have sameNode : original = conditionNode :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst original
  exact ⟨by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using typed,
    bodySyntax, control.enterLoop, bodyFinal, bodyFacts, bodyTyped⟩

end LoopFacts

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (guard : Location → NativeFrame → Prop)
  {certificate : GenericExpressionMeaning.Certificate} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word} {scope : Scope}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport callerProtocol)

include transport in
theorem loop_preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (loopFacts : LoopFacts source expressionSyntax context condition post statements expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postPreserves : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostPreservesAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode))
    (postFaults : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostFaultsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode)) :
    ∀ size, size ≤ budget → ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      functions program evidence validity size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type
      (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  obtain ⟨conditionFacts, bodyFacts⟩ := LoopFacts.sites unique loopFacts conditionFound
  exact ProtectedFor.Body.Stateful.WithReady.loop_preserves_bounded_for
    functions program evidence callerProtocol guard transport
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedForReadiness.activation bridge)
    validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning child smaller))
    conditionFound conditionFacts bodyFacts conditionTree typed unique correct postPreserves postFaults

include transport in
/-- The exact same-code body compiler Tree supplies its existing control
shape proof, while the actual post-item producers keep their live states. -/
theorem loop_reflects_bounded_from_tree_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (loopFacts : LoopFacts source expressionSyntax context condition post statements expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (postReflects : ∀ {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
      {ξ : Renaming} {contextLocation location : Location},
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      validity context →
      Below budget (fun size => ProtectedFor.Body.Stateful.WithReady.PostReflectsAt callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard size functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode))
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (bodyTree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values source
      expressionSyntax certificates ambient.definitions administrative context scope
      (.statements false statements) expected type code) :
    ∀ size, size ≤ budget → ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      functions program evidence validity size (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type
      (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  obtain ⟨conditionFacts, bodyFacts⟩ := LoopFacts.sites unique loopFacts conditionFound
  exact ProtectedFor.Body.Stateful.WithReady.loop_reflects_bounded_for
    functions program evidence callerProtocol guard transport
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedForReadiness.activation bridge)
    validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning child smaller))
    conditionFound conditionFacts bodyFacts conditionTree typed correct
    (fun executed => bodyTree.control_not_fault unique executed) postReflects

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForBounds
