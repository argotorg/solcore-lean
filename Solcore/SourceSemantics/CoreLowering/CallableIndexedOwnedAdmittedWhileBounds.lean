import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.ProtectedWhileGenericEndpoint
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape

/-! Authentic Source statement syntax and typing supply the real condition
and loop-body sites. Admitted children run at the exact retained states from
the existing measured while proofs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedLoopContracts (Below)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open TypedLexicalWhile (Scope ValuesContext)

private theorem body_syntax {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId} {expected : TypeSystem.Ty}
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements) :
    ProtectedStateImperativeSourceSites.Facts source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, syntaxTree, _typed⟩ := facts
  cases syntaxTree
  case body syntaxTree =>
    cases syntaxTree <;> simp_all
  all_goals simp_all [ProtectedStateImperativeSourceSites.Facts]

/-- Only the authentic parent while occurrence projects condition and body
facts; original Source typing remains independent of the lowered Core type. -/
theorem sites {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (facts : ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode) :
    ProtectedStateLexicalSourceSites.ExpressionFacts source context condition conditionNode ∧
      ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax context false statements expected := by
  have bodySyntax := body_syntax facts found form
  obtain ⟨_mode, _rest, _syntaxTree, statementsTyped⟩ := facts
  obtain ⟨conditionTyped, bodyTyped⟩ := ProtectedStateImperativeTypedSourceSites.while_loop unique
    (ProtectedStateImperativeTypedSourceSites.head statementsTyped) found form
  obtain ⟨original, contains, sameType⟩ := conditionTyped.stored_type
  have sameNode : original = conditionNode :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans conditionFound)
  subst original
  exact ⟨by simpa only [ProtectedStateLexicalSourceSites.ExpressionFacts, sameType] using conditionTyped,
    bodySyntax, bodyTyped⟩

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
  {administrative : Core.Context} {type : Ty} {conditionCode code : Expr} {selfReason : Word} {scope : Scope}
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (transport : AdministrativeTransport callerProtocol)

include transport in
theorem preserves_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code)) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid sourceFacts
  obtain ⟨conditionFacts, bodyFacts⟩ := sites unique sourceFacts found form conditionFound
  exact ProtectedWhile.Body.Stateful.WithReady.while_preserves_bounded_for
    (protocol := callerProtocol) (guard := guard) (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedWhileReadiness.activation bridge)
    functions program evidence transport validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge _ (meaning child smaller))
    found form conditionFound conditionFacts bodyFacts conditionTree typed unique correct size bounded valid True.intro

include transport in
theorem reflects_bounded_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  intro size bounded valid sourceFacts
  obtain ⟨conditionFacts, bodyFacts⟩ := sites unique sourceFacts found form conditionFound
  exact ProtectedWhile.Body.Stateful.WithReady.while_reflects_bounded_for
    (protocol := callerProtocol) (guard := guard) (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (facts := ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
    (activation := CallableIndexedOwnedAdmittedWhileReadiness.activation bridge)
    functions program evidence transport validity budget
    (fun child smaller => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge _ (meaning child smaller))
    found form conditionFound conditionFacts bodyFacts conditionTree typed correct bodyCannotFault size bounded valid True.intro

include transport in
/-- The authentic same-code body compiler Tree discharges the separate Source
control-fault restriction through its existing proved control shape. -/
theorem reflects_bounded_from_tree_for (validity : SourceSemantics.Context → Prop) (budget : Nat)
    (meaning : Below budget (fun size => CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults size))
    {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode code selfReason) (LocalLoop.resultType type) ambient.definitions)
    (unique : NodeOccurrencesUnique source)
    (correct : Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.Facts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size false statements expected type code))
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (bodyTree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values source
      expressionSyntax certificates ambient.definitions administrative context scope
      (.statements false statements) expected type code) :
    ∀ size, size ≤ budget → RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith
      callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) guard
      (ProtectedStateImperativeTypedSourceSites.HeadFacts source expressionSyntax)
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) size id expected type (LocalLoop.whileLoop type conditionCode code selfReason) := by
  exact reflects_bounded_for bridge guard functions evidence transport validity budget meaning
    found form conditionFound conditionTree typed unique correct
    (fun executed => bodyTree.control_not_fault unique executed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileBounds
