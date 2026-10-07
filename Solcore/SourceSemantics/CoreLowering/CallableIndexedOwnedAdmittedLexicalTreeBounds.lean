import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalReadiness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds

/-! The existing lexical Tree folds consume authentic Source syntax and
admission at actual inputs. Real child posts and allocations supply each next
input; lexical restoration retains the actual returned pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory
open GenericLexicalStatements (Tree Scope ValuesContext)
open CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (bindings : Bindings callerProtocol)
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (unique : NodeOccurrencesUnique source)

include definitions registered producer bindings acquire unique in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context →
      BinderExtends source.owner context binder nextContext → validity nextContext)
    (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : ∀ child, child ≤ budget → ∀ context, validity context →
      CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (expressions context) faults child)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code) :
    PreservesAtFor callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) condition
      (GenericLexicalStatements.Syntax source expressionSyntax)
      (validity := validity) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) functions program evidence
      size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted trace
  exact RecursiveNamedLexicalTreeBounds.Stateful.WithReady.preserves_at_for
    (protocol := callerProtocol) (condition := condition) (producer := producer)
    (stateBindings := bindings) (acquire := acquire)
    (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
    (facts := GenericLexicalStatements.Syntax source expressionSyntax)
    (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
    (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
    (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
    (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
    functions definitions registered program evidence validity extend budget size bounded
    (fun child within context childValid => CallableIndexedOwnedAdmittedLexicalReadiness.preserves_at bridge
      _ (expressionMeaning child within context childValid))
    tree valid sourceFacts unique environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted trace

include definitions registered producer bindings acquire unique in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context →
      BinderExtends source.owner context binder nextContext → validity nextContext)
    (budget size : Nat) (bounded : size ≤ budget)
    (expressionMeaning : ∀ child, child ≤ budget → ∀ context, validity context →
      CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        context evidence source (expressions context) faults child)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code) :
    ReflectsAtFor callerProtocol (CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge) condition
      (GenericLexicalStatements.Syntax source expressionSyntax)
      (validity := validity) (source := source) (context := context) (registry := registry)
      (faults := faults) (frameLayout := frame) (globals := globals) functions program evidence
      size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted completed
  exact
    RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for
      (protocol := callerProtocol) (condition := condition) (producer := producer)
      (stateBindings := bindings) (acquire := acquire)
      (readiness := CallableIndexedOwnedAdmittedLexicalReadiness.readiness bridge)
      (facts := GenericLexicalStatements.Syntax source expressionSyntax)
      (headFacts := ProtectedStateLexicalSourceSites.HeadFacts source expressionSyntax)
      (exprFacts := ProtectedStateLexicalSourceSites.ExpressionFacts source)
      (sites := ProtectedStateLexicalSourceSites.sites program evidence unique)
      (transfers := CallableIndexedOwnedAdmittedLexicalReadiness.allocation_transfers bridge bindings source)
      functions definitions registered program evidence validity extend budget size bounded
      (fun child within context childValid => CallableIndexedOwnedAdmittedLexicalReadiness.reflects_at bridge
        _ (expressionMeaning child within context childValid))
      tree valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped
      initial conditioned admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalTreeBounds
