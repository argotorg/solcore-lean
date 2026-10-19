import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedPlainInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! A genuine generalized Source declaration creates the actual mixed physical
prefix before the remaining ordinary Source statements are lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open TypedLexicalWhile (initializedRequest sequence)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private theorem head_typed {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (source named) context (id :: rest)) :
    ∃ control final facts, StatementHasType (source named) control context id final facts := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton head => exact ⟨control, _, _, head⟩
  | cons head _ => exact ⟨control, _, _, head⟩

include record registered in
theorem generalized {mode : Bool} {context nextContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : StatementId} {node : StatementNode} {binder : TypedBinder} {initializer : ExpressionId}
    {initializerNode : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {lambdaBody rest : List StatementId} {type : Ty} {lowered : SourceCoreBasic.LoweredExpr}
    {body : Expr} {childFuel : Nat} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
      (found : (source named).lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some initializer))
      (declaration : (SourceCoreDataPlaces.declaredBinders (source named)).filter
        (fun actual => decide (actual.id = binder.id)) = [binder])
      (polymorphic : binder.scheme.quantified ≠ [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (initializerFound : (source named).lookupExpression? initializer = some initializerNode)
      (initializerForm : initializerNode.form = .lambda parameters result lambdaBody)
      (valueType : initializerNode.type = binder.scheme.body)
      (requirements : initializerNode.requirements = [])
      (coercions : initializerNode.coercions = [])
      (site : CellAwareSourceBodyAdmission.Site whole.indexed.base.locals named.signature.key [] (source named) binder initializer)
      (initial : GeneralizedLocalInitializerPackets.Receipt whole.indexed
        (GeneralizedLocalInitializerCompilation.namedInputs compiled childFuel (childFuel + 1)
          (CallableIndexedNamedGeneration.context whole.indexed named) scope initializer reasonAt) site.binding [] lowered)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression (LanguageResult.resultType lowered.type) whole.indexed.layouts.definitions)
      (allocation : SourceCoreAllocationLayouts.Allocation whole.indexed.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated whole.indexed.ancestry.layout.frame
        whole.indexed.base.globals.length
        (whole.indexed.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
    (sourceEq : invocation.source = source named)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named reasonAt)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer nextContext ((binder.id, lowered.type) :: scope) mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped current admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique := runtime.graph.nodeOccurrencesUnique
  let descriptor := Dynamic.GeneralizedClosure.ofDirectLambda context (source named) environment binder initializer
    parameters result lambdaBody
  have captures : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer descriptor :=
    .directLambda (lookupExpression?_sound initializerFound) initializerForm
      (by simpa only [ExpressionNode.rawType, coercions] using valueType) valueType requirements coercions
  obtain ⟨tailSize, function, location, bound, _strict, actualCaptures, allocated, tail⟩ :=
    CellAwareGeneralizedPlainInversion.generalized (mode := mode) (invocation := invocation) (by simpa only [sourceEq] using unique)
      (by simpa only [sourceEq] using found) form polymorphic (by simpa only [sourceEq] using extended)
      ⟨descriptor, by simpa only [sourceEq] using captures⟩ trace
  have capturesNamed : Dynamic.GeneralizedClosureCaptures context (source named) environment binder initializer function := by
    simpa only [sourceEq] using actualCaptures
  obtain ⟨control, next, facts, headTyped⟩ := head_typed sourceTyped
  have functionTyped := CellAwareGeneralizedSourceInversion.captured_wellTyped runtime locals headTyped
    found form polymorphic capturesNamed
  obtain ⟨values, marker, _agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      _preserved, _effect, nextAuthority, reached, _related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
    CellAwareNamedGeneralizedPrefix.complete bridge compiled record site initial issuer declaration polymorphic extended
      ordinary nativeTyped allocation annotation same producer registered environments heaps locals agrees actualTyped
      current admitted authority physical (ready current physical.read) capturesNamed functionTyped allocated type body
  have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
    intro index current stored
    have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
    simpa only [locationEq, nativeEq] using previous
  obtain ⟨resultContext, resultOutcome, resultHeap, stagedTail, adapted⟩ :=
    remaining nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
      (runtime.transport (.ofBinderExtends extended))
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
      ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
      (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended)
      reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tail
  exact ⟨resultContext, resultOutcome, resultHeap,
    .letGeneralized (by simpa only [sourceEq] using lookupStatement?_sound found) form actualCaptures polymorphic
      (by simpa only [sourceEq] using extended) allocated stagedTail, adapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowGeneralizedLifting
