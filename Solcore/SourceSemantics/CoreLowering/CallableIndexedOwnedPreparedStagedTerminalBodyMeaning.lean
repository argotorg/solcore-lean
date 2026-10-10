import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalStatementOrigins

/-! Actual accepted terminal compilation supplies its used expression and
footer. The original SourceView supplies the terminal occurrence. Strict
expression hypotheses then establish meaning for that exact emitted body,
including nested stage failures and the reached caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
universe u

def fallback (type : Ty) (fellThrough : Word) : Expr :=
  if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}

/-- Substitution changes statement types, while preserving the original
terminal occurrence and expression identifier. -/
theorem source_head
    (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
    {invocation : Staging.Recursive.Scope} (view : SourceView invocation.source compilerSource) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression statements := by
  cases receipt.terminal with
  | returning rest found form =>
    exact CallableIndexedOwnedPreparedTerminalStatementOrigins.returning_head view rest found form
  | tail found form =>
    exact CallableIndexedOwnedPreparedTerminalStatementOrigins.tail_head view found form

/-- The actual used child type and footer determine the exact renamed body. -/
theorem emitted
    (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
    (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code receipt.child.type
      ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename ξ)
      escaped ((fallback receipt.child.type fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [receipt.sameType, CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result
        (LocalLoop.returnValue result receipt.child.expression) escaped (fallback result fellThrough) ξ))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
  (view : SourceView invocation.source compilerSource)
  (certifies : ∀ child, policy.lowerExpression receipt.childFuel compilerSource scope expression reasonAt = .ok child →
    certificate scope expression child)
  {node : ExpressionNode}
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view certifies found sourceTyped environments heaps locals agrees typed admitted in
/-- Preservation uses the actual accepted compiler child once. No body law
or independent terminal Head is supplied. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type receipt.child.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  rw [emitted receipt ξ]
  exact CallableIndexedOwnedAdmittedStagedTerminalBody.preserves bridge (source_head receipt view)
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped ((fallback receipt.child.type fellThrough).rename ξ) child within

include view certifies found sourceTyped environments heaps locals agrees typed admitted in
/-- Reflection starts from the literal emitted body, obtains a strict native
child and reconstructs an independently measured original Source body. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type receipt.child.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  rw [emitted receipt ξ] at completed
  exact CallableIndexedOwnedAdmittedStagedTerminalBody.reflects bridge (source_head receipt view)
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped ((fallback receipt.child.type fellThrough).rename ξ) completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
