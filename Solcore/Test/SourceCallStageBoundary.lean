import Solcore.SourceSemantics.CoreLowering.CallStageBoundary

/-! A stage failure precedes even an absent argument occurrence. A Core callee
write remains visible, while the argument's different write is skipped. The
latter test is universal over authenticated dispatch receipts, without assuming
an argument or callable-body evaluation. -/

set_option autoImplicit false
namespace Tests.SourceCallStageBoundary
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"call_stage_boundary", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "call_stage_boundary.solc"⟩, 0, 1⟩
private def parameter : TypedBinder := { id := ⟨owner, 0⟩, name := "input", scheme := .mono .word, comptime := true }
private def node : ExpressionNode := { id := id 1, span, type := .function .word .unit, form := .lambda [parameter] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression (id 1)], nodes := [.expression node] }
private def program : Program := ⟨⟨[], [], [], [], [], []⟩, [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures program.signatures
private def function : Dynamic.Closure := {
  parameters := [parameter], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def contract : Staging.CallGuard.Contract := ⟨[parameter], false⟩
private def frame : Staging.CallBoundary.Frame where
  stages := ⟨false, .unit, fun _ => some .runtime⟩
  Binds value selected := value = .closure function ∧ selected = contract
  userCallable := by rintro value selected ⟨rfl, _⟩; exact .closure _
  unique := by rintro value left right ⟨_, rfl⟩ ⟨_, rfl⟩; rfl
private def reason : Staging.CallGuard.Fault := .argumentStage 0 (id 2) .runtime
private def metadata : IndirectCallResolution := { argumentCount := 1, argumentTypeBeforeCoercion := .word, argumentTypeAfterCoercion := .word }

private theorem rejected : Staging.CallBoundary.GuardRejects frame (id 0) [id 2] (.closure function) reason := by
  apply Staging.CallBoundary.GuardRejects.contract (show frame.Binds (.closure function) contract from ⟨rfl, rfl⟩)
  apply Staging.CallGuard.Rejects.arguments
  · rintro (flag | only)
    · cases flag
    · cases only
  · exact .head (.wrongStage (.inr (.inl rfl)) rfl (by decide))

private theorem callee (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context [] source [] heap (id 1) (.closure function) heap :=
  .intro ⟨List.mem_singleton_self _, rfl⟩ (.lambda rfl) .nil

/-- The absent argument would fail if evaluated. -/
example (heap : Dynamic.Heap) : Dynamic.ExpressionFaults program context [] source [] heap (id 2)
    (.missingExpression (id 2)) heap := by
  apply Dynamic.ExpressionFaults.missing
  exact .expression (by decide) (.nil _)

/-- The call boundary nevertheless reports the earlier stage failure, with no
argument execution in its derivation. -/
example (heap : Dynamic.Heap) :
    Staging.CallBoundary.Executes program frame context [] source [] heap (id 0) (id 1) [id 2] metadata (.stageFault reason) heap :=
  .stageRejected (callee heap) rejected

example : ¬ Staging.CallBoundary.GuardAccepts frame (id 0) [id 2] (.closure function) := by
  intro accepted
  exact accepted.not_rejects rejected

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def calleeCode : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 11))) (Core.LanguageResult.success (.var 2))
private def argumentCode : Core.Expr :=
  .letE (.storeCell (.var 0) (.word (word 22))) (Core.LanguageResult.success .unit)

/-- Any authenticated row with these original source-stage facts retains only
the callee's write. The argument would write 22, and is not evaluated. -/
example (site : SourceCoreCallableContracts.Callsite) (carrier : Core.Value)
    (dispatch : CallStageBoundary.Dispatch frame site (id 0) [id 2] (.closure function) carrier) :
    Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      (site.lower (word 99) .unit calleeCode argumentCode)
      (.inLeft .unit (.word (dispatch.reason reason))) [.word (word 11)] := by
  have calleeEvaluation : Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      calleeCode (.inRight .word carrier) [.word (word 11)] :=
    .letE (.storeCell (.var rfl) rfl .word rfl) (.inRight (.var rfl))
  have wrapped : Core.Evaluates [.cellRef .word 0, carrier] [.word (word 0)]
      calleeCode (.inRight .word (.pair dispatch.function (.word dispatch.contract))) [.word (word 11)] := by
    rw [← dispatch.shape]
    exact calleeEvaluation
  exact site.lower_stage_failure (word 99) dispatch.row _ dispatch.found (dispatch.rejected rejected) wrapped

/-- Static receipt reflection reconstructs independent acceptance. It does not
use an evaluated argument or function body as a premise. -/
example (frame : Staging.CallBoundary.Frame) (site : SourceCoreCallableContracts.Callsite)
    (call : ExpressionId) (arguments : List ExpressionId) (sourceValue : Dynamic.Value) (carrier : Core.Value)
    (dispatch : CallStageBoundary.Dispatch frame site call arguments sourceValue carrier)
    (passed : dispatch.row.beforeArguments = .ok ()) :
    Staging.CallBoundary.GuardAccepts frame call arguments sourceValue :=
  dispatch.accepted_iff.mp passed

end Tests.SourceCallStageBoundary
