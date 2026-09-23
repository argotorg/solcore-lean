import Solcore.ContractRuntime.FrameTrace
import Solcore.ContractRuntime.FrameContinuationContextWithTracePrefix

/-! Definition-only tests for indexed incremental frame-trace extension. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive ExtensionEvent where
  | entered
  | child

private inductive ExtensionReason where
  | marker

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def matchesEntered : List ExtensionEvent → Bool
  | [.entered] => true
  | _ => false

private def matchesChild : List ExtensionEvent → Bool
  | [.entered, .child] => true
  | _ => false

private def matchesRepeated : List ExtensionEvent → Bool
  | [.entered, .child, .child] => true
  | _ => false

private def earlierTrace : FrameTrace ExtensionEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def extension : FrameTrace.ExtensionFrom earlierTrace :=
  FrameTrace.ExtensionFrom.start earlierTrace

private def recorded : FrameTrace.ExtensionFrom earlierTrace :=
  extension.record .child

private def repeated : FrameTrace.ExtensionFrom earlierTrace :=
  recorded.record .child

private def baseContext :
    FrameContinuationContext Nat (FrameTrace ExtensionEvent)
      ExtensionReason :=
  ⟨WorldState.empty, ⟨10, earlierTrace⟩, ⟨20, recorded.toTrace⟩,
    ⟨WorldState.empty, .trapped .marker⟩⟩

private example :
    FrameContinuationContextWithTracePrefix Nat ExtensionEvent
      ExtensionReason :=
  ⟨baseContext, recorded.earlier_isPrefixOf_toTrace⟩

def testFrameTraceExtension : IO Unit := do
  assertTrue
    (matchesEntered extension.toTrace.toList)
    "start must retain a nonempty earlier trace exactly once"

  assertTrue
    (matchesChild recorded.toTrace.toList)
    "record must place one event after the fixed earlier trace"

  assertTrue
    (matchesRepeated repeated.toTrace.toList)
    "record must preserve chronological duplicates"

end Tests
