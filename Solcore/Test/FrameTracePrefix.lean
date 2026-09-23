import Solcore.ContractRuntime.FrameTracePrefix

/-! Definition-only compile regressions for concrete frame-trace prefixes. -/

set_option autoImplicit false

namespace Tests

open Solcore.ContractRuntime

private inductive PrefixEvent where
  | entered
  | completed

private def enteredTrace : FrameTrace PrefixEvent :=
  FrameTrace.record FrameTrace.empty .entered

private def completedTrace : FrameTrace PrefixEvent :=
  FrameTrace.record FrameTrace.empty .completed

private example :
    FrameTrace.IsPrefixOf FrameTrace.empty enteredTrace :=
  ⟨enteredTrace, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace enteredTrace :=
  ⟨FrameTrace.empty, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace
      (FrameTrace.append enteredTrace completedTrace) :=
  ⟨completedTrace, rfl⟩

private example :
    FrameTrace.IsPrefixOf enteredTrace
      (FrameTrace.append
        (FrameTrace.append enteredTrace completedTrace)
        enteredTrace) :=
  ⟨FrameTrace.append completedTrace enteredTrace, rfl⟩

end Tests
