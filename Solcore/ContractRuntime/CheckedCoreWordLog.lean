import Solcore.ContractRuntime.RuntimeScalars

/-! ABI-independent word logs emitted by checked Core execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
One internal checked-Core log observation.

The active execution context supplies `emitter`; Core supplies only the raw
word-sized topic and payload. ABI interpretation is deliberately separate.
-/
structure CheckedCoreWordLog where
  emitter : Address
  topic : Core.Word
  payload : Core.Word
  deriving Repr, BEq, DecidableEq

end Solcore.ContractRuntime
