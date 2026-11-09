import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.CodeImage
import Solcore.Frontend.RustHull.LinkedContract
import Solcore.Frontend.RustHull.ScalarExecution

/-!
# Rust Hull

Checked import of the typed Hull that the pinned Rust compiler exports, its execution on the Core
machine, and the proofs about both. Read in this order. `docs/guide/frontend.md` lists every file.

1. **Syntax.** `RustHull/Syntax` is the program, and `RustHull/Decode` reads the exported text.
2. **Meaning.** `RustHull/Semantics` is the independent evaluation; it does not run compiled Core.
   It shares a few compiler definitions: `AccountState.Account` and `Memory.packBytes` in
   `Semantics/World`, and `YulFragment.primitives` in `Semantics/Frames`.
   `RustHull/Semantics/` gives the effects: memory, digests, world, accounts, the stacked effect
   layers, and frames.
3. **Compiler.** `RustHull/Lowering` compiles Hull and inline Yul to Core, on top of
   `RustHull/Memory`, `RustHull/LoweringSupport`, `RustHull/Precompiles` and `RustHull/Effects`.
   `RustHull/AccountRuntime` builds message frames, and `RustHull/Contract`,
   `RustHull/LinkedContract` and `RustHull/ScalarExecution` are the public entry points:
   `decodeText`, `ScalarExecution.prepare`, `LinkedContract.prepareDeployment` and
   `Contract.runWithReceipt`.
4. **Main theorems.** `RustHull/Safety` excludes machine faults. `RustHull/Correspondence` connects
   functions and programs to public execution. `RustHull/ContractStateTheorems`,
   `RustHull/ContractCodeTheorems` and `RustHull/ContractCallTheorems` do the same for contracts,
   layer by layer.

`RustHull/Internal/` holds the proofs behind those theorems.

Imported Hull is a separate path from the native source compiler. See
`docs/design/hull-meaning-preservation.md` for what is connected and what is not.
-/
