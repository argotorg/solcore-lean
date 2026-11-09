import Solcore.Frontend.Fragments
import Solcore.Frontend.Current

/-!
# Frontend

Two compilers to Core, and an older chain that neither of them uses. Read in this order.
`docs/guide/frontend.md` lists every file and the main theorems.

1. **Public API.** `SourceCompiler` exports what `SourceCoreExecution` defines: `compile`,
   `Compiled.open`, `Session.run` and `Checkpoint.resume`.
2. **Checking.** From a raw workspace to a checked program: `ProgramInterfaces`, `ProgramImports`,
   `ProgramTypeResolution`, `ProgramSignatures`, `ProgramSignatureFormation`, `TraitResolution`,
   `SourceInference`, and `ProgramChecking` on top, which defines `checkProgram`.
3. **Staging and specialization.** `SourceStageAnalysis`, `SourceSpecialization`,
   `SourceSpecializationWorklist` and `SourceCompilationPlan` close a checked program into a
   finite plan.
4. **Lowering.** `SourceCoreElaboration`, then `SourceCore/`, from expressions and data to the
   source-compatible functions. `SourceCoreCompiler` gives one compiler entry, and
   `SourceCoreIndexedSession` the persistent sessions.
5. **Rust Hull.** A separate path, with the area's main theorems. `RustHull` has its own guide.

`Current` imports every stage of the pipeline. `Fragments` imports the historical adapters: the
pipeline reaches only `WordLiteral` from them, so a reader can skip them. The proofs that lowered
source means what it says are in `SourceSemantics/CoreLowering`, not here.
-/
