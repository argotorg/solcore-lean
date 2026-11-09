import Solcore.Synthesis.Core
import Solcore.Synthesis.Source

/-!
# Synthesis

The generators of the semantic differential tests. A case is a checked Core program with its
reference result, and the source text an emitter prints from it. Read in this order.
`docs/guide/synthesis.md` lists every file, and maps every profile to its file.

1. **What a case is.** `Source/Cases` is the shape of a case and a corpus. `Source/Acceptance` says
   what a profile accepts and which inputs it runs.
2. **What is generated.** `Core/Fragment` is the checked fragment, `Core/Generator` and `Core/Seed`
   draw programs from it, and `Core/Shrink` reduces them.
3. **What is printed.** `Source/Emitter` defines `EmittedProgram`, which most emitters return.
4. **One profile.** `Internal/` has one file per family of profiles: its Core reference, renderer,
   emitter, stateful execution and cases.
5. **Emitter meaning.** `Source/ScalarMeaning/` proves that the text of fifteen emitters means what
   the original Core program computes. The grammars and semantics are its specification, and
   `PureTheorems`, `LoopTheorems` and `StatefulTheorems` hold the results.

Only `Source/ScalarMeaning/` holds proofs of this kind. Elsewhere, an admitted program carries a
proof of Core typing, and nothing more.
-/
