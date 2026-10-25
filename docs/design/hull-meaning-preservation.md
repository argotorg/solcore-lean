# Hull meaning preservation

## Completion rule

A feature is connected when its independent `Semantics` derivation reaches the
actual `compile` / `ScalarExecution.prepare` implementation and the public
`run` / `resume` API. Its theorem must relate the result, language-fault reason
and represented source heap. Compiler output, function installation, argument
initialization and loop closures must come from the implementation, rather than
from an assumed body-preservation premise.

Helper lemmas count as intermediate work. Each implementation step should end
with a public theorem consumer, an executable regression, verification and a
commit.

## Public function theorem

`Correspondence.prepare_recursive_program_resumes` relates every genuine finite
chain of resumptions to an independent finite Hull function evaluation. It
preserves values and language faults, including all allocations and writes made
before failure. Completion occurs exactly when cumulative fuel reaches the
transition count; otherwise the computation remains resumable.

The theorem requires successful preparation, `RecursiveProgram` syntactic
eligibility and a finite independent source evaluation. It accepts any source
result: value representation and exclusion of malformed source observations
follow from the proof. Actual compilation and initialization establish scope
coverage, parameter arity and the typed heap relation. Successful builtin
compilation supplies the required argument constraints. No separate
`SafeResult` premise is required.

Public inputs use the existing scalar parser. The theorem does not assert
termination or specify concrete external effects.

The connected fragment includes structural values, pure builtins, recursive
named calls, local variables, blocks, loops and control transfers, product-path
assignments and pattern alternatives. Language fault propagation is connected
through expressions, argument evaluation, function boundaries and every loop
stage (`2b7a07347`).

## Public contract state theorems

`ContractMemoryCorrespondence.prepare_resumes_exact` connects an independent
Hull evaluation to actual `Contract.prepare`, `runWithReceipt` and any genuine
chain of `resumeWithReceipt` calls. Successful compilation and the independent
derivation establish the whole Core evaluation. The proof obtains runtime
references, initial memory, captured frame closures and snapshot observations
from the actual object initialization.

The fragment supports `mload`, `mstore`, `mstore8` and `msize`, together with
pure operations, recursive function calls, loops and language faults. It
preserves the final memory, including writes before failure. The public result
is the actual receipt decoder applied to the source-derived message value, so
export limits and cumulative execution fuel retain their public behavior.

The contract theorems use an empty code catalog, no supplied code image and a
context with `deploying = false`. They do not yet cover deployment or calls
to other contracts.

`Tests.RustHullMemoryCorrespondence.public_resumes` supplies complete independent
source derivations for unaligned memory access and a fault after a write, then
applies the public theorem. Executable regressions also check checkpoint
resumption, public outcomes and final Core snapshots.

`ContractRuntimeEffectsCorrespondence.prepare_resumes_exact` extends this
connection to `sload`, `sstore`, `tload` and `tstore`, interleaved with memory
operations. The actual allocator establishes distinct locations for all memory
and storage registers, including shared references. The resulting message
relates the independent final world and memory to the actual frame snapshot,
message finalization and public receipt decoder.

The proof includes static-write rejection, writes before faults and transaction
finalization. `Tests.RustHullRuntimeEffectsCorrespondence.public_resumes`
provides independent derivations for successful interleaved writes and reads,
a memory fault after storage writes, and a rejected static write after a memory
write. Executable checks also verify committed persistent storage, cleared
transient storage, retained failure snapshots and empty exported worlds on
failure.

`ContractEnvironmentCorrespondence.prepare_resumes_exact` adds message and
block observations to the same public connection. It covers address, caller,
call value, calldata and return-data size, calldata word reads, supplied gas,
ten optional ambient words, block hashes and blob hashes. The actual context
normalization and shared/frame initializers establish their observations;
memory and storage operations preserve them. Missing optional inputs retain
their language-fault reasons. The `codesize` implementation also has a builtin
and frame correspondence proof, but its public connection requires the
remaining code-image support.

`Tests.RustHullEnvironmentCorrespondence.public_resumes` supplies independent
derivations for calldata-driven memory writes, timestamp-driven storage writes,
block/blob hash reads and a missing-gas fault after writes. Runtime checks cover
address normalization, transient-state finalization, checkpoints and the
snapshots retained before a fault.

`ContractLogCorrespondence.prepare_resumes_exact` adds `log0` through `log4`
to the same memory, storage and environment model. Its independent event
semantics records emitter, topics and a copied payload. The actual allocator
supplies the log mapping and cursor, and the compiled frame observes their
final values before message completion and public receipt decoding. Static
logging, capacity overflow and memory overflow retain their termination or
fault behavior.

`Tests.RustHullLogCorrespondence.public_resumes` supplies independent source
derivations for two logs separated by a memory overwrite, a later missing-gas
fault, and logging in a static context. Executable checks compare copied
payloads, checkpoint resumption and failure receipts with retained Core
snapshots.

`ContractFullCorrespondence.prepare_resumes_exact` also covers explicit
`return`, `revert`, `stop` and `invalid`. These operations share the existing
source memory, world and log state. The public connection preserves the exit
kind and returned range, memory expansion and overflow, and the message's
commit or rollback behavior. A source termination prevents subsequent
statements from running.

`Tests.RustHullTerminationCorrespondence.public_resumes` supplies five complete
source derivations: memory, logs and storage are updated before each exit or
an overflowing return range. Runtime checks verify return bytes, successful
storage and log publication, failure rollback, multiple resumptions and the
retained failure snapshots.

`ContractCopyCorrespondence.prepare_resumes_exact` adds `mcopy` and
`calldatacopy` to the same public connection. The independent copy relation
reads a retained source mapping, including when source and destination overlap.
Actual calldata initialization supplies that mapping. The proof covers
word-sized chunks and byte tails, source zero padding and address overflow,
range checks before memory changes, and the resulting memory extent.

`Tests.RustHullMemoryCopyCorrespondence.public_resumes` covers a 33-byte input
copy followed by overlapping copies in both directions. Its four cases include
ordinary return, a zero-length copy at the largest address, and separate
source/destination overflow. Runtime checks compare returned bytes, final
memory snapshots and multiple resumptions, including a source-overflow case
that must not expand destination memory.

`ContractHashCorrespondence.prepare_resumes_exact` adds `keccak256`. The
independent source algorithm specifies the lane permutation, 24 rounds,
136-byte absorption blocks, Ethereum padding and the final digest. Its proof
reaches the actual Core permutation, recursive absorption helper and public
contract execution. Hashing expands only the touched memory range and leaves
the input bytes unchanged.

`Tests.RustHullKeccakCorrespondence.public_resumes` supplies source derivations
for empty input at the largest offset, an unaligned short input, the 136-byte
rate boundary, a 137-byte input and memory overflow. Executable checks compare
returned digest bytes against the separate ABI hash implementation, verify
input preservation and memory size, and exercise repeated resumptions.

## Priorities

| Priority | Theorem / connection | Completion evidence | Status |
| --- | --- | --- | --- |
| 1 | Product-path assignment preserves the result and heap, including failed RHS calls. | The common recursive public theorem covers nested places; source/public/runtime consumers cover successful writes and faults. | Connected |
| 1 | Pattern matching preserves arm selection, binder allocation and control outcomes. | Actual `testPattern` and `lowerAlternatives` feed the mutual derivation proof and public resumptions, including skipped arms and faults. | Connected |
| 2 | Accepted initialization and execution exclude malformed source observations. | Actual globals, parameter binding, locals and match binders supply scope coverage; compiler checks and typed heaps exclude malformed observations. The public theorem has no outcome-safety premise. | Connected |
| 3 | Concrete external state is preserved. | Memory, storage, environment reads, logs, explicit termination, memory copying and hashing reach public receipts and resumptions; further state operations remain. | In progress |
| 4 | External calls, creation and rollback preserve observable outcomes. | Returned data, balances, storage, receipts and rollback are related through actual execution and resumption. | Open |
| 4 | Assembly preserves its independent meaning. | Yul statement derivations connect to actual lowering and public execution, reusing the concrete effect relations. | Open |
| 5 | Divergence and reverse correspondence. | Relate nontermination and characterize Core outcomes after terminating execution and effects are covered. | Open |

Priorities 1 and 2 close gaps in the existing pure Hull theorem. Priorities 3
and 4 connect the remaining observable runtime behavior. Priority 5 should not
delay those connections.

## Next public milestone

Connect account inspection through the same state relations. The remaining work includes code
images and catalogs, external calls, creation, rollback and assembly. Each step
must derive runtime inputs from actual initialization and end in a public
theorem consumer.

## Verification

- Build the affected theorem modules and the full test executable.
- Run independent-source public consumers and the complete test suite.
- Check the semantic-kernel declaration policy and the public theorem's axioms.
- Record actual ambiguities or upstream bugs in the ignored `questions.md`.
- Delete disposable proof checks and verification logs after use.
