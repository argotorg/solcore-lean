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

The base contract theorems use an empty code catalog and no supplied code
image. The code-image theorem below removes those two restrictions. The public
connections require `deploying = false`; calls to other contracts and deployment
remain separate milestones.

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
their language-fault reasons. The code-image theorem below also connects `codesize` through the actual
code-slot initialization.

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


`ContractAccountCorrespondence.prepare_resumes_exact` adds `balance`,
`selfbalance`, `extcodesize`, `extcodecopy` and `extcodehash`. The actual
initializers establish the balance ledger and account world. Independent
account observations normalize target addresses, distinguish incomplete worlds
from missing code, copy code bytes into caller memory, and hash known code in
fresh scratch cells. Hashing preserves every existing caller cell.

`Tests.RustHullAccountCorrespondence.public_resumes` supplies nine source
cases, including unknown accounts, absent code, empty accounts and funded
accounts with empty code. Executable checks verify address normalization,
copying across a memory-word boundary, source zero padding, independent code
hashes, unchanged balances and caller memory, and repeated resumptions.


`ContractCodeCorrespondence.compileObject_resumes_exact` accepts supplied code
images and arbitrary successfully compiled catalogs. It connects `codesize`,
`codecopy` and `datacopy` to actual `compileObject`, object instantiation,
`runWithReceipt` and `resumeWithReceipt`. Actual catalog compilation supplies
all closures and their packet positions. The frame initializer supplies the
extra code cells and their values; the entry derivation needs no assumption
about evaluation of compiled catalog bodies.

The theorem applies when a code image is supplied or the catalog is nonempty,
which is exactly when the compiler installs code slots. A supplied empty image
has size zero and copies zero padding. An absent image with a nonempty catalog
keeps its unavailable-code fault. Catalog installation is covered here; the child-call theorem below also
connects execution of selected catalog entries.


`Tests.RustHullCodeImageCorrespondence.public_resumes` supplies nine independent
source derivations. They cover both copy names, code-size observations, known
empty and unavailable images, nonempty catalogs, copies across memory words,
zero padding, range overflow and zero-length ranges at the largest address.
Runtime checks compare public receipts and retained Core snapshots after
multiple resumptions.

`ContractReturnDataCorrespondence.compileObject_resumes_exact` connects
`returndatacopy` and `memoryguard` through actual compilation, initialization
and public resumptions. It covers both layouts, with and without code slots,
and `prepare_resumes_exact` covers the default preparation path. Return-data
contents and size are mutable resources, ready for call responses.

`Tests.RustHullReturnDataCorrespondence.public_resumes` supplies six source
derivations combining storage, logs, account observations, optional code copies
and return-data operations. They cover empty copies and both source-range
checks, including invalid termination before destination overflow. Runtime
checks confirm public rollback and retained internal snapshots. Two additional
direct-copy cases cover nonempty return data across memory words and destination
overflow. `memoryguard` preserves its evaluated argument.

`ContractCallCorrespondence.compileObject_resumes_exact` connects ordinary and
static calls through actual compilation, installed callbacks, caller transport,
account dispatch and public resumptions. `prepare_resumes_exact` covers the
default preparation path. Callback closures and their captured shared references
come from the real allocator; callback correctness is proved from their bodies.

This first call theorem covers absent target accounts, balance transfers,
insufficient funds, transfer overflow, incomplete world information, static-value
rejection, gas-stipend overflow and caller memory-range checks. Caller memory,
complete return data, balances, storage and logs remain in one state relation.
Dispatch faults execute the actual checkpoint restoration before message
completion applies its own commit or rollback rules.

The source effect instance uses `noChildren`: an absent account in a complete
world can succeed, but executing a compiled child is outside this instance.
Explicitly stored empty-code accounts also need a further code-identity proof.
`effectsWith` accepts the source child relation used by the later finite-height
connection below to supply recursive child derivations.

`Tests.RustHullCallCorrespondence.public_resumes` supplies independent source
derivations for nine scenarios: ordinary and static calls, a balance transfer,
insufficient funds, incomplete-world rollback, static-value rejection,
gas-stipend overflow, and both caller memory-range failures. Runtime consumers
check normal execution, interrupted execution followed by resumption, and the
retained Core snapshot, including storage, logs, balances and failed receipts.

`ContractChildCallCorrespondence.compileObject_resumes_exact` connects compiled
catalog children to the same public runner. The source catalog selects Hull
programs and bodies independently. Actual catalog compilation supplies the
closures and their indices; actual initial-world construction supplies their
executable identities. The public assumptions concern source evaluation,
syntactic eligibility, catalog selection and initial account code. They do not
assume a Core evaluation or callback correctness.

The child allocator supplies fresh memory, return data, message observations,
gas and code cells, while reusing the current world, balances and logs. Captured
ambient references remain available after intervening parent effects. Actual
child completion extracts returned bytes, and account dispatch either commits
the shared changes or restores its checkpoint. The proof preserves the parent's
local cells throughout child execution and return-data extraction.

This theorem permits arbitrary successfully compiled catalogs with the stated
source-to-catalog correspondence. Selected children use the established effect
language without further external calls (`CallFree`). Nested calls are covered by the finite-height theorem below. Root reentry
remains outside these instances; the mode theorem below covers CALLCODE and
DELEGATECALL. Identity, SHA-256 and RIPEMD-160 precompile calls are covered as described below.

`Tests.RustHullChildCallCorrespondence.public_resumes` supplies four independent
source derivations: a child returns after memory, storage, transient storage and
log writes; the child reverts with return data; it exits invalid; or a static
call rejects its storage write. The parent writes storage, memory and a log
before calling, then observes call status, full return-data size and the copied
byte. Runtime consumers check public receipts, two resumptions, shared rollback,
parent-local preservation and transaction finalization.

`ContractNestedChildCallCorrespondence.compileObject_resumes_exact` extends the
connection to any finite-height source call tree. Each child can make ordinary
or static calls through the same actual dispatcher. The induction uses a
strictly smaller source height for each executed child; it does not bound Core
fuel or replace a deeper source execution with a failure.

Nested frame initialization supplies each child's handler and call depth. The
proof retains the dispatcher cell alongside ambient and creator cells, refreshes
shared values before each child allocation, and derives callback execution from
the smaller-height theorem. The public statement has no callback-correctness or
Core-evaluation premise. Its initial code-link conditions still select nonroot
catalog entries; root reentry remains a separate connection.

`Tests.RustHullNestedChildCallCorrespondence.public_resumes` covers parent,
child and grandchild frames with distinct memory contents, storage locations
and logs. Its three source derivations cover all frames succeeding, a reverted
grandchild followed by a successful child, and a successful grandchild whose
changes are subsequently rolled back by the child's revert. Runtime checks also
cover returned bytes, retained parent and child memory, and repeated resumptions.

`ContractCallModeCorrespondence.compileObject_resumes_exact` connects all four
message-call operations through the same finite-height construction. CALLCODE
and DELEGATECALL select code by the requested target but execute against the
invoking frame's address and storage. CALLCODE supplies the explicit value and
current address as caller; DELEGATECALL inherits the caller and call value.
Neither mode transfers balances. Their concrete handler closures come from the
actual frame allocator, and every nested call retains those captures.

The mode consumers cover CALLCODE success, DELEGATECALL success and a reverting
DELEGATECALL. They compare the independent source result with public receipts,
including execution address, caller, value, storage, logs, return bytes and
balance preservation. The rollback case retains the parent's earlier changes.

The same public theorem includes `selfdestruct`. Its independent account
semantics distinguishes existing accounts from accounts created during the
current transaction. It checks beneficiary balance overflow before committing
updates, transfers or burns the balance as appropriate, and records pending
removal without changing code, nonce or storage during execution. Actual public
transaction finalization removes only the accounts scheduled for removal.
Static rejection and lifecycle faults preserve the corresponding source result.
Catalog identities remain valid while nested frames execute; no assumption that
scheduled accounts survive finalization is added to the public theorem.

Three concrete consumers cover an existing account, an account created during
the transaction, and parent rollback after a successful child destruction.
They connect source derivations to actual compilation and public resumptions,
including beneficiary balances, storage, logs and code visibility before
transaction finalization.

Root reentry is also connected. The actual entry compilation and captured
closure supply code identity 1, alongside ordinary catalog entries. Finite
source call trees determine each reentrant frame's execution; the public
theorem does not assume that the Core child executes correctly. Initial root
code links follow from the accepted compilation, supplied root image and
context. This connection covers ordinary execution contexts; deployment is
still a separate obligation.

Two concrete consumers cover successful root reentry and parent rollback.
They check fresh child calldata and memory, retained parent memory, shared
storage, return bytes and repeated public resumptions. Their public proofs
require only actual compilation success.

The identity precompile is connected through the same account dispatch. Its
independent rule, `AccountCallSemantics.Precompile`, applies to address 4. It
charges 15 gas plus 3 per started input word, computed over natural numbers and
compared with the forwarded gas. A funded call returns a byte copy of the
complete input, specified by `MemoryCopySemantics.Copy`. Forwarded gas below
the charge fails the call without return data, and an unaddressable input range
is a memory fault. `Run.precompile` adds this rule to dispatch without changing
shared state. Value transfer and checkpoint rules are those of ordinary
dispatch, so a false response or a fault restores the transferred balances.

The proof reaches the actual `AccountRuntime.dispatch`, its precompile wrapper
and `Precompiles.staticCall`. The identity branch runs the actual copy loop into
fresh result memory, publishes the return data and copies the empty output
range. Both implementation files keep these builders private.
`PrecompileCorrespondence.staticCall_shape` and
`AccountCallCorrespondence.dispatch_precompile_eq` restate them with public
builders and prove each restatement by `rfl`; the other precompile branches stay
opaque. The public call theorems for child-free calls, compiled children,
finite nested children, call modes and root reentry keep their statements.
Their source semantics now includes identity calls.

`Tests.RustHullPrecompileCorrespondence.public_resumes` supplies four independent
source derivations: a funded identity call whose output is copied into caller
memory, an underfunded call, a value transfer to address 4 and a static call.
`Tests.RustHullPrecompileCorrespondence.Modes.public_resumes` applies the
call-mode theorem to CALLCODE with value and to DELEGATECALL; neither moves
balances. Runtime checks compare returned bytes, committed balances, repeated
resumptions and the retained Core snapshot.

SHA-256, at address 2, uses the same dispatch path, and the same public call
theorems cover it without statement changes. `Sha256Semantics` specifies
FIPS 180-4 independently: the message schedule, 64 rounds and chaining
addition, big-endian word reads, and padding with the 0x80 marker, zero bytes
and the 64-bit bit length, including the extra block when the marker leaves no
room. The rule charges 60 gas plus 12 per started input word and returns the
32-byte digest. The proof reaches the actual `Sha256.hash` and its
`HashBlocks` streaming helper, restated by `rfl` in `Sha256Implementation`,
through the actual precompile branch, its fresh source memory and the
return-data mapping.

RIPEMD-160, at address 3, follows the same path. `Ripemd160Semantics` is
written from the designers' definition: both 80-step lines with their word
selections, rotations, constants and round functions, the final combination
with the chaining words, little-endian message words and bit length, and the
20-byte digest left-padded to 32 bytes. Its NOT is a 32-bit complement. The
implementation complements all 256 bits; the proof shows that the two round
functions agree modulo 2^32, which is all the enclosing sums observe. The rule
charges 600 gas plus 120 per started input word. The proof reaches the actual
`Ripemd160.hash`, restated by `rfl` in `Ripemd160Implementation`, through the
same precompile branch and shared block-streaming lemmas.

`Tests.RustHullPrecompileCorrespondence.Digest` hashes "abc" from caller memory
with each digest and copies the result back, and also covers underfunded
calls. Kernel evaluation checks both independent digests against the published
test vectors, and runtime checks compare the returned bytes.

ECRECOVER and P256VERIFY have no source rule, so the public theorems state
nothing about calls to them. An independent specification would use the
affine group law over F_p, but the implementations compute in Jacobian
coordinates (madd-2004-hmv with dbl-2009-l, or dbl-2001-b for P-256's a = -3).
They take inverses and square roots by Fermat exponentiation and combine
256-round joint double-and-add with Shamir's trick. Connecting them needs, for
each curve: modular field arithmetic with inverse correctness (Fermat requires
primality of p and n, or an extended Euclid argument); polynomial identities
showing that each Jacobian formula, including the doubling, opposite-point and
infinity cases, represents the affine result; and the joint ladder's equality
with scalar multiplication. ECRECOVER also needs square roots through
(p + 1) / 4 with the quadratic-residue check, and the connected Keccak address
derivation. The repository has no algebra library for these identities, so
neither curve fits in one connected unit.

`CreationSemantics.Refused` specifies, independently of Core, the CREATE and
CREATE2 attempts that are refused before any init code runs. The checks run
in the order of the actual lowering. A static frame, or init code longer than
EIP-3860's 49,152 bytes, halts the frame exceptionally without expanding
memory. Without a gas observation the attempt is language fault 9, and an
unaddressable init range is a memory fault that keeps the previous return
data. At the depth limit (a frame at depth 1024), with an endowment above the
creator's balance, or with a creator nonce of at least EIP-2681's 2^64 − 1, the
attempt returns zero. Memory then covers the init range and return data is
empty; balances, accounts, logs and the creator nonce are unchanged. Only
admitted attempts advance the nonce.

`RuntimeCallModeSemantics.Builtin` gains `create` and `create2` constructors
for these rules, and both names join the call-mode `supported` predicates.
The public call-mode and root-reentry theorems keep their statements. Their
source semantics now includes refused creation attempts, both in the outermost
frame and in every compiled child frame. The child-free, compiled-child and
nested-child theorems use the earlier effect layer with CALL and STATICCALL
only, which has no creation rule.

The proof reaches the actual lowering, `Creation.invoke` and the funds and
nonce checks of `CreationRuntime.dispatch`. These modules keep their builders
private. `CreationImplementation` restates the CREATE lowering in `Effects`,
the invocation transport, the dispatcher and the create handler built by
`objectHandlers`, and proves each restatement by `rfl`; the dispatcher's
address derivation, checkpoint and installation form a separate `admitted`
remainder. `CreationCorrespondence.HandlerClosure` records the installed
closure, its captured shared references and its runtime installation; init
selection and the identification of a nonempty runtime image stay abstract.
`ModeHandlers` now carries this handler, its cell and its closure. The actual
frame allocator identifies each frame's create-handler slot with the installed
creator cell (`allocateFrameSlots_creates`), and a child frame receives the
cell's read through the call that starts it (`CreateHandler.context`).

`Tests.RustHullCreationCorrespondence.public_resumes` applies the call-mode
theorem to eight independent source scenarios: a static frame, oversized init
code for CREATE and CREATE2, missing gas, an unaddressable init range,
insufficient endowments for CREATE and CREATE2, and an exhausted nonce.
Runtime checks compare receipts, balances, the creator nonce and a
resumption. The depth refusal has no public consumer, because it needs a frame
at depth 1024 and the outermost frame has depth zero; `Tests.RustHullCreation`
checks the depth branch of the actual transport at runtime.

`CreationSemantics.Admitted` specifies admitted attempts that run no init
frame. Such an attempt passes every refusal check, copies its init bytes from
memory, advances the creator nonce and derives the new address with
`CreationAddressSemantics`. CREATE hashes the RLP list of the creator address
and its nonce; CREATE2 hashes 0xff, the creator address, the salt and the
Keccak-256 of the copied init bytes. RLP follows appendix B of the Yellow
Paper, and Keccak-256 of a byte string is the connected `KeccakSemantics`
absorption of the bytes stored from address zero. Following EIP-684, an
account with a nonzero nonce or code size at the address is a collision: the
attempt returns zero and keeps the advanced nonce, for init code of any
length. An address absent from a complete world receives a new account with
nonce one and the endowment. With empty init code no init frame runs, the
deployed code is empty and the attempt returns the address; the EVM runs an
empty init frame here, which has no effect the model observes. An unknown
account at the address, absent from an incomplete world or recorded with a
zero nonce and unknown code, is language fault 7, and an endowment that would
overflow the new account's balance is language fault 12. Both faults restore
the checkpoint taken after the nonce advance: only the advanced nonce remains,
and memory and return data are as for a refusal.
`RuntimeCallModeSemantics.Builtin` gains `createAdmitted` and
`create2Admitted`, and the call-mode and root-reentry public theorems keep
their statements.

The proof connects the actual `admitted` remainder of the dispatcher.
`CreationImplementation` also restates `Creation.createAddress`,
`Creation.create2Address` and the runtime installation of `objectHandlers` by
`rfl`. The address builders write their preimages into fresh scratch cells
with the actual `mstore8` and `mstore` and hash them with the connected
Keccak. `CreationBytes` proves byte reads of source memory after byte and word
writes at any alignment, and that Keccak absorption reads only the absorbed
bytes; `CreationPreimage` shows that the scratch bytes are the specified
preimages, so the masked digest is the specified address. The nonce write,
checkpoint loads, collision checks, record insertion, endowment, empty-init
validation and installation are evaluated against `StorageCorrespondence`, and
catalog code links survive every outcome. For the faults, the protection
around the attempt and the checkpoint's restoration code are evaluated
(`CreationCorrespondence.restoreCode_evaluates`, `protect_failed`,
`attempt_restored`): the restoration writes back the world after the nonce
advance and the balances and logs that the checkpoint loaded. The transport
publishes the handler's account and balance changes through
`transport_updated`; a fault is returned without publishing return data,
which stays cleared (`invoke_failed`).

`Tests.RustHullCreationAdmittedCorrespondence.public_resumes` applies the
call-mode theorem to four independent source scenarios: CREATE and CREATE2
deployments of empty init code, one with an endowment, and CREATE and CREATE2
collisions with an account of nonzero nonce and with one that has code. The
kernel evaluates the derived addresses. Runtime checks compare the returned
address, balances, the advanced creator nonce and the new account.
`Tests.RustHullCreationAddressVectors` derives the 11 recorded CREATE and
CREATE2 address vectors from the specification in the kernel, covering every
RLP nonce encoding and EIP-2681's largest nonce.

`Tests.RustHullCreationFaultCorrespondence.public_resumes` applies the
call-mode theorem to four independent source scenarios: a CREATE target absent
from an incomplete world, a CREATE2 target recorded with a zero nonce and
unknown code, and CREATE and CREATE2 endowments that would overflow a target
holding the largest balance. Runtime checks compare the language failure
reasons of a full run and of a resumption; failure receipts carry no world.

Admitted attempts not yet described: nonempty init code, whose init frame runs
in a deployment context; and an existing account at the address with zero
nonce and known empty code, because a catalog link for empty bytes at that
address could not survive installation, which records identity zero.

Hull's explicit `revert` statement is connected through the call-mode and
root-reentry public theorems. `RevertSemantics.Reverted` specifies it
independently of the lowering: the message holds at most 32 UTF-8 bytes, their
big-endian value left-aligned in one word is stored at memory offset zero with
the `mstore` semantics, and the frame terminates with revert exit 2 over
exactly the message bytes. The compiler rejects longer messages, as the pinned
Yul backend does. The call-mode effects use this rule at every frame height.
`ExecutableStatement` accepts the statement wherever the `revert` builtin is
supported, and the common recursive proof discharges it through a separate
obligation, `RevertPreservation`. Effect layers without a revert rule meet the
obligation vacuously, and `assemble_recursive_program_effects` supplies that
case by default, so only the call-mode layer gives a proof. The other layers'
theorems therefore admit programs with an explicit revert but say nothing about
a run that reaches one. No public theorem statement changes.

The proof (`RevertBuiltinCorrespondence.preserves`) connects the actual
`Effects.revertMessage` code. The word the lowering computes is the specified
left-aligned word, the actual `mstore` code writes it, and the actual revert
termination records the exit registers over the message range. The frame,
linked world and captured context relations carry over as for the static-frame
termination.

`Tests.RustHullRevertCorrespondence.public_resumes` applies the call-mode
theorem to four independent source scenarios: a short message, an empty
message, a full 32-byte message, and a short message written over an earlier
word at offset zero. Runtime checks compare the revert bytes of a full run and
of a resumption.

Inline Yul is connected for a first fragment through the call-mode and
root-reentry public theorems. `YulSemantics` specifies an assembly block of one
statement that calls `mstore`, `mstore8`, `return` or `revert` on two literal
words. Number and hexadecimal literals denote words as Hull word literals do,
and `true` and `false` denote one and zero. The arguments are evaluated from
right to left, as in Yul; literals have no effect, so the fragment cannot
observe the order. The call is the independent memory write or termination on
the frame: a returning call continues after the block, and a fault, including
the termination sentinel, stops it. The call-mode effects use this rule at
every frame height. `ExecutableStatement` accepts an assembly block when
`YulFragment.Eligible` holds, that is, one call statement on two literals
whose name is supported. The common recursive proof discharges it through a
separate obligation, `AssemblyPreservation`, which
`assemble_recursive_program_effects` meets by default for the effect layers
without an assembly rule. The other layers' theorems therefore admit programs
with such a block but say nothing about a run that reaches one. No public
theorem statement changes.

The proof (`YulBuiltinCorrespondence.preserves`) connects the actual
`YulLowering.lowerStatements` code. `YulLowering` keeps its builders private
and mutually recursive, and a public copy is not equal to them by `rfl`, so
the proof instead peels the accepted lowering of the fixed block shape with
`change`, which unfolds the private definitions definitionally. The lowering
binds the second literal and then the first, its words agree with the source
literals, and the actual `mstore`, `mstore8` and termination code run on them.
The frame, linked world and captured context relations carry over as for the
explicit revert.

`Tests.RustHullAssemblyCorrespondence.public_resumes` applies the call-mode
theorem to four independent source scenarios, each writing memory in one block
and ending the frame in another: an `mstore` returned as a word, an `mstore8`
of a hexadecimal byte, an `mstore` whose last byte is reverted, and an
`mstore` of `true` whose last byte is returned. Runtime checks compare the
returned or reverted bytes of a full run and of a resumption.

## Priorities

| Priority | Theorem / connection | Completion evidence | Status |
| --- | --- | --- | --- |
| 1 | Product-path assignment preserves the result and heap, including failed RHS calls. | The common recursive public theorem covers nested places; source/public/runtime consumers cover successful writes and faults. | Connected |
| 1 | Pattern matching preserves arm selection, binder allocation and control outcomes. | Actual `testPattern` and `lowerAlternatives` feed the mutual derivation proof and public resumptions, including skipped arms and faults. | Connected |
| 2 | Accepted initialization and execution exclude malformed source observations. | Actual globals, parameter binding, locals and match binders supply scope coverage; compiler checks and typed heaps exclude malformed observations. The public theorem has no outcome-safety premise. | Connected |
| 3 | Concrete external state is preserved. | Memory, storage, environment reads, logs, explicit termination, memory copying, hashing, account observations, linked code images and return data reach public receipts and resumptions; further state operations remain. | In progress |
| 4 | External calls, creation and rollback preserve observable outcomes. | All four message-call operations, root reentry, the identity, SHA-256 and RIPEMD-160 precompiles, account destruction, refused CREATE/CREATE2 attempts and admitted attempts without an init frame reach public receipts, including finite nested children, transfers, return data, checkpoint rollback, new accounts and transaction finalization. ECRECOVER, P256VERIFY and creation with init frames remain. | In progress |
| 4 | Assembly preserves its independent meaning. | Yul statement derivations connect to actual lowering and public execution, reusing the concrete effect relations. One-call blocks of memory writes and terminations on literals are connected; several statements, variables, assignments, nested calls, control flow, local functions and Hull locals remain. | In progress |
| 5 | Divergence and reverse correspondence. | Relate nontermination and characterize Core outcomes after terminating execution and effects are covered. | Open |

Priorities 1 and 2 close gaps in the existing pure Hull theorem. Priorities 3
and 4 connect the remaining observable runtime behavior. Priority 5 should not
delay those connections.

## Deferred public proof work

The bounded [M0–M6 differential-testing milestones](semantic-differential-testing.md)
are complete. They did not require completion of every remaining Hull proof
and do not discharge those obligations. The
[next implementation roadmap](next-implementation-roadmap.md) prioritizes
continuous bounded campaigns, backend and grammar coverage, and the native
Source public proof connection before this remaining Hull work.

The identity, SHA-256 and RIPEMD-160 precompiles are connected through their
independent gas, byte-copy and digest semantics, actual dispatch and public
execution. ECRECOVER and P256VERIFY still need independent elliptic-curve
semantics connected to their Jacobian implementations; the missing pieces are
listed with the precompile connection above. Creation attempts refused before
init code runs, collisions, deployments of empty init code and the faults
after the nonce advance are connected, and so are Hull's explicit revert and
one-call inline Yul blocks; creation with init frames and the rest of assembly
follow as their proof domains are connected. Each proof step must derive
runtime inputs from actual initialization and end in a public theorem
consumer. Executable support and test agreement alone do not close these
obligations.

## Remaining public connections

`call` and `staticcall` have public connections for calls without child execution,
finite nested compiled children, root reentry and the identity, SHA-256 and
RIPEMD-160 precompiles. The elliptic-curve precompile branches remain.
`create` and `create2` are connected for refusals, collisions, deployments
of empty init code, unknown targets and endowment overflow. CALLCODE and
DELEGATECALL are covered by the same finite nested-child connection.

| Order | Connection | Required public evidence |
| --- | --- | --- |
| 1 | Contract calls | Connect ECRECOVER (1) and P256VERIFY (0x100) through independent affine elliptic-curve semantics, with field arithmetic, Jacobian-formula identities and ladder correctness. Reuse the connected dispatch, Keccak, checkpoint restoration and public resumptions. |
| 2 | Contract creation | Connect init frames: nonempty init code at the next depth in a deployment context, runtime-code validation, installation of the exact image and failure rollback. Their source rule needs an init-template catalog, which changes the public theorem statements. Also connect existing empty accounts at the address. Refusals, collisions, empty init code, unknown targets and endowment overflow are connected. |
| 3 | Assembly and source revert | Extend the connected Yul fragment, one call on two literals, to independent Yul evaluation with its argument order: several statements, variables and assignments, nested calls, control flow, local functions and Hull locals. Hull's string revert is connected through its memory write and termination. |
| 4 | Object linking | Prove the `datasize` / `dataoffset` substitutions and connect `LinkedContract` preparation to execution. The current code-image theorem starts with supplied images. |

Creation's refusals, collisions, deployments of empty init code and the two
faults after the nonce advance are connected (see above). Init frames remain.
Their source rule must run nonempty init code at the next depth in a
deployment context, with empty calldata and the init bytes as code; validate
the returned runtime code (24,576 bytes and no 0xef prefix) and install the
exact image; and roll back accounts, balances and logs to the post-nonce
checkpoint when the init frame fails, with its revert bytes as return data.

The proof must connect the actual `runInit` and the identification step of
`CreationImplementation.installWith`, which `HandlerClosure` keeps abstract:
init-template selection by image comparison over the catalog's init entries,
the child init frame through the finite-height catalog induction with a
deployment-context allocation, the child result conversion, and runtime-image
identification. The checkpoint's restoration is evaluated for the faults after
the nonce advance (`CreationCorrespondence.restoreCode_evaluates`,
`protect_failed`, `attempt_restored`), so init-frame failures can reuse it.
Public deployment also needs the theorems' `deploying = false` premise lifted
through `finishDeployment`. Creation over an existing empty account needs
catalog links for empty bytes excluded at the address, or installation to keep
their identity.

Init frames cannot be connected under the current public theorem statements.
The call-mode and root-reentry theorems fix the source effects to
`ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image`, whose
catalog is keyed by account address, and their catalog connections relate its
entries only to the root code or to compiled runtime definitions with code
anchors. The actual `runInit` selects an init template by comparing the init
bytes with the catalog's `isInit` definitions, which no source entry or
premise describes. The source rule therefore needs an init-template catalog
keyed by init bytes, and the public theorems need a premise connecting its
entries to the compiled `isInit` definitions.

Larger Yul fragments keep the same public statements and the same assembly
obligation, but their proof needs the lowering of statement lists of any
length. The private recursive builders of `YulLowering` (`lowerSequence`,
`lowerBlock`, `lowerExpr`) unfold definitionally only on lists of known shape,
and a public copy is not provably equal to them by `rfl`. A general proof
therefore needs those builders made public, or a way for the proof to refer to
the private constants; with either, an induction over the statements can
follow the peeling of the one-call block.

Lower-level helpers or isolated builtin results do not complete any row without
its actual public execution consumer.

## Verification

- Build the affected theorem modules and the full test executable.
- Run independent-source public consumers and the complete test suite.
- Check the semantic-kernel declaration policy and the public theorem's axioms.
- Record actual ambiguities or upstream bugs in the ignored `questions.md`.
- Delete disposable proof checks and verification logs after use.
