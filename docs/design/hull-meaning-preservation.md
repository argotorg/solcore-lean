# Hull meaning preservation

Updated: 2026-11-17. These theorems connect independent finite evaluations of imported Hull to the
Rust Hull importer's actual lowering, initialization and public execution, including repeated
resumptions. This note gives the rule for when a feature counts as connected, the public theorems
as they are now, their status, and what each remaining connection needs.

## Completion rule

A feature is connected when its independent `Semantics` derivation reaches the actual `compile` /
`ScalarExecution.prepare` implementation and the public `run` / `resume` API. Its theorem must
relate the result, the language-fault reason and the represented source heap. Compiler output,
function installation, argument initialization and loop closures must come from the
implementation, not from an assumed body-preservation premise.

Helper lemmas count as intermediate work. Each step ends with a public theorem consumer, an
executable regression, verification and a commit. Executable support and test agreement alone do
not close an obligation.

## Functions

`Correspondence.prepare_recursive_program_resumes` relates every genuine finite chain of
resumptions to an independent finite Hull function evaluation. It preserves values and language
faults, including all allocations and writes made before failure. Completion occurs exactly when
the cumulative fuel reaches the transition count; otherwise the computation remains resumable.

- **Premises:** successful preparation, `RecursiveProgram` syntactic eligibility and a finite
  independent source evaluation. Any source result is accepted: its value representation and the
  exclusion of malformed source observations follow from the proof. Actual compilation and
  initialization establish scope coverage, parameter arity and the typed heap relation, and
  successful builtin compilation supplies the argument constraints. There is no separate
  outcome-safety premise.
- **Inputs and effects.** Public inputs use the existing scalar parser. The theorem does not assert
  termination or specify concrete external effects.
- **Fragment:** structural values, pure builtins, recursive named calls, local variables, blocks,
  loops and control transfers, product-path assignments and pattern alternatives. Language faults
  propagate through expressions, argument evaluation, function boundaries and every loop stage.

## Contract state

Each theorem below connects an independent Hull evaluation to the actual `Contract.prepare` (or
`compileObject`), `runWithReceipt` and any genuine chain of `resumeWithReceipt` calls. Successful
compilation and the independent derivation establish the whole Core evaluation. Runtime references,
initial memory, captured frame closures and snapshot observations come from the actual object
initialization. Each theorem has a consumer, such as
`Tests.RustHullMemoryCorrespondence.public_resumes`, that applies it to independent source
derivations, with runtime checks of receipts and snapshots.

| Theorem | Adds | What it preserves |
| --- | --- | --- |
| `ContractMemoryCorrespondence.prepare_resumes_exact` | `mload`, `mstore`, `mstore8` and `msize`, with pure operations, recursive calls, loops and language faults | The final memory, writes before failure included. The public result is the actual receipt decoder applied to the source-derived message value, so export limits and cumulative fuel keep their public behavior. |
| `ContractRuntimeEffectsCorrespondence.prepare_resumes_exact` | `sload`, `sstore`, `tload` and `tstore`, interleaved with memory | The actual allocator gives every memory and storage register a distinct location. Static-write rejection, writes before faults and transaction finalization are covered. |
| `ContractEnvironmentCorrespondence.prepare_resumes_exact` | Address, caller, call value, calldata and return-data size, calldata word reads, supplied gas, ten optional ambient words, block hashes and blob hashes | The actual context normalization and initializers establish the observations, and memory and storage operations preserve them. Missing optional inputs keep their language-fault reasons. |
| `ContractLogCorrespondence.prepare_resumes_exact` | `log0` to `log4` | Emitter, topics and a copied payload. Static logging, capacity overflow and memory overflow keep their termination or fault behavior. |
| `ContractFullCorrespondence.prepare_resumes_exact` | `return`, `revert`, `stop` and `invalid` | The exit kind and returned range, memory expansion and overflow, and the message's commit or rollback. A termination stops the later statements. |
| `ContractCopyCorrespondence.prepare_resumes_exact` | `mcopy` and `calldatacopy` | Copies that overlap, word chunks and byte tails, source zero padding, address overflow, range checks before memory changes, and the resulting memory extent. |
| `ContractHashCorrespondence.prepare_resumes_exact` | `keccak256` | An independent algorithm (the lane permutation, 24 rounds, 136-byte blocks, Ethereum padding, the digest) reaching the actual Core permutation and absorption helper. Hashing expands only the touched range and leaves the input unchanged. |
| `ContractAccountCorrespondence.prepare_resumes_exact` | `balance`, `selfbalance`, `extcodesize`, `extcodecopy` and `extcodehash` | Normalized target addresses, incomplete worlds told apart from missing code, code bytes copied into caller memory, and known code hashed in fresh scratch cells that keep every caller cell. |
| `ContractCodeCorrespondence.compileObject_resumes_exact` | `codesize`, `codecopy` and `datacopy`, with supplied code images and any compiled catalog | Actual catalog compilation supplies the closures and their packet positions. It applies when an image is supplied or the catalog is nonempty, exactly when the compiler installs code slots. A supplied empty image has size zero; an absent image with a nonempty catalog keeps its fault. |
| `ContractReturnDataCorrespondence.compileObject_resumes_exact` | `returndatacopy` and `memoryguard` | Both layouts, with and without code slots; `prepare_resumes_exact` covers the default path. Return-data contents and size are mutable resources, ready for call responses. |

The base contract theorems use an empty code catalog and no supplied code image; the code-image
theorem removes both restrictions. The public connections require `deploying = false`.

## Calls

- **Child-free calls.** `ContractCallCorrespondence.compileObject_resumes_exact` connects ordinary
  and static calls through actual compilation, installed callbacks, caller transport, account
  dispatch and public resumptions; `prepare_resumes_exact` covers the default path. Callback
  closures come from the real allocator, and their correctness is proved from their bodies. It
  covers absent targets, balance transfers, insufficient funds, transfer overflow, incomplete world
  information, static-value rejection, gas-stipend overflow and caller memory-range checks, and
  dispatch faults run the actual checkpoint restoration. Its source effect instance uses
  `noChildren`, so executing a compiled child is outside it; explicitly stored empty-code accounts
  need a further code-identity proof. `effectsWith` takes the child relation that the
  finite-height connection supplies.
- **Compiled children.** `ContractChildCallCorrespondence.compileObject_resumes_exact` runs catalog
  children through the same public runner.
  - The source catalog selects Hull programs and bodies independently. Actual catalog compilation
    supplies the closures and indices, and the initial-world construction their identities. The
    assumptions concern source evaluation, syntactic eligibility, catalog selection and initial
    account code, not a Core evaluation or callback correctness.
  - Each child gets fresh memory, return data, message observations, gas and code cells and reuses
    the current world, balances and logs. The parent's local cells are preserved throughout.
  - Selected children use the effect language without further calls (`CallFree`).
- **Nested children.** `ContractNestedChildCallCorrespondence.compileObject_resumes_exact` covers
  any finite-height source call tree, by induction on a strictly smaller source height for each
  child. It does not bound Core fuel or replace a deeper execution with a failure. Its statement has
  no callback-correctness or Core-evaluation premise. Its initial code-link conditions select
  nonroot catalog entries.
- **Call modes.** `ContractCallModeCorrespondence.compileObject_resumes_exact` connects all four
  message-call operations through the same construction. CALLCODE and DELEGATECALL select code by
  the requested target but run against the invoking frame's address and storage. CALLCODE supplies
  the explicit value and the current address as caller; DELEGATECALL inherits the caller and the
  call value. Neither transfers balances. Their handler closures come from the actual frame
  allocator.
- **Account destruction.** The same theorem covers `selfdestruct`. Its account semantics tells
  existing accounts from accounts created during the transaction, checks beneficiary balance
  overflow before committing, transfers or burns the balance, and records pending removal without
  changing code, nonce or storage. Actual public finalization removes only the accounts scheduled
  for removal. No assumption that scheduled accounts survive finalization is added.
- **Root reentry** (`ContractRootCallCorrespondence`). The actual entry compilation and its captured
  closure supply code identity 1, beside the ordinary catalog entries. Finite source call trees
  determine each reentrant frame's execution, and the initial root code links follow from the
  accepted compilation, the supplied root image and the context. This covers ordinary execution
  contexts; deployment is a separate obligation.

## Precompiles

The identity (address 4), SHA-256 (address 2) and RIPEMD-160 (address 3) precompiles use the same
account dispatch. The public call theorems for child-free calls, compiled and nested children, call
modes and root reentry cover them without statement changes.

- **Identity.** `AccountCallSemantics.Precompile` charges 15 gas plus 3 per started input word,
  over natural numbers, against the forwarded gas. A funded call returns a byte copy of the input
  (`MemoryCopySemantics.Copy`). Forwarded gas below the charge fails the call without return data,
  and an unaddressable input range is a memory fault. `Run.precompile` adds the rule to dispatch;
  value transfer and checkpoints follow ordinary dispatch, so a false response or a fault restores
  the transferred balances.
- **SHA-256.** `Sha256Semantics` specifies FIPS 180-4 independently, padding and the extra block
  included. It charges 60 gas plus 12 per started input word and returns the 32-byte digest. The
  proof reaches the actual `Sha256.hash` and its `HashBlocks` streaming helper, restated by `rfl`
  in `Sha256Implementation`.
- **RIPEMD-160.** `Ripemd160Semantics` follows the designers' definition, with the 20-byte digest
  left-padded to 32 bytes. It charges 600 gas plus 120 per started input word. Its NOT is a 32-bit
  complement, while the implementation complements all 256 bits; the proof shows that the two
  round functions agree modulo 2^32, which is all the sums observe. The proof reaches the actual
  `Ripemd160.hash`, restated by `rfl` in `Ripemd160Implementation`, through the shared
  block-streaming lemmas.
- **The proof** reaches the actual `AccountRuntime.dispatch`, its precompile wrapper and
  `Precompiles.staticCall`, which the implementation keeps private:
  `PrecompileCorrespondence.staticCall_shape` and `AccountCallCorrespondence.dispatch_precompile_eq`
  restate them with public builders, by `rfl`, and the other precompile branches stay opaque. The
  identity branch runs the actual copy loop into fresh result memory.
- **ECRECOVER and P256VERIFY** have no source rule, so the public theorems say nothing about calls
  to them. An independent specification would use the affine group law over F_p, while the
  implementations compute in Jacobian coordinates (madd-2004-hmv with dbl-2009-l, or dbl-2001-b
  for P-256's a = -3), take inverses and square roots by Fermat exponentiation, and combine
  256-round joint double-and-add with Shamir's trick. Connecting them needs, for each curve:
  - modular field arithmetic with inverse correctness (Fermat requires the primality of p and n, or
    an extended Euclid argument);
  - polynomial identities showing that each Jacobian formula, the doubling, opposite-point and
    infinity cases included, represents the affine result;
  - the joint ladder's equality with scalar multiplication;
  - for ECRECOVER, square roots through (p + 1) / 4 with the quadratic-residue check, and the
    connected Keccak address derivation.

  The repository has no algebra library for these identities, so neither curve fits in one
  connected unit.

## Creation

- **Refused attempts** (`CreationSemantics.Refused`), checked in the actual lowering's order:
  - a static frame, or init code over EIP-3860's 49,152 bytes, halts the frame exceptionally
    without expanding memory;
  - without a gas observation the attempt is language fault 9, and an unaddressable init range is a
    memory fault that keeps the previous return data;
  - at the depth limit (a frame at depth 1024), with an endowment above the creator's balance, or
    with a creator nonce of at least EIP-2681's 2^64 − 1, the attempt returns zero. Memory then
    covers the init range and return data is empty; balances, accounts, logs and the creator nonce
    are unchanged. Only admitted attempts advance the nonce.
- **Admitted attempts without an init frame** (`CreationSemantics.Admitted`). The attempt copies its
  init bytes from memory, advances the creator nonce and derives the address
  (`CreationAddressSemantics`): CREATE from the RLP list of the creator and its nonce (Yellow Paper
  appendix B), CREATE2 from 0xff, the creator, the salt and the Keccak-256 of the init bytes,
  through the connected `KeccakSemantics`.
  - A nonzero nonce or code size at the address is a collision (EIP-684): the attempt returns zero
    and keeps the advanced nonce, for init code of any length.
  - An address absent from a complete world receives a new account with nonce one and the
    endowment. With empty init code no init frame runs, the deployed code is empty, and the address
    is returned; the EVM's empty init frame has no effect the model observes.
  - An unknown account at the address is language fault 7, and an endowment that would overflow the
    new account's balance is language fault 12. Both restore the checkpoint taken after the nonce
    advance.
- **Statements.** `RuntimeCallModeSemantics.Builtin` has `create` and `create2` for the refusals,
  both names in the call-mode `supported` predicates, and `createAdmitted` and `create2Admitted`
  for the admitted attempts. The call-mode and root-reentry public theorems keep their statements,
  and their source semantics includes refused attempts in the outermost frame and in every compiled
  child frame. The child-free, compiled-child and nested-child theorems use the effect layer with
  CALL and STATICCALL only, which has no creation rule.
- **The proof** reaches the actual lowering, `Creation.invoke`, the funds and nonce checks of
  `CreationRuntime.dispatch`, the address builders (`Creation.createAddress`,
  `Creation.create2Address`) and the installation, restated by `rfl` in `CreationImplementation`.
  `CreationBytes` proves byte reads of memory after writes at any alignment, and `CreationPreimage`
  that the scratch bytes are the specified preimages. For the faults, the checkpoint's restoration
  code is evaluated (`CreationCorrespondence.restoreCode_evaluates`, `protect_failed`,
  `attempt_restored`). `CreationCorrespondence.HandlerClosure` records the installed create
  handler; init selection and the identification of a nonempty runtime image stay abstract.
- **Consumers.** The depth refusal has no public consumer, since it needs a frame at depth 1024 and
  the outermost frame has depth zero; `Tests.RustHullCreation` checks the depth branch of the actual
  transport at runtime.
- **Not covered:** nonempty init code, whose init frame runs in a deployment context; and an
  existing account at the address with a zero nonce and known empty code, because a catalog link for
  empty bytes at that address could not survive installation, which records identity zero.

## Explicit revert

`RevertSemantics.Reverted` specifies Hull's `revert` statement independently of the lowering. The
message holds at most 32 UTF-8 bytes; their big-endian value, left-aligned in one word, is stored at
memory offset zero with the `mstore` semantics, and the frame terminates with revert exit 2 over
exactly the message bytes. The compiler rejects longer messages, as the pinned Yul backend does.

The call-mode effects use this rule at every frame height. The common recursive proof discharges it
through a separate obligation, `RevertPreservation`. Effect layers without a revert rule meet it
vacuously, by default through `assemble_recursive_program_effects`, so the other layers' theorems
admit programs with an explicit revert but say nothing about a run that reaches one.
`RevertBuiltinCorrespondence.preserves` connects the actual `Effects.revertMessage` code. No public
theorem statement changes.

## Inline Yul

`YulSemantics` specifies an assembly block as a list of statements: `let` with one name and an
optional value, assignment to one name, expression statements, nested blocks, `if` and `switch`.

- **Expressions** are literals, variables and calls of `mload`, `msize`, `mstore`, `mstore8`,
  `return` and `revert` and of the word operations `add`, `sub`, `lt`, `gt`, `eq` and `iszero`,
  nested to any depth. `add` and `sub` are modulo 2^256, the comparisons are unsigned, and the
  comparisons and `iszero` give one or zero. Literals denote words as Hull word literals do, and
  `true` and `false` denote one and zero.
- **Order.** A call evaluates its arguments from right to left, as in Yul, and the order is
  observable: `mstore(mload(32), msize())` takes the memory size before `mload(32)` expands memory.
- **Control.** An `if` runs its body when the condition word is nonzero. A `switch` runs the first
  case whose literal denotes the scrutinee word, or else its default; string case literals are
  outside the fragment. A fault, including the termination sentinel, stops the block, also from a
  nested body.
- **Locals.** Yul locals are Hull heap cells whose scope ends with their block or body. A variable
  may also name a Hull word local, which the block reads and assigns in place.
- **Eligibility.** `ExecutableStatement` accepts a block when `YulFragment.Eligible` holds: every
  statement, nested bodies included, has one of these forms, every call names a supported builtin
  or one of the six word operations, and the layer supports some name. Calls of other supported
  names are eligible, but `YulSemantics` gives them no rule,
  so the theorems say nothing about a run that reaches one. The common proof discharges a block
  through `AssemblyPreservation`, which layers without an assembly rule meet by default. No public
  theorem statement changes.
- **The proof** (`YulBlockCorrespondence`) follows the source derivation through the actual
  `YulLowering` builders, by mutual induction over expressions and argument lists, and over
  statements with `YulSemantics.Compound` for nested blocks, `if` and `switch`. The effect builtins
  go through the frame model's `BuiltinStep`, which `YulBuiltinCorrespondence.step` meets. The word
  operations compile with `RustYulPrimitives.compile` to pure Core operations, which
  `primitive_step` proves once for every effect model. `lowerSequence`, `lowerBlock`,
  `lowerFunction`, `lowerExpr` and their helpers are public for the proof, a visibility-only change;
  `validateControl`, `decodeChars` and `stringWord` stay private.

## The init-template catalog in the public statements

The call-mode and root-reentry theorems fixed their source effects to
`ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image`, whose catalog is keyed by
account address. The actual `runInit` instead selects an init template by comparing the init bytes
with the catalog's `isInit` definitions, which no source entry or premise described.
`ChildFrameSemantics.InitCatalog` now holds the init templates, source codes keyed by the bytes
that begin an init code, and the runtime images a deployment may install, and `effectsAt` takes it
as its second argument.

Exactly these changes were made, the same in `compileObject_preserves` and
`compileObject_resumes_exact` of `ContractCallModeCorrespondence` and of
`ContractRootCallCorrespondence`:

- a new implicit argument `initCatalog : ChildFrameSemantics.InitCatalog`;
- in the premise `evaluated`, the source effects
  `ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog (height + 1) image` (root reentry:
  `(some rootBytes)` for `image`) in place of
  `ChildFrameModeSemantics.effectsAt sourceCatalog (height + 1) image`;
- a new explicit premise after `connection`:
  `initConnection : InitCatalogCorrespondence.InitCatalogConnection initCatalog image catalog`
  (root reentry: `(some rootBytes)` for `image`).

`InitCatalogConnection` states that the templates are the compiled init definitions in catalog order
(`initDefinitions catalog`, the list the actual `runInit` filters), each with the same program,
object and init bytes and with executable functions; that every runtime image is one the actual
installation identifies (`runtimeImages image catalog`: the root image and the catalog entries that
are not init definitions); and that `catalog.length + 2 < wordModulus`, so the entry identities
`index + 2` are distinct words. No other premise, argument or conclusion changed. No source rule
reads the catalog yet, so the theorems still say nothing about a run that reaches an init frame.
Every existing consumer passes the empty catalog `{}` and discharges the premise with
`InitCatalogConnection.empty`; none was removed or weakened.

## Status

| Priority | Connection | Status |
| --- | --- | --- |
| 1 | Product-path assignment preserves the result and heap, including failed right-hand-side calls; pattern matching preserves arm selection, binder allocation and control outcomes. | Connected |
| 2 | Accepted initialization and execution exclude malformed source observations: actual globals, parameter binding, locals and match binders supply scope coverage, and the public theorem has no outcome-safety premise. | Connected |
| 3 | Concrete external state: memory, storage, environment reads, logs, explicit termination, memory copying, hashing, account observations, linked code images and return data are connected; further state operations remain. | In progress |
| 4 | External calls, creation and rollback: all four call operations, root reentry, three precompiles, account destruction, refused creation and admitted creation without an init frame are connected; ECRECOVER, P256VERIFY and creation with init frames remain. | In progress |
| 4 | Assembly: the inline Yul fragment above is connected; `for` with `break` and `continue`, local functions, multi-name `let` and assignment, string literals and other builtins remain. | In progress |
| 5 | Divergence and reverse correspondence: relate nontermination, and characterize Core outcomes once terminating execution and effects are covered. | Open |

Priorities 1 and 2 close gaps in the pure Hull theorem, and 3 and 4 connect the remaining
observable runtime behavior. Priority 5 should not delay those connections. The bounded
differential-testing milestones did not need these proofs and do not discharge them; the
[roadmap](next-implementation-roadmap.md) orders this work.

## Remaining public connections

| Order | Connection | Required public evidence |
| --- | --- | --- |
| 1 | Contract calls | Connect ECRECOVER (1) and P256VERIFY (0x100) through independent affine elliptic-curve semantics, with field arithmetic, Jacobian-formula identities and ladder correctness. Reuse the connected dispatch, Keccak, checkpoint restoration and public resumptions. |
| 2 | Contract creation | Connect init frames: nonempty init code at the next depth in a deployment context, runtime-code validation, installation of the exact image and failure rollback. The init-frame source rule and its proof remain. Also connect public deployment through `finishDeployment`, and existing empty accounts at the address. |
| 3 | Assembly | Extend the inline Yul fragment to `for` with `break` and `continue`, local functions and `leave`, multi-name `let` and assignment, string literals and the other builtins. |
| 4 | Object linking | Prove the `datasize` / `dataoffset` substitutions and connect `LinkedContract` preparation to execution. The current code-image theorem starts with supplied images. |

**Init frames.** Their source rule must run nonempty init code at the next depth in a deployment
context, with empty calldata and the init bytes as code; validate the returned runtime code (24,576
bytes and no 0xef prefix) and install the exact image; and roll back accounts, balances and logs to
the post-nonce checkpoint when the init frame fails, with its revert bytes as return data. The proof
must connect the actual `runInit`, which is a local definition of `AccountRuntime.objectHandlers`,
and the identification step of `CreationImplementation.installWith`; `HandlerClosure` keeps both
abstract.
The pieces, in the order the dispatcher runs them:

- **Template selection.** `runInit` compares the init bytes with each definition of
  `initDefinitions catalog` through `ImageComparison.compareBytes` with a suffix allowed, takes
  identity `index + 2` for the first match, and fails with 16 when no template or a second template
  matches. `compareBytes` is a one-pass bitmap comparison over the packed memory mapping with no
  evaluation lemma yet.
- **The child init frame.** The selected closure runs through `invoke` at the next depth with the
  packet `[target, creator, value, false, depth, gas, empty calldata, 0]` and the init code as code.
  `ModeChildCatalogExecutionCorrespondence.FrameExecution` already concludes with exactly this
  `invoke` shape, so the init frame can reuse the finite-height catalog induction once the creation
  cases of `external_preserves` take an init-frame callback, as CALL takes `callbacks`. `invoke`
  receives the copied init entries, while `FrameExecution` expects `Memory.packBytes` of the code
  bytes, so the two representations need a bridge.
- **The child result.** `AccountRuntime.childResult` converts the init frame's exit, and
  `FrameExecution` already relates it to the source response.
- **Validation.** The deployment reads the returned size and the first byte of the returned memory
  snapshot. Oversized or 0xef-prefixed code and a reverting init frame roll back through `restore`,
  without the fault path of `protect`.
- **Installation.** `installWith` identifies the returned bytes by an exact `compareBytes` against
  the root and non-init images, takes the first match, and fails with 16 for bytes that are not an
  image. The source rule therefore installs only bytes in the catalog's `runtimes`.

The checkpoint's restoration is evaluated for the faults after the nonce advance, so init-frame
failures can reuse it, with the init frame's revert bytes as return data instead of the empty data
that `invoke_admitted` fixes today. Nested init frames run through `invoke`, not `objectFrame`, so
`finishDeployment` is not on their path: lifting the theorems' `deploying = false` premise concerns
public deployment transactions, whose root frame runs init code, and is a separate piece. Creation
over an existing empty account needs catalog links for empty bytes excluded at the address, or an
installation that keeps their identity.

**`for` loops in inline Yul.** Larger Yul fragments keep the same public statements and the same
assembly obligation. `for` needs three more pieces:

- a continuation parameter in place of fallthrough, since the lowering lowers the init block with
  the loop as its continuation: an end-of-list rule that runs the loop in the environment and
  context after the init's locals, with every other rule passing the continuation on;
- a loop relation, mutual with the statement run, for the condition, a body whose `break` ends the
  loop and whose `continue` reaches the post block, and the post block, matched against the
  installed closure of `LocalLoop.iterate` stage by stage with the Core `iterate_start`,
  `loopBody_done`, `loopBody_step`, `loopBody_bodyBreak` and failure lemmas, as the Hull loop proof
  does;
- `break` and `continue` statements, which the lowering accepts only in a loop body and which end
  their list. The statement-list proof already carries the loop flag they require.

A terminating consumer can count with the connected word operations. Local functions need the
closures `lowerBlock` installs and the `leave` result. Other effect builtins extend `BuiltinStep`,
and other word operations extend `primitive_step`, one at a time.

## Verification

- Build the affected theorem modules and the full test executable.
- Run the independent-source public consumers and the complete test suite.
- Check the semantic-kernel declaration policy and the public theorem's axioms.
- Record actual ambiguities or upstream bugs in the ignored `questions.md`.
- Delete disposable proof checks and verification logs after use.
