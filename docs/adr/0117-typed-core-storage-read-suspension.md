# ADR-0117: Typed Core storage-read suspension

- Status: Accepted
- Decision date: 2026-08-29
- Scope: syntax-independent host requests, resumable Core execution, and safety
- Implementation: In progress

## Context

ADR-0116 associates checked closed Core code with Account state and can run it
by address. That execution is intentionally pure: Core has no way to request a
contract-storage read. More wrappers around `WorldState.runCode?` cannot close
this gap because the current Core machine never exposes an operation to a host.

Adding a `storageRead` expression constructor would spread a host concern
through every syntax traversal and would weaken the existing theorem that a
checked closed program eventually finishes. A second contract IR would instead
duplicate Core typing, evaluation, local-store behavior, and safety. Core
already has typed functions and left-to-right application, so the host boundary
can use that existing language.

## Decision

Keep `Expr`, `HasType`, and the frozen wire expression languages unchanged.
Add one runtime-only function value:

```lean
inductive HostFunction where
  | storageRead

-- storageRead : word -> word
def HostFunction.parameterType : HostFunction -> Ty
def HostFunction.resultType : HostFunction -> Ty
def HostFunction.index : HostFunction -> Nat
```

`Value.hostFunction` carries the capability. There is no expression constructor
that creates it. A fixed host context and matching environment expose storage
read at its stable de Bruijn index. Later capabilities append to these tables;
they do not renumber an existing capability.

A separate `Program.checkHost` checks a program body under exactly that
context. `Program.check` continues to check a closed body under the empty
context. The proof-carrying admission boundary is likewise separate from
ADR-0116's closed carrier:

```lean
structure CheckedHostCoreProgram where
  program : Core.Program
  checked : program.checkHost = true

def CheckedHostCoreProgram.ofProgram? :
  Core.Program -> Option CheckedHostCoreProgram
```

Host functions are runtime capabilities, not source names, opcodes, addresses,
or authority tokens. A future elaborator may target the fixed context without
exposing that context as concrete Solcore syntax.

## Interactive machine boundary

Extend the internal CEK frame algebra with a host-application frame. Ordinary
application still evaluates the function first and its argument second.
Applying storage read to a fully evaluated Word produces one request:

```lean
inductive HostRequest where
  | storageRead (slot : Word)

def HostRequest.Response : HostRequest -> Type
-- storageRead response = Word

structure HostSuspension where
  request : HostRequest
  continuation : List Frame
  store : Store

def HostSuspension.resume
    (suspension : HostSuspension)
    (response : suspension.request.Response) : State
```

The suspension retains the exact remaining continuation and Core-local store.
Resuming supplies `.word response`. The request contains no `Address`,
`Account`, `WorldState`, checkpoint, frame outcome, or rollback policy.

Add an interactive advance result and fuelled runner with four boundaries:
next state, completed value, machine fault, or suspension. The fuelled result
also retains out-of-fuel state. Reaching a suspension consumes one CEK unit and
returns the remaining fuel, so a later driver cannot obtain unbounded execution
by repeatedly resuming with the original budget.

The legacy raw machine reports an explicit unhandled-host fault if manually
given a host value or host frame. This branch is unreachable for a normally
checked closed program. Existing pure checking, evaluation, correspondence,
sufficient-fuel completion, and no-fault statements remain unchanged.

## Required proof interface

Publish and verify:

- soundness and completeness of `checkHost` against declarative
  `Program.HostWellTyped`;
- exact lookup and typing of the fixed host context and environment;
- a declarative interactive step/request relation corresponding to executable
  interactive advance;
- host-aware value, environment, continuation, and state typing without
  weakening the existing pure reducibility relation;
- preservation for ordinary interactive steps;
- exact Word argument and request typing;
- preservation of continuation and local store across suspension and resume;
- progress to next, done, or a well-typed suspension for host-typed states;
- impossibility of a machine fault for checked host execution; and
- typed values and stores for every completed checked host run.

Do not claim that a checked host program eventually returns `.done` without a
handler. A well-typed program may suspend. The honest finite result is done,
suspended, or out of fuel, with machine faults excluded.

## Compatibility and dependency boundary

Wire v1 and v2 explicitly reject `Value.hostFunction`. No existing schema,
Oracle command, profile, capability document, or golden stream changes.

Core defines only the host function, typed request, suspension, and resumption.
It does not import `Solcore.Semantics`. The next runtime slice interprets a
read request through the existing proven-present working Account operation and
returns the observed Word while leaving that carrier unchanged. Code address
and storage address remain separate inputs.

ADR-0116's Account field continues to contain `CheckedCoreProgram` during this
slice. Migrating address-selected code to `CheckedHostCoreProgram` and adding a
fuel-preserving driver require a later ADR after the Core protocol and its
storage handler are proved. Storage write is also separate: it appends a new
capability and must return an updated proven-present carrier.

## Required regressions

Tests cover host-check acceptance and rejection, exact capability lookup,
function-before-argument order, exact request slots, raw invalid arguments,
continuation and local-store preservation, typed resume, repeated suspensions,
exact fuel edges, unchanged pure execution, both frozen wire rejections, and
direct use of the safety and correspondence theorems.

## Staged implementation plan

Keep every commit below 300 changed lines and green:

1. record this decision and update targeted internal roadmaps;
2. add host-function values, legacy-machine rejection, and frozen-wire rejection;
3. add the fixed host context, host checker, and proof-carrying admission;
4. add request, suspension, typed response, and resume;
5. add declarative and executable interactive advance;
6. add the fuelled interactive runner and resource laws;
7. add host-aware runtime typing, preservation, progress, and no-fault safety;
8. add the Semantics storage-read handler and focused regressions;
9. run trust-zero checks and independent audit, then record completion.

## Consequences

Core programs can request a storage read without embedding concrete Solcore
syntax or contract state in the Core language. The saved CEK continuation is
the protocol continuation; no recursive free-monad value is required.

This decision does not define who owns storage, when writes commit or roll
back, how a contract is called, or how a Core value becomes return bytes.
Those remain explicit runtime decisions layered above this protocol.
