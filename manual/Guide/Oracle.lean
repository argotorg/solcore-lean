import VersoManual
import Solcore.Synthesis.CoreV3.Generator
import Solcore.Synthesis.CoreV3.Shrink

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Reproducible experiments with the Oracle" =>
%%%
tag := "oracle"
file := "oracle"
%%%

The Oracle is a command-line interface to the model. Oracle v5 accepts Semantic
Core v3 and an explicit execution scenario. It does not compile arbitrary
Solcore source text. This makes it a useful reference point for experiments
whose inputs and observable outcomes can be recorded exactly.

# Start with the capabilities

Build the executable from the repository root and inspect its advertised
boundary:

```
lake build
lake exe solcoreOracle capabilities-v5
```

The report identifies versions, profiles, query kinds, supported observations,
and resource limits. Without a subcommand, the executable reads one JSON
request per line and writes one response per line. Keep the schema, spec,
profile, and digest from the selected published boundary together.

For a complete checked-in execution request, run:

```
lake exe solcoreOracle < Tests/golden/v5-execute-request.ndjson
```

The [root README](https://github.com/Y-Nak/solcore-lean/blob/main/README.md#query-oracle-v5)
provides a complete capabilities request and an execution fixture command.
The [Oracle v5 catalog](https://github.com/Y-Nak/solcore-lean/blob/main/docs/ORACLE_V5_WIRE.md)
is the authority for exact fields, scalar encodings, rejection priority, and
limits. The [Core v3 catalog](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CORE_WIRE_V3.md)
defines the expression payload. Internal Lean fields are not a substitute for
those closed wire contracts.

# What an execution experiment needs

An execution scenario fixes the checked contract definitions, initial accounts,
storage, balances and code references, the call and creation configuration,
invocation data, fuel, and requested state probes. Those inputs determine what
question is being asked. Changing the initial account world changes the
experiment even if the Core body stays the same.

The execution path decodes and validates the envelope, checks Core typing,
admits contract entry profiles, validates the scenario, runs the contract, and
materializes observations. A failure at an earlier boundary is not evidence
that a later boundary ran.

A useful experiment compares two invocations differing in one detail: for
example, the same storage-writing computation followed by return versus revert.
Inspect the terminal outcome, committed slot endpoints, committed logs, and
created-address list. A speculative working write is not itself evidence of a
committed change.

# Read the response category first

: Protocol error

  The JSON or versioned envelope is invalid. No language judgment is implied.

: Rejected

  A well-formed query fails the relevant checking or admission rule. Inspect
  which phase and diagnostic are reported.

: Unsupported

  The requested behavior is outside the selected profile's supported meaning.

: Inconclusive

  A resource boundary prevented an answer. More fuel or a different admitted
  budget may allow progress; this category is not source rejection.

: Executed

  Execution reached a modeled terminal outcome. Return, revert, and defined
  traps are distinct observations, not automatically internal errors.

: Internal error

  A model implementation invariant failed. This is separate from ordinary
  user-program failure and deserves investigation.

An accepted check establishes typing or admission at its query boundary; it
is not an execution result.

# Generate checked inputs

The synthesis library generates a restricted pure Word-result fragment, called
G0, directly in Core v3. It records its seed and budget for replay:

```lean
open Solcore.Synthesis.CoreV3

def replayRequest : GenerationRequest where
  seed := Seed.ofNat 0
  maxProgramNodes := 64

def generatedSize : Except GenerationError Nat := do
  let generated ← generate replayRequest
  pure generated.nodeCount
```

{name Solcore.Synthesis.CoreV3.CheckedWordProgram.wellTyped}`CheckedWordProgram.wellTyped`

{includeDocstring Solcore.Synthesis.CoreV3.CheckedWordProgram.wellTyped}

{includeDocstring Solcore.Synthesis.CoreV3.CheckedWordProgram}

{name Solcore.Synthesis.CoreV3.shrink}`shrink`

{includeDocstring Solcore.Synthesis.CoreV3.shrink}

# What comparison can establish

Compare the same semantic observations under the same inputs and profile.
Matching tests give evidence of agreement on those cases. A compiler-correctness
theorem would additionally need a representation relation and a proof connecting
the compiler's outputs to this model for all admitted inputs.

Bytecode identity, optimizer traces, generated names, and elapsed time are not
standard semantic observations. EVM gas and fork-specific behavior require a
separate specification boundary. The
[compatibility matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/COMPATIBILITY_MATRIX.md)
records which external comparisons currently exist.

# Version isolation is part of correctness

Oracle v1 is the legacy interface; v2 uses Core v1; v3 uses Core v2; v4 exposes
the historical Surface v1 parser; v5 exposes Core v3 checking and checked
contract execution. These interfaces retain their published meanings.
An internal new constructor must fail projection into a closed older wire
language that has no representation for it. A new publication is additive;
it does not reinterpret old bytes.
