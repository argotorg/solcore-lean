# ADR-0003: Verdict Categories and Resource Exhaustion

- Status: Accepted
- Decision date: 2026-07-23
- Scope: `solcore-oracle/v1`

## Reader summary / Current implementation

- **Decision:** Language outcomes use six distinct verdicts, malformed protocol
  input is separate, and exhausted implementation limits are `inconclusive`
  rather than language rejection.
- **Current implementation:** Oracle v1 through v4 keep protocol errors outside
  language results and preserve the distinction among the verdict subset each
  closed query set can emit. In particular, reaching a defined limit is not
  reclassified as source rejection.
- **Boundary:** Contract execution and its runtime halt observations remain
  outside the currently published Core- and parser-only profiles.
- **Suggested reading:** Read “Decision” for wire meaning and
  “Conformance Requirements” for limit and regression behavior.

## Context

Differential fuzzing must distinguish a program that is invalid under the
language rules, an unsupported operation in the reference implementation, an
abandoned search, and a broken oracle. Collapsing all of these outcomes into a
compile failure would create false semantic divergences.

Type-class search, recursive evaluation, and contract calls may not terminate,
so an executable oracle requires resource limits. These limits are not part of
the language semantics.

## Decision

A language query has one of the following six verdicts:

- `accepted`: The requested static phase completed.
- `rejected`: The input violated a language rule defined by the target profile.
- `unsupported`: A required feature or semantic rule is not defined by the
  profile.
- `inconclusive`: A resource limit was reached before a definitive result was
  obtained.
- `executed`: A dynamic query ran and produced a normative observation.
- `internalError`: An oracle invariant was violated or an oracle defect
  occurred.

Malformed wire input produces `protocolError`, not a language verdict.

The wire type is a six-branch discriminated sum and does not permit fields that
are irrelevant to a variant. The result of `accepted` and the observation of
`executed` are envelopes containing a schema ID and a required JSON value. A
JSON `null` value is not confused with an absent payload. Every response must
echo `spec` together with the profile ID and digest and the query kind.

Limits on the solver, evaluation, call depth, and transaction count are
explicit request fields. Reaching a limit must not be converted into
`rejected`.

Runtime `return`, `revert`, and specification-defined `trap` outcomes are halt
statuses in an `executed` observation, not `internalError` verdicts.

## Consequences

- A harness that compares only definitive acceptance and rejection can exclude
  `unsupported` and `inconclusive`.
- Different limits can change whether the same program is inconclusive, but
  cannot change its definitive meaning.
- An oracle crash cannot be hidden as a compiler rejection.
- Incremental feature delivery does not incorrectly declare an unimplemented
  program invalid.

## Conformance Requirements

- Encoding, decoding, and golden NDJSON tests must exist for every verdict.
- A regression test must verify that an unimplemented query returns
  `unsupported`.
- Tests must verify that solver and evaluator limit exhaustion returns
  `inconclusive`.
- A malformed request must produce `protocolError`, and the next request in the
  stream must still be processed.
- Source-level rejection, runtime reversion, and internal errors must remain
  distinct.
- A `rejected` verdict must include a phase and at least one normative
  diagnostic.
