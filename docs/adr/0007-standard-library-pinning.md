# ADR-0007: Standard-library pinning and the boundary of primitive semantics

- Status: Accepted
- Decision date: 2026-07-23
- Scope: language version, standard library

## Context

Many Solcore type classes, ABI dispatch mechanisms, and operations depend on
standard-library source. A comparison that uses different standard-library
revisions cannot distinguish compiler differences from library differences.

At the same time, delegating the semantics of the ABI, storage layout, word
operations, Keccak, and EVM primitives to accidental omissions or bugs in the
existing standard library would turn those defects into the formal specification.

## Decision

`LanguageVersion` pins the standard library by both its upstream revision and its
content digest.

The canonical upstream bundle for M0 consists of the following six files from the
Haskell baseline at `1d490d8bb5f374356f06e0720655496482eb1fb4`.

- `ABIGeneric.solc`
- `Generic.solc`
- `StorageGeneric.solc`
- `dispatch.solc`
- `opcodes.solc`
- `std.solc`

Compute SHA-256 over the raw bytes of each file and sort relative paths by C byte
order. Construct a manifest beginning with
`solcore-fileset-sha256-v1<LF>`, followed by one record per file of the form
`<path><TAB><decimal-byte-size><TAB><lowercase-sha256><LF>`. Compute SHA-256 over
the entire manifest, including its final LF. The M0 digest is:

```text
3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22
```

The older five-file snapshot bundled with the Rust baseline is maintained
separately as compatibility evidence and is not a canonical bundle.

M0 CI checks out the commit above separately and recomputes the manifest from the
raw `.solc` bytes themselves, not merely from the recorded sizes and hashes.
Cross-checking only the hashes stored in metadata is not a substitute for pinning
the upstream content.

Ordinary library definitions are treated as Solcore source whenever possible.
However, the ABI, storage layout, and cryptographic and EVM primitives that
directly determine external observations receive normative Lean definitions.
Future work will prove that the standard-library implementations refine those
definitions.

A semantic change to the shared standard library is fixed and verified in the
upstream Haskell standard library first. After its revision is updated, it is
vendored into the Rust implementation byte for byte. No Rust-specific semantic
fork is added to the standard library.

## Consequences

- A compiler comparison is not a semantic comparison unless both sides use the
  same standard-library digest.
- Evidence missing from the standard library does not justify a Lean language
  rule.
- Primitive semantics can be proved independently of standard-library source
  implementation details.
- Changing the standard-library digest requires an explicit language-version
  update and renewed compatibility validation.

## Conformance requirements

- Verify the standard-library manifest digest at startup or build time.
- When multiple vendored copies exist, verify byte identity for the covered files.
- The `capabilities` response reports the standard-library revision and digest.
- On a standard-library update, rerun the Haskell and Rust frontend, dispatch, and
  backend tests against the same snapshot.
- Add standard-library refinement tests or theorems for primitive and ABI
  definitions incrementally.
- Treat a digest mismatch as a configuration or protocol failure, not as a
  language-level `rejected` verdict.
