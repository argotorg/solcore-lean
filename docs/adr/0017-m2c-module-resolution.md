# ADR-0017: M2c module and lexical name resolution

- Status: Proposed
- Decision date: 2026-08-18
- Scope: M2c module graph, public interfaces, and lexical name resolution

## Context

ADR-0014 fixes caller-workspace identity and canonical logical paths. Accepted
ADR-0015 fixes the closed Multi Surface language and its independently
specified parser. Accepted ADR-0016 fixes structural syntax identity over
certified parser output. This ADR begins strictly after those boundaries. It does not define a
lexer, grammar, AST payload, source span, child traversal, or address language.

The implementation evidence remains pinned by `metadata/baselines.json`:

- Haskell Solcore at
  `1d490d8bb5f374356f06e0720655496482eb1fb4`; and
- Rust Solcore at
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`.

Neither implementation is specification authority. The Haskell loader uses
host paths and first-existing-candidate lookup, limits interface iteration by a
heuristic round count, and has environment insertions that can choose one
duplicate. The Rust loader also depends on filesystem state, changes some
library meanings in editor multi-root mode, delegates recursive interface
convergence to its incremental engine, and recursively collects instances
through the import graph. Both implementations contain scope behavior that is
unsuitable as a portable reference identity or deterministic ambiguity policy.

The resolver therefore needs a closed, pure meaning over the values established
by ADR-0014 through ADR-0016. The result is an internal formal specification and
differential-testing reference. It is not yet a wire feature.

## Decision

### Frozen published boundaries

Oracle v1 through v4, draft.1 through draft.4 language versions, every existing
profile, Surface v1, parse-result v1, Semantic Core v1 and v2, M2b golden
streams, feature statuses, and capability bytes remain unchanged. In
particular:

- Surface v1 remains the M2b single-file grammar;
- `frontend-m2b-v1` remains parse-only;
- no existing opaque source label is reinterpreted as a `SourceId`;
- no existing `resolve` query becomes supported; and
- `modules.import-export` remains planned.

The internal resolver algebra is named
`solcore-resolution-surface/m2c-v1`. A later publication ADR must assign new
wire Surface, language, profile, Oracle, limit, and golden-stream versions.

This ADR remains Proposed. ADR-0015 and ADR-0016 are now Accepted prerequisites,
but this ADR does not authorize resolver implementation until the SHA-256 and
canonical resolver feasibility gates below have passed. A feasibility-only
proof spike may be discarded or reviewed separately;
it is not resolver implementation and does not make this ADR Accepted.

### Prerequisite contracts

ADR-0015 owns the exact token algebra, grammar, separators, comments, string
and number rules, balanced assembly scanning, complete Multi Surface AST, and
closed parser diagnostics. This ADR consumes these exact exports:

```text
Multi.parseModule :
  WorkspaceFile ->
  Except (NonemptyList Multi.SurfaceDiagnostic) Multi.CertifiedParsedModule
```

`Multi.CertifiedParsedModule` is tied to the exact `WorkspaceFile` and certifies
all AST and span invariants. In particular, the accepted syntax already fixes
optional `else`, optional return expressions, contract fallback contexts,
contract-local type aliases, literals, call shapes, match arity, trailing-comma
policy, pragma shape, and every other parser question. A parser error is never
reclassified as a resolver diagnostic.

This ADR assumes the reviewed ADR-0015 correction that
`ClassDeclPayload.className : IdentifierOccurrence`. The class name is a declaration
binder selected through its declaration identity; it is not a qualified-name
occurrence and does not create a `classNameComponent` occurrence role.

The module-reference payload exported by ADR-0015 is exactly:

```text
ModuleReferencePayload =
  | relative    (components : NonemptyList PathComponent)
  | libraryRoot (marker : Marker)
                (tail : NonemptyList PathComponent)
  | standard    (marker : Marker)
                (tail : List PathComponent)
  | external    (at : Marker)
                (library : Located ExternalLibraryName)
                (tail : NonemptyList PathComponent)
```

All components and outer nodes are `Multi.Located`. The marker's certified
`SyntaxMarker` value is respectively `libraryRoot`, `standardRoot`, or
`externalSigil`. The empty `standard` tail is the source spelling `std`; the
one-component tail `[std]` is `std.std`. ADR-0015
`ModuleReferenceShape` erases spans for structural-payload comparison. Those
values remain structurally distinct even when they resolve to the same module.

ADR-0016 owns `SyntaxNodeKey`, `StructuralAddress`, `DirectRole`, `ListRole`,
`ScopeRole`, `GraphReadyModule`, `prepareGraphModule`,
`Structural.ModuleReferenceSite M`, primary spans, source order,
`CertifiedModuleIndex`, and the generic `LocalSyntaxId M K` and `SyntaxId I K`.
It supplies `DeclarationId I`, `MemberId I`, `BodyId I`, `ScopeId I`,
`LocalSiteId I`, and `OccurrenceId I`, all indexed only by the policy-free
`I : CertifiedModuleIndex`. ADR-0017, not ADR-0016, owns reachable graph policy,
`PatternClassification W`, and the `LocalId W C` refinement. This direction
prevents the structural kernel from importing resolution.

During graph discovery, `prepareGraphModule` turns a certified parsed module
into a `GraphReadyModule`, and each module reference has a module-local
`Structural.ModuleReferenceSite M`. Only after reachability succeeds are the
discovered modules passed to `CertifiedModuleIndex.ofUnique`; ADR-0017 wraps
that index with graph policy:

```text
ParsedReachableWorkspace = {
  entry      : SourceId,
  roots      : List ModuleId,
  index      : CertifiedModuleIndex,
  localEdges : canonical List LocalSourceEdge,
  ...proof that roots = canonicalRoots entry and roots.length = 7,
  ...proof that index.modules contains exactly the successfully reached
     GraphReadyModule values,
  ...proof that every root occurs exactly once in index.modules,
  ...proof that localEdges contains exactly one edge for every import/export
     module-reference occurrence exposed by each indexed GraphReadyModule,
  ...proof that every localEdges source and target occurs in index.modules,
  ...proof that every indexed module is reachable from a root by localEdges...
}
```

Its root list is the exact canonical seven-element list containing the main
entry followed by the six distinct standard modules, with both an equality and
a length proof. `ParsedReachableWorkspace` additionally contains every module
reached through a successfully parsed import or export reference. It does not
contain unrelated validated files merely because they were supplied. Every
resolver identity is non-dangling by construction. There is consequently no
malformed-address resolver diagnostic and no independent post-graph
address-validation phase. Local sites lift with ADR-0016 `lift` into identities
indexed by `W.index`, never by `W` itself.

For compact pseudocode only, every structural alias below uses this notation:

```text
DeclarationId W = Structural.DeclarationId W.index
MemberId      W = Structural.MemberId W.index
BodyId        W = Structural.BodyId W.index
ScopeId       W = Structural.ScopeId W.index
LocalSiteId   W = Structural.LocalSiteId W.index
OccurrenceId  W = Structural.OccurrenceId W.index
UnconditionalLocalSite W = Structural.UnconditionalLocalSite W.index
PatternCandidateSite W   = Structural.PatternCandidateSite W.index
```

This notation is not a new identity family. Equality, ordering, selection,
ownership, and primary spans remain exactly the ADR-0016 operations on
`SyntaxId W.index K`.

ADR-0017 may not weaken either prerequisite certificate, reconstruct identity
from text equality, or accept an unchecked AST supplied by a compiler.

### Raw standard bundle and exact closed-workspace assembly

ADR-0014 `ValidatedUserWorkspace` contains caller sources only and proves that
none uses `LibraryId.standard`. The neutral module introduced by ADR-0015 owns
the sole canonical source-byte literals and exports exactly:

```text
Solcore/Standard/CanonicalData.lean

CanonicalFileId =
  | abiGeneric | generic | storageGeneric | dispatch | opcodes | std

CanonicalRawFile = {
  id                  : CanonicalFileId,
  logicalPathUtf8     : ByteArray,
  contentUtf8         : ByteArray,
  expectedByteCount   : Nat,
  expectedSha256Bytes : Vector UInt8 32
}

Solcore.Standard.canonicalRawFiles : Vector CanonicalRawFile 6
```

The vector is in the exact table order below, contains every `CanonicalFileId`
once, and has the displayed logical-path bytes. Its count and digest fields are
metadata values, not proofs. `CanonicalData` contains no parser result,
resolver result, hash theorem, manifest literal, or Git provenance claim.
ADR-0015
`StandardFixtures` decodes these same bytes into parser `WorkspaceFile` values;
ADR-0017 standard verification compares raw input with these same bytes. No
second source-content literal is permitted under `Surface` or `Resolution`.

ADR-0017 derives `canonicalFile id` as the unique vector entry with that id,
`canonicalIds` as the six ids in vector order, and these values without copying
literal bytes:

```text
canonicalPathBytes id    = (canonicalFile id).logicalPathUtf8
canonicalContentBytes id = (canonicalFile id).contentUtf8
canonicalByteCount id    = (canonicalFile id).expectedByteCount
canonicalDigest id       =
  Digest256.ofVector (canonicalFile id).expectedSha256Bytes

canonicalManifestBytes =
  the manifest equation below mapped over canonicalIds

expectedManifestDigest =
  Digest256.ofLowerHex
    "3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22"
```

Server-owned standard input is raw bytes:

```text
RawStandardFile = {
  pathBytes    : ByteArray,
  contentBytes : ByteArray
}

RawStandardBundle = {
  files : List RawStandardFile
}
```

For an input bundle `B`, define:

```text
matchingIndices(B, p) =
  the ascending list of i where B.files[i].pathBytes = canonicalPathBytes p

recognizedPath(B, i) =
  the unique p whose canonical path bytes equal B.files[i].pathBytes, if any

structurallyExact(B) =
  B.files.length = 6 and
  every matchingIndices(B, p) has length 1
```

Pairwise distinct canonical path bytes make `recognizedPath` functional.
`structurallyExact` also entails that no input path is unexpected.

There is no caller-supplied revision claim, decoded source string, digest, or
pre-resolved interface. `verifyStandardBundle` validates the complete canonical
error set and, only when it is empty, constructs `VerifiedStandardBundle`.
Verification requires all of the following:

1. the file list contains exactly the six path byte strings below, once each;
2. canonical output order is ascending C byte order of those path bytes;
3. each content byte array equals the corresponding kernel constant byte for
   byte, not merely a digest with the expected value;
4. each content is valid UTF-8 and decoding then encoding yields the same byte
   array;
5. the recorded decimal byte size and pure SHA-256 digest equal the values
   below; and
6. the exact manifest construction and its digest equal ADR-0007.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `ABIGeneric.solc` | 5540 | `b14f31abd374d65e194c7706183086082558ab2a60d230ec5b9e6f1b9c9b9ae2` |
| `Generic.solc` | 445 | `913a02e32829e0230e31db6512151c36e019f5630e3dbd0be9d033a9019194d7` |
| `StorageGeneric.solc` | 10546 | `8d68601447f40a6e662de8b6cff06031998628339ca23ec917a970157c301a6a` |
| `dispatch.solc` | 11249 | `b723ec9a0a76a6abf091d49a12467c6a4628b634c48d8c34e82e2c45d6e939f5` |
| `opcodes.solc` | 10377 | `a6a08beed16ccdf722f65c60af835dcfd0eaec61f34f041082bbc0fca1e69bab` |
| `std.solc` | 72958 | `e8ec755232347bbf4a130dcc05c7c5a3230c4d0cb0223445a2d82260d4474fec` |

The manifest is the byte concatenation of
`solcore-fileset-sha256-v1<LF>` and, in table order, the ASCII path, TAB,
canonical unsigned decimal size, TAB, lowercase hexadecimal digest, and LF for
each file. The final LF is included. Its SHA-256 digest is
`3f81bebfd1fc161ee08972be9e7a52150d02bdf55dd7449dfa058cd81cfafc22`.

The configuration error algebra is closed:

```text
StandardBundleError =
  | unexpectedPath
      (inputIndex : Nat) (pathBytes : ByteArray)
  | duplicatePath
      (path : CanonicalFileId)
      (indices : canonical NonemptyList Nat)
  | missingPath
      (path : CanonicalFileId)
  | contentMismatch
      (path : CanonicalFileId) (inputIndex : Nat)
  | invalidUtf8
      (path : CanonicalFileId) (inputIndex : Nat)
  | sizeMismatch
      (path : CanonicalFileId) (inputIndex : Nat)
      (expected actual : Nat)
  | sha256InputTooLarge
      (path : CanonicalFileId) (inputIndex actualSize : Nat)
  | fileDigestMismatch
      (path : CanonicalFileId) (inputIndex : Nat)
      (expected actual : Digest256)
  | manifestDigestMismatch
      (expected actual : Digest256)
```

`StandardBundleError.Applies B error` is independent of the verifier. Its
truth table is exact:

| Constructor | Applies exactly when |
| --- | --- |
| `unexpectedPath i bytes` | `i` is in bounds, the stored path equals `bytes`, and `recognizedPath B i = none` |
| `duplicatePath p indices` | `indices = matchingIndices B p` and `indices.length >= 2` |
| `missingPath p` | `matchingIndices B p = []` |
| `contentMismatch p i` | `recognizedPath B i = some p` and the input content bytes differ from `canonicalContentBytes p` |
| `invalidUtf8 p i` | `recognizedPath B i = some p` and strict UTF-8 decoding of the input content fails |
| `sizeMismatch p i expected actual` | `recognizedPath B i = some p`, `expected = canonicalByteCount p`, `actual` is the input size, and they differ |
| `sha256InputTooLarge p i actualSize` | `recognizedPath B i = some p`, `actualSize` is the input size, and `not (actualSize < 2^61)` |
| `fileDigestMismatch p i expected actual` | `recognizedPath B i = some p`, the content size is below `2^61`, `expected = canonicalDigest p`, `actual` is the pure digest of the input, and they differ |
| `manifestDigestMismatch expected actual` | `structurallyExact B`, all six input contents are below `2^61`, `expected = expectedManifestDigest`, `actual` is the digest of the manifest built from the six actual sizes and actual file digests, and they differ |

All applicable errors coexist. In particular:

- a duplicate canonical path and a missing different path are both reported;
- every unexpected input is reported even when paths are also missing or
  duplicated;
- every recognized occurrence, including every duplicate occurrence, is
  independently checked for exact content, UTF-8, size, and digest;
- invalid UTF-8 does not suppress exact-content or size checking;
- an oversized input suppresses only the digest check for that occurrence and
  the manifest check;
- duplicates, missing paths, or extras suppress only
  `manifestDigestMismatch`; and
- when the path set is structurally exact, manifest mismatch may coexist with
  content, UTF-8, size, and file-digest errors.

The strict UTF-8 decoder proves that every successful decode re-encodes to the
input bytes. Therefore the round-trip requirement has no additional reachable
failure case; `invalidUtf8` is the complete UTF-8 error constructor rather than
an omission from the closed sum.

Errors are sorted by the displayed constructor order, canonical path when the
constructor has one, input index, then remaining fields; exact duplicates are
removed. `verifyStandardBundle B` returns exactly the canonical nonempty list
of errors whose `Applies` relation holds, or constructs
`VerifiedStandardBundle` exactly when no error applies. A digest comparison
never substitutes for exact content equality.

```text
VerifiedStandardBundle = {
  input          : RawStandardBundle,
  workspaceFiles : canonical List WorkspaceFile,
  ...proof that input is structurallyExact and no StandardBundleError applies,
  ...proof that workspaceFiles is exactly canonicalIds mapped to the
     corresponding LibraryId.standard SourceId and strict UTF-8 decoding of
     canonicalContentBytes, with no other element...
}
```

The input is retained only as evidence for the verification relation. Resolver
code can inspect `workspaceFiles` and its equalities, not choose between raw
occurrences.

The Git revision
`1d490d8bb5f374356f06e0720655496482eb1fb4` is provenance evidence checked by
CI: CI reads the six raw blobs from `std/` at that commit and compares them with
the kernel constants. Git history and commit identity are not values the Lean
kernel can establish from bytes, so no theorem claims that a byte array came
from a Git commit.

The assembled input algebra has no freely supplied file list:

```text
ClosedWorkspace = {
  user     : ValidatedUserWorkspace,
  standard : VerifiedStandardBundle
}

ClosedWorkspace.entry S = S.user.entry
ClosedWorkspace.declaredExternalLibraries S =
  S.user.declaredExternalLibraries
ClosedWorkspace.files S =
  canonicalSortBySourceId (S.user.files ++ S.standard.workspaceFiles)

assembleClosedWorkspace user standard = { user, standard }
```

Thus every `ClosedWorkspace` is definitionally the product of one validated
caller workspace and one raw-byte-verified standard bundle; there is no public
constructor accepting derived accessors. If `S = assembleClosedWorkspace user
standard`, its defining equations are:

```text
S.entry                     = user.entry
S.declaredExternalLibraries = user.declaredExternalLibraries
S.files = canonicalSortBySourceId (user.files ++ standard.workspaceFiles)

f in S.files <->
  f in user.files or f in standard.workspaceFiles
```

`standard.workspaceFiles` has exactly the six `LibraryId.standard` identities
above. Thus the result has no third source category, synthetic file, replaced
caller file, or omitted standard file. The existing source order is main,
standard, then external libraries by canonical external name, with canonical
paths inside each library. Entry membership and all caller declarations are
preserved exactly.

Standard verification failure is a server configuration failure. It is never a
source rejection and is outside `ResolutionFailure`.

### SHA-256 module boundary and feasibility gate

SHA-256 is a separate Foundation kernel, not a monolithic helper embedded in
standard-bundle code:

```text
Solcore/Foundation/Sha256/Syntax.lean
Solcore/Foundation/Sha256/Judgment.lean
Solcore/Foundation/Sha256/Execution.lean
Solcore/Foundation/Sha256/Certificate.lean
Solcore/Foundation/Sha256/Properties.lean
Solcore/Foundation/Sha256.lean
```

`Syntax` defines the 32-byte digest, block, schedule, state, padding, and
lowercase rendering types. `Judgment` defines `Sha256.Digests` from the SHA-256
padding, schedule, and compression equations without importing `Execution`.
`Execution` defines the pure `BitVec 32` executor without importing `Judgment`.
`Certificate` defines a finite per-block chaining-state certificate and a pure
replayer. `Properties` alone imports both sides and proves executor and replayer
soundness, completeness, and judgment functionality. The umbrella imports the
completed proof boundary.

The executable cannot be called on an unbounded raw value:

```text
Sha256.Input = {
  bytes : ByteArray,
  sizeFits : bytes.size < 2^61
}

Sha256.digest : Sha256.Input -> Digest256
```

`Sha256.Digests input digest` is indexed by the same refined input. The
`2^61` bound is exactly the condition that the bit length fits SHA-256's 64-bit
length field. Standard verification constructs `Sha256.Input` only after the
bound check in the error truth table. The executor uses no host hash, foreign
call, file I/O, or runtime-only decision procedure.

The 111,115 canonical source bytes require a practical kernel-checking plan.
An untrusted build-time generator may emit block boundaries and expected
chaining states, but the checked certificate contains no trusted conclusion:
the replayer recomputes padding and every block transition, and its proved
soundness yields `Sha256.Digests`. Concrete file proofs are split at block
boundaries so no single elaboration term expands the complete bundle.

Before this ADR can become Accepted, an isolated gate must build all of these
without `native_decide`, new axioms, or increased heartbeat/recursion limits:

- empty, one-block, two-block, and padding-boundary known vectors;
- executor/judgment correspondence;
- replayer soundness;
- the complete 72,958-byte `std.solc` certificate; and
- the manifest certificate.

If that gate is not practical in the repository's ordinary CI configuration,
the representation and certificate strategy must be revised in this ADR before
resolver implementation starts.

### Closed intrinsic environment

The intrinsic identity is the following exact finite sum:

```text
IntrinsicId =
  | typeWord | typeBool | typeInteger | typeUnit | typeArrow
  | typePair | typeSum
  | classInvokable | classInt
  | constructorTrue | constructorFalse | constructorUnit
  | constructorPair | constructorInl | constructorInr
  | functionInvoke | functionPrimAddWord | functionPrimEqWord
  | functionWordToInteger | functionWordFromInteger
  | functionIntegerAdd | functionIntegerSub | functionIntegerMul
  | functionIntegerLt | functionIntegerEq
  | methodInvokableInvoke | methodIntFromInteger
```

The ordinary bare-identifier fallback is the following total finite map:

| Lookup namespace | Spelling | Target |
| --- | --- | --- |
| type | `word` | `typeWord` |
| type | `bool` | `typeBool` |
| type | `integer` | `typeInteger` |
| type | `pair` | `typePair` |
| type | `sum` | `typeSum` |
| class | `invokable` | `classInvokable` |
| class | `Int` | `classInt` |
| term/constructor | `true` | `constructorTrue` |
| term/constructor | `false` | `constructorFalse` |
| term/constructor | `pair` | `constructorPair` |
| term/constructor | `inl` | `constructorInl` |
| term/constructor | `inr` | `constructorInr` |
| term/function | `invoke` | `functionInvoke` |
| term/function | `primAddWord` | `functionPrimAddWord` |
| term/function | `primEqWord` | `functionPrimEqWord` |
| term/function | `wordToInteger` | `functionWordToInteger` |
| term/function | `wordFromInteger` | `functionWordFromInteger` |
| term/function | `integerAdd` | `functionIntegerAdd` |
| term/function | `integerSub` | `functionIntegerSub` |
| term/function | `integerMul` | `functionIntegerMul` |
| term/function | `integerLt` | `functionIntegerLt` |
| term/function | `integerEq` | `functionIntegerEq` |

Qualified lookup adds exactly
`invokable.invoke -> methodInvokableInvoke` and
`Int.fromInteger -> methodIntFromInteger`. `invoke` therefore denotes
`functionInvoke`, not an intrinsic method. There is no bare intrinsic
`fromInteger`, and the unqualified class-method fallback later in this ADR
never adds either intrinsic method.

The remaining intrinsic targets are attached only to exact structured syntax:

- `TypeExpr.function domain codomain` carries `typeArrow`;
- the empty type tuple carries `typeUnit`;
- the empty expression or pattern tuple carries `constructorUnit`; and
- every nonempty flat type, expression, or pattern tuple remains a flat tuple
  for M2d and is not rewritten into nested `pair` applications.

The identifiers `pair`, `sum`, `inl`, and `inr` go through ordinary lookup and
can be shadowed; they are not attached merely because tuple or sum-like syntax
was parsed. No identifier spelling `()` or `->` exists. This set matches the
pinned Haskell empty environment and is closed. `Word` is not an alias for
`word`; `string` is not intrinsic; and ordinary names such as `bnotWord`,
`bshlWord`, and `bshrWord` resolve from verified standard sources. A caller
cannot extend or replace the intrinsic value. Intrinsics have the lowest
priority in their respective lexical namespaces.

### Pure module-reference resolution

For current module `M`, the ADR-0015 module-reference payload maps to exactly
one target `ModuleId`:

| Payload | Target library | Target module path |
| --- | --- | --- |
| `relative [p0, ..., pn]` | `M.library` | `M.path.directory ++ [p0, ..., pn]` |
| `libraryRoot marker [p0, ..., pn]` | `M.library` | `[p0, ..., pn]` |
| `standard marker []` | `standard` | `[std]` |
| `standard marker [p0, ..., pn]` | `standard` | `[p0, ..., pn]` |
| `external marker L [p0, ..., pn]` | `external L` | `[p0, ..., pn]` |

The ADR-0014 canonical component constructors make each concatenation a module
path. Bare `lib` is a one-component relative reference because the
`libraryRoot` constructor requires a nonempty tail. Bare `std` is always the
standard module `std` and never falls back to a relative source. Bare `@name`
cannot be constructed by ADR-0015.

An external reference first requires `L` in
`ClosedWorkspace.declaredExternalLibraries`, then requires the exact target in
`ClosedWorkspace.files`. These failures have distinct graph diagnostics. Every
other reference succeeds exactly when the one target `ModuleId` is present.
There is no candidate search, extension probing, cwd, realpath, root prefix,
filesystem existence fact, editor namespace, or standard fallback.

A form that creates a module binding uses its explicit alias when present.
Otherwise it converts the target path's final `PathSegment` with
`PathSegment.asIdentifier?`. This conversion succeeds exactly when the segment
text satisfies ADR-0015 `identifierTextValid`, including its complete hard-keyword
exclusion. If it fails, the resolver emits `defaultBindingRequiresAlias` at the
exact module-reference occurrence. It never manufactures an identifier. Selective
imports and wildcard re-exports create no default module binding and therefore
do not require an alias merely because the target leaf is reserved. In
particular, `std` is an ordinary ADR-0015 identifier, so plain `import std;`
binds `std`. A reference such as `foo.if` has a hard-keyword leaf and requires
an explicit alias in module-binding form; `import foo.if.{*};` does not.

### Reachability and occurrence-preserving source graph

The root frontier is exactly `canonicalRoots entry`: the caller entry followed
by the six standard modules in canonical `ModuleId` order. ADR-0014's caller-
only proof and the six distinct standard ids prove that these seven elements
are already duplicate-free; discovery does not silently shrink the list.
Every standard module is therefore parsed and resolved even when caller code
never imports `std`.

Reachability is discovered in canonical rounds. For every current frontier,
modules are processed in ascending `ModuleId` order. An exact source lookup is
passed to `Multi.parseModule`, followed by `prepareGraphModule`; a successful
graph-ready certificate exposes module references in source order. Each
reference is resolved by the pure rule above. Successful targets form the next
deduplicated canonical frontier. If parsing returns its canonical nonempty
diagnostic list, phase 2 emits one typed `surface` wrapper for every element,
storing its zero-based position in that returned list and without changing or
collapsing any `Multi.SurfaceDiagnostic`; it exposes no outgoing references for
that module. Other modules in the same frontier are still processed. Missing
and undeclared targets contribute graph diagnostics and no edge. An unrelated
file is never parsed.

Discovery continues through every frontier produced by successfully parsed
modules even when an earlier module in the same phase failed. Phase 2 then
combines all retained Surface failures and all module-reference failures,
sorting first by source/`ModuleId`, then optional primary span, phase-2
constructor, structural site when present, and remaining diagnostic payload.
Thus multiple parser structural
diagnostics from one module and failures from different modules on the same
frontier all survive the first-phase output.

The seen-module set grows inside the finite exact `ClosedWorkspace.files` set,
so discovery terminates without recursion fuel or a depth cap.

During discovery, an edge is keyed by the module-local certified reference:

```text
LocalSourceEdge = {
  kind   : import | export,
  module : GraphReadyModule,
  site   : Structural.ModuleReferenceSite module.parsed,
  target : ModuleId
}
```

The source is definitionally `module.parsed.file.id.toModuleId`.

After a diagnostic-free closure constructs `W : ParsedReachableWorkspace`, the
site is lifted to its `OccurrenceId W`:

```text
SourceEdge W = {
  kind   : import | export,
  source : ModuleId,
  site   : Structural.OccurrenceId W.index,
  target : ModuleId
}
```

One import declaration contributes one import edge. Every module reference in
an export contributes its own export edge, including every `allFrom` entry.
Two references that have the same source and target remain two edges because
their occurrence sites differ. Thus `std` and `std.std`, or two repeated export
references, are never collapsed in the occurrence-preserving graph. A separate
semantic adjacency set may erase `kind` and `site` only for reachability proofs.

The stored `SourceEdge W` list is strictly sorted by source `ModuleId`, then by
the structural absolute-address order of `site`, then by `kind` with `import`
before `export`, and finally by target `ModuleId`. Exact duplicate structural
sites are impossible. No normalization deduplicates a source/target pair, so
different occurrences remain different edges even when every other semantic
field agrees. `LocalSourceEdge` uses the corresponding module-local site order
before `W.index` exists.

### Phase order and first-failure boundary

The executor has the following exact phases:

1. verify the raw standard bundle and assemble the closed workspace;
2. discover reachable parses, certified graph-ready modules,
   module-reference targets, and source edges;
3. build declaration catalogs and reject declaration, unconditional
   simultaneous-binder, and invalid default-module-binding errors;
4. compute the least static candidate/rule closure and then compute `N`, `E`,
   `A`, `R`, `O`, and `resolutionUnits`;
5. saturate interfaces to the proved least fixed point;
6. validate public interfaces and every import/export selection against that
   fixed point;
7. construct module, owner, import, and source-instance environments and the
   total `PatternClassification W`; and
8. lift classified `LocalId W C` values, resolve lexical occurrences, and
   construct deferred M2d selectors.

Phase 1 returns configuration failure, not a language diagnostic. For phases 2
through 8, the executor returns the complete canonical diagnostic list from the
first phase with any diagnostic and does not run later phases. Catalog errors
therefore never produce a fabricated `R` or resource metric,
and interface errors never leak cascaded lexical errors.

The internal executor is total and has no caller fuel. A future publication
limit is checked after phase 4 and before saturation. At the exact limit the
request proceeds; one unit over is `inconclusive`, never a language rejection.
Decoder allocation limits and ADR-0014 caller byte/file preflight remain earlier
and separate. Phase 4 materializes only the least static closure, but a
publication ADR must still derive checked allocation bounds from concrete input
and worklist lengths and stop before closure construction when that bound
exceeds its executor envelope. It may not enumerate or take the cardinality of
the logical carrier merely to obtain that bound. The semantic metric does not
by itself bound allocation.

### Declaration catalogs and duplicate policy

The duplicate namespaces are the exact closed sums:

```text
DeclarationNamespace = typeOrClass | term

MemberNamespace =
  | contractType | contractTerm | dataConstructor
  | classMethod | instanceMethod

ContractId W = {
  declaration : DeclarationId W,
  ...proof that declaration selects a contract...
}

SimultaneousGroupRole =
  | dataParameters | typeAliasParameters | contractParameters
  | topFunctionGeneric | classGeneric | classMethodGeneric
  | instanceGeneric | instanceMethodGeneric
  | contractFunctionGeneric | fallbackGeneric
  | topFunctionParameters | classMethodParameters
  | instanceMethodParameters | contractFunctionParameters
  | fallbackParameters | contractConstructorParameters
  | lambdaParameters

SimultaneousGroupRole.toScopeRole : SimultaneousGroupRole -> ScopeRole
-- the total same-named constructor map for all 17 cases above

SimultaneousGroupKey W = {
  scope : ScopeId W,
  role  : SimultaneousGroupRole,
  exact : scope.role = role.toScopeRole
}

UnconditionalGroupMember W (group : SimultaneousGroupKey W) = {
  local : UnconditionalLocalSite W,
  owner : Structural.localOwner local.site = group.scope,
  roleCompatible : compatibleGroupRole local.role group.role
}
```

`compatibleGroupRole` is the following closed table and has no default case:

| Unconditional local role | Permitted simultaneous group role |
| --- | --- |
| `dataParameter` | `dataParameters` |
| `typeAliasParameter` | `typeAliasParameters` |
| `contractParameter` | `contractParameters` |
| `forallBinder` | exactly one of the seven displayed `...Generic` roles |
| `functionParameter` | exactly one of `topFunctionParameters`, `classMethodParameters`, `instanceMethodParameters`, `contractFunctionParameters`, `fallbackParameters`, or `contractConstructorParameters` |
| `lambdaParameter` | `lambdaParameters` |

ADR-0016 `letBinder` and `forLetBinder` have no constructor in this relation;
`patternCandidate` is not an `UnconditionalLocalSite`. They therefore cannot be
inserted into a `SimultaneousGroupKey` by type. The explicit
`contractParameter` row prevents contract parameter duplicates from falling
through an informal callable rule.

Module declarations are cataloged without source-order winner selection.
Module-local type and class declarations share the `typeOrClass` duplicate
namespace. Module functions use the `term` namespace. Contracts have a nested
type namespace for data and type aliases and a nested term namespace for fields
and functions. Data constructors, class methods, and instance methods each use
their owning declaration as a namespace. At most one unnamed contract
constructor and one fallback are accepted per contract.

Duplicate constructor names in one data declaration, class method names in one
class, instance method names in one instance, and contract member names in the
same member namespace are typed duplicate-member diagnostics. There is no
generic string-keyed duplicate escape hatch.

Before pattern classification, the duplicate local binders rejected by the
catalog phase are exactly the `UnconditionalGroupMember` values of one
`SimultaneousGroupKey`. Pattern binders are checked later because same-name
constructor classification depends on final interfaces. Sequential ordinary
and for-initializer `let` bindings are not simultaneous groups. Each advances
to its ADR-0016 `sequentialContinuation`, so a later `let x` may deliberately
shadow an earlier `x` in the same body.

ADR-0015 has already rejected repeated syntax inside one import/export
declaration, including repeated span-erased `ModuleReferenceShape` values.
Repeated declarations elsewhere retain all candidates; neither source order nor
map insertion chooses an origin.

### Import semantics

This section assigns meaning to the exact ADR-0015 `ImportMode` constructors;
it does not redefine their grammar. A module import contributes one module
binding and no unqualified entity. An item import contributes unqualified
entities and no module binding.

For `ImportMode.module alias?`, the binding is the explicit alias or the valid
default binding described above. Its target is the exact resolved module.

For `ImportMode.items selection hiding?`:

- a named entry selects the target interface's public source name and installs
  the explicit alias or that same name locally;
- wildcard selects every public entity atom from the target;
- hiding is compared with source public names after wildcard/named expansion
  and before aliases are installed;
- a hiding name must exist in the target public entity set even if a named
  selection did not select it;
- ADR-0015 certification proves that source names, resulting local names, and
  hiding names do not repeat within the declaration; and
- selection never copies public module bindings or instances.

The parser has already rejected empty lists, wildcard/name mixtures, and all
within-declaration duplicates according to ADR-0015. The resolver retains exact
selector occurrences for unknown and ambiguity diagnostics.

Selecting a data entity copies exactly the constructor atoms visible under that
public type binding. Locally the constructors remain subordinate to the local
type name: unaliased `T` permits `T.C`, while `T as U` permits `U.C`. No import
introduces a generic bare `C`. A hidden constructor cannot be recovered by a
later import or export along that same route. An independent route that
explicitly exposes it contributes its own constructor atom, and exact equal
atoms then join idempotently.

Every successful import edge, regardless of module/item/wildcard mode, also
contributes the target module's own local instance declarations to
`sourceInstanceEnvironment`. It does not contribute instances that the target
itself imported. Export edges contribute no instances.

### Export semantics

The following table is exhaustive for the ADR-0015 export constructors.

| Form | Interface contribution |
| --- | --- |
| local wildcard `export {*}` | every importable entity declared locally in this module; zero constructor atoms; no imported entity, module binding, or instance |
| local item `name` | the visible local/imported entity under `name`; zero constructor atoms |
| local item `T(*)` | data entity `T` plus every constructor currently visible under that binding |
| local item `T(C1, ..., Cn)` | data entity `T` plus exactly the requested currently visible constructors |
| local `allFrom moduleRef` | same entity and subordinate-constructor copying as remote wildcard; no module binding or instance |
| module `moduleRef` | one module binding under the valid default leaf |
| module `moduleRef as alias` | one module binding under `alias` |
| remote dot wildcard or braced wildcard | every target public entity and exactly its subordinate visible constructor atoms; no target module binding or instance |
| remote named item | the selected target entity and the constructor subset requested by `none`, `all`, or `named` |

Local wildcard deliberately makes local data opaque. Remote wildcard preserves
the provider's constructor visibility. Those two wildcard meanings are not
interchangeable. `public` on a function is an ABI property and never creates an
implicit export. There is no entity export alias in m2c-v1.

For a requested constructor selection, the entity contribution depends only on
the entity being visible. Each requested constructor contribution depends on
that constructor being visible. If the entity is not data,
`nonDataConstructorSelector` is emitted. If a named constructor is absent,
`unknownExportConstructor` is emitted. The intermediate positive fixed point
may therefore contain the entity while validation reports a missing requested
constructor; an invalid fixed point is never used to build environments.

ADR-0015 rejects repeated named export entries, constructor names, and exact
`moduleRef.*` entries before constructing `CertifiedParsedModule`. Its duplicate
check uses structural `ModuleReferenceShape`, not resolved-target equality, so
`std.*` and `std.std.*` remain distinct entries even though their target module
is equal. ADR-0017 retains the distinct structural occurrence sites for graph
edges, rules, and diagnostics.

### Public interface atoms and invariant

Resolver refinements never use bare addresses:

```text
EntityId W = {
  syntax : DeclarationId W | MemberId W,
  ...proof that syntax selects a named function, data, type alias, class,
     contract, contract field, contract function, or nested contract type...
}

PublicEntityId W = {
  entity      : EntityId W,
  declaration : DeclarationId W,
  ...proof that entity.syntax = .declaration declaration and declaration is an
     importable top-level declaration...
}

DataEntityId W = {
  entity : PublicEntityId W,
  ...proof that entity is a top-level data declaration...
}

OwnedDataId W = {
  entity : EntityId W,
  ...proof that entity is any top-level or contract-nested data declaration...
}

ConstructorId W = {
  member : MemberId W,
  owner  : OwnedDataId W,
  ...proof that member is a constructor structurally owned by owner...
}

ClassMethodId W = {
  member : MemberId W,
  ...proof that member is a class method...
}

InstanceId W = {
  declaration : DeclarationId W,
  ...proof that declaration is an instance...
}
```

For `W : ParsedReachableWorkspace`, all owners, targets, and candidate names are
finite proof-carrying values rather than unconstrained fields:

```text
EntityNamespace = term | type | class

ReachableModule W = {
  id     : ModuleId,
  member : exists M in W.index.modules, moduleId M = id
}

ImportAliasKey W = {
  occurrence : OccurrenceId W,
  value      : Identifier,
  exact      : occurrence selects an explicit item or module import alias
               whose spelling is value
}

ExportAliasKey W = {
  occurrence : OccurrenceId W,
  value      : Identifier,
  exact      : occurrence selects an explicit module export alias whose
               spelling is value
}

StaticNameRole =
  | catalogEntity | catalogConstructor
  | importSource | importAlias | hidingName
  | exportSource | exportAlias | exportConstructor
  | validDefaultLeaf

StaticNameSyntax W =
  | declaration (DeclarationId W)
  | member (MemberId W)
  | occurrence (OccurrenceId W)
  | defaultLeaf (ModuleBindingKey W)

StaticNameSite W = {
  role   : StaticNameRole,
  syntax : StaticNameSyntax W,
  value  : Identifier,
  exact  : StaticNameSite.Selects role syntax value
}

StaticNameSite.Selects =
  | catalogEntity
      (origin : PublicEntityId W)
      : Selects catalogEntity (.declaration origin.declaration)
          (declaredLeaf origin)
  | catalogConstructor
      (constructor : ConstructorId W)
      : Selects catalogConstructor (.member constructor.member)
          (declaredLeaf constructor)
  | importSource
      (key : ImportNameSelectorKey W)
      : Selects importSource (.occurrence key.sourceOccurrence) key.sourceName
  | importAlias
      (key : ImportAliasKey W)
      : Selects importAlias (.occurrence key.occurrence) key.value
  | hidingName
      (key : HidingSelectorKey W)
      : Selects hidingName (.occurrence key.occurrence) key.value
  | exportSource
      (key : ExportSelectorKey W)
      : Selects exportSource (.occurrence key.sourceOccurrence) key.sourceName
  | exportAlias
      (key : ExportAliasKey W)
      : Selects exportAlias (.occurrence key.occurrence) key.value
  | exportConstructor
      (key : ConstructorNameKey W)
      : Selects exportConstructor (.occurrence key.occurrence) key.value
  | validDefaultLeaf
      (key : ModuleBindingKey W) (value : Identifier)
      (exact : key.targetLeaf.asIdentifier? = some value)
      : Selects validDefaultLeaf (.defaultLeaf key) value

StaticName W = {
  value   : Identifier,
  present : exists site : StaticNameSite W, site.value = value
}

EntityAtom W = {
  owner      : ReachableModule W,
  publicName : StaticName W,
  origin     : PublicEntityId W
}

entityNamespaceOf : PublicEntityId W -> EntityNamespace
EntityAtom.namespace e = entityNamespaceOf e.origin

ConstructorAtom W = {
  owner          : ReachableModule W,
  publicTypeName : StaticName W,
  dataOrigin     : DataEntityId W,
  constructor    : ConstructorId W,
  exactOwner     : constructor.owner.entity = dataOrigin.entity.entity
}

ModuleBindingAtom W = {
  owner      : ReachableModule W,
  publicName : StaticName W,
  target     : ReachableModule W
}

InterfaceAtom W =
  | entity (EntityAtom W)
  | constructor (ConstructorAtom W)
  | moduleBinding (ModuleBindingAtom W)
```

There is no `StaticNameSite.Selects` constructor for arbitrary identifier
occurrences. `StaticName.present` is a proposition, so proof
irrelevance makes `StaticName` equality exactly identifier equality rather than
witness-site equality.

`entityNamespaceOf` is the closed catalog-kind table: functions, contract
fields, and contract functions are `term`; data declarations, type aliases,
contracts, and contract-nested types are `type`; and class declarations are
`class`. Its argument refinement rules out every other declaration kind.
`ReachableModule`, `StaticNameSyntax`, `StaticNameSite`, `StaticName`, each atom
record, and therefore `InterfaceAtom` have executable `DecidableEq`, `Ord`, and
`Fintype` instances derived only from the finite `W.index` enumerators and the
closed structural key enumerators. No instance uses a list of all identifier
byte strings.

Instances are intentionally absent. They are local catalog facts consumed by
the direct-import rule above and are never saturated or re-exported.

Every interface set satisfies this invariant: each constructor atom has the
matching type-namespace entity atom for the same owner, public type name, and
data origin, and the `ConstructorId` is owned by that data origin. An opaque data
export is exactly a data entity atom with no constructor atom. The rule compiler
and each saturation step preserve the invariant.

Two exact atoms are idempotent. Constructor atoms for the same public type name
and data origin join by union. Distinct entity origins under the same public
name are ambiguous even when their entity namespaces differ. Equal module
bindings to the same target are idempotent; different targets are ambiguous. A
public module binding and public entity with the same name collide. No
normalization chooses a candidate.

### Least static candidate closure and import-route provenance

The implementation does not materialize the infeasible cartesian product of
every module, spelling, and origin. It constructs only candidates justified by
actual catalog entries and source routes.

An import route retains its complete immediate provenance. The fields called
`exact...` below are propositions and are erased from equality and ordering:

```text
WildcardImportSelectorKey W = {
  key   : ImportSelectorKey W,
  exact : key selects Multi.ImportSelectionEntry.wildcard
}

ImportRouteId W =
  | named {
      importSite     : ImportNameSelectorKey W,
      owner          : ReachableModule W,
      target         : ReachableModule W,
      sourceAtom     : EntityAtom W,
      sourceName     : StaticName W,
      localName      : StaticName W,
      exactOwner     : importSite occurs in owner.id,
      exactTarget    : importSite's resolved module = target.id,
      exactSource    : sourceAtom.owner = target and
                       sourceAtom.publicName = sourceName,
      exactLocal     : localName is the written alias when present and
                       sourceName otherwise,
      selected       : importSite selects sourceName,
      notHidden      : sourceName is absent from the exact hiding keys
    }
  | wildcard {
      importSite     : WildcardImportSelectorKey W,
      owner          : ReachableModule W,
      target         : ReachableModule W,
      sourceAtom     : EntityAtom W,
      localName      : StaticName W,
      exactOwner     : importSite.key occurs in owner.id,
      exactTarget    : importSite.key's resolved module = target.id,
      exactSource    : sourceAtom.owner = target,
      exactLocal     : localName = sourceAtom.publicName,
      notHidden      : sourceAtom.publicName is absent from the exact hiding keys
    }
```

The named destination is its explicit alias or source name. A wildcard
destination is the source public name. A route exists only when the source atom
is an entity candidate of the resolved target module, the named source matches
or the wildcard admits it, and its source name is not hidden. If the importing
module has a local entity with the same destination and namespace, that local
entity suppresses the imported route in that namespace. Other namespaces are
not suppressed. Exact equal routes are idempotent; their structural import site
is never erased.

Entity and constructor sources used by exports are proof-carrying:

```text
EntityRoute W =
  | local {
      owner      : ReachableModule W,
      localName  : StaticName W,
      origin     : PublicEntityId W,
      exactOwner : origin is declared in owner.id,
      exactName  : localName is origin's catalog leaf
    }
  | imported (route : ImportRouteId W)

ConstructorRoute W =
  | local {
      dataOrigin  : DataEntityId W,
      constructor : ConstructorId W,
      exactOwner  : constructor.owner.entity = dataOrigin.entity.entity
    }
  | imported {
      entityRoute : ImportRouteId W,
      sourceConstructor : ConstructorAtom W,
      exactSource : sourceConstructor.owner = entityRoute.target and
                    sourceConstructor.publicTypeName =
                      entityRoute.sourceAtom.publicName and
                    sourceConstructor.dataOrigin.entity =
                      entityRoute.sourceAtom.origin
    }
```

The final equality in `exactSource` is well typed only when the route's source
entity is data; construction of an imported constructor route therefore proves
that refinement as well. Constructor ownership is already carried by
`ConstructorAtom.exactOwner`.

The rule identity is structural and contains no compiler ordinal:

```text
AllConstructorSelectionKey W = {
  key   : ConstructorSelectionKey W,
  exact : key selects ExportItem.constructorSelection.all
}

NamedConstructorSelectionKey W = {
  key     : ConstructorSelectionKey W,
  entries : canonical NonemptyList (ConstructorNameKey W),
  exact   : key selects ExportItem.constructorSelection.named entries
}

SelectionCase W =
  | opaque
  | all (key : AllConstructorSelectionKey W)
  | named (key : NamedConstructorSelectionKey W)

ConstructorRuleKey W =
  | all (selection : AllConstructorSelectionKey W)
  | named {
      selection   : NamedConstructorSelectionKey W,
      constructor : ConstructorNameKey W,
      member      : constructor in selection.entries
    }

SubordinateConstructor W
    (entity : EntityAtom W) (constructor : ConstructorAtom W) =
  constructor.owner = entity.owner and
  constructor.publicTypeName = entity.publicName and
  constructor.dataOrigin.entity = entity.origin

RawRuleCase W =
  | localWildcardEntity
      (key : LocalExportSelectorKey W) (origin : PublicEntityId W)
  | localItemEntity
      (key : ExportSelectorKey W) (selection : SelectionCase W)
      (route : EntityRoute W)
  | localItemConstructor
      (key : ExportSelectorKey W) (selector : ConstructorRuleKey W)
      (route : ConstructorRoute W)
  | remoteItemEntity
      (key : ExportSelectorKey W) (selection : SelectionCase W)
      (source : EntityAtom W)
  | remoteItemConstructor
      (key : ExportSelectorKey W) (selector : ConstructorRuleKey W)
      (sourceEntity : EntityAtom W) (sourceConstructor : ConstructorAtom W)
      (compatible : SubordinateConstructor W sourceEntity sourceConstructor)
  | remoteWildcardEntity
      (key : ModuleWildcardKey W) (source : EntityAtom W)
  | remoteWildcardConstructor
      (key : ModuleWildcardKey W)
      (sourceEntity : EntityAtom W) (sourceConstructor : ConstructorAtom W)
      (compatible : SubordinateConstructor W sourceEntity sourceConstructor)
  | allFromEntity
      (key : ModuleWildcardKey W) (source : EntityAtom W)
  | allFromConstructor
      (key : ModuleWildcardKey W)
      (sourceEntity : EntityAtom W) (sourceConstructor : ConstructorAtom W)
      (compatible : SubordinateConstructor W sourceEntity sourceConstructor)
  | moduleBinding
      (key : ModuleBindingKey W) (target : ReachableModule W)
      (destination : StaticName W)
      (exact : destination is the explicit alias or the validated default leaf)

RuleCase.Valid : RawRuleCase W -> Prop

RuleCase W = {
  raw   : RawRuleCase W,
  exact : RuleCase.Valid raw
}

RuleId W = RuleCase W
```

`RuleCase.Valid` is a closed inductive family with exactly one constructor for
each displayed `RawRuleCase`. Its constructor proves that the key selects that
exact source form, every `SelectionCase` or `ConstructorRuleKey` is the exact
optional constructor selection below that same export item, the output owner is
the key's containing module, every
remote source owner equals the key's resolved target, every local source is
either a declared local origin or carries its complete structurally admissible
`ImportRouteId`, every destination is the displayed written leaf, and every constructor source satisfies the displayed
compatibility refinement. There is no catch-all validity constructor.
`RuleId` equality and ordering compare the complete displayed `raw` value; all
proof fields are erased. Consequently `RuleId` is injective in the export site,
selection mode, import route, source atom, constructor, target, and destination.

The exact destination and premise table is:

| Rule case | Destination public name | Public premises |
| --- | --- | --- |
| local wildcard entity | local declaration leaf | none |
| local item entity | written item leaf | none for local route; imported source entity for imported route |
| local item constructor | written item leaf | destination entity; plus imported source entity and constructor for imported route |
| remote item entity | written item leaf | source entity |
| remote item constructor | written item leaf | source entity, source constructor, destination entity |
| remote wildcard entity | source public name | source entity |
| remote wildcard constructor | source public type name | source entity, source constructor, destination entity |
| local `allFrom` entity | source public name | source entity |
| local `allFrom` constructor | source public type name | source entity, source constructor, destination entity |
| module binding | explicit alias or valid default leaf | none |

The conclusion is the corresponding entity, constructor, or module-binding atom
owned by the exporting module. Premises are sorted and duplicate-free.
Constructor conclusions always include the matching destination entity as a
premise, so the interface invariant holds in every round.

The selector/compiler truth table is closed:

| Source form | Entity cases | Constructor cases | Module/instance cases |
| --- | --- | --- | --- |
| local wildcard | every local importable entity | none | none |
| local item, no constructor selector | every enabled local/imported route with the written leaf | none | none |
| local item, `(*)` | same entity routes | every constructor visible through the same route | none |
| local item, named constructors | same entity routes | exactly matching written constructor leaves | none |
| remote item, no constructor selector | target entity candidates with the written leaf | none | none |
| remote item, `(*)` | same entity candidates | every matching target constructor candidate | none |
| remote item, named constructors | same entity candidates | exactly matching written constructor leaves | none |
| remote wildcard or local `allFrom` | every target entity candidate | every target constructor candidate subordinate to a copied entity | target module bindings and instances excluded |
| module export | none | none | exactly one module binding |

`opaque` is the semantic no-constructor selection, not an unknown case. `all`
and `named` carry the exact located selector key. No other `RawRuleCase` can be
constructed. Unknown names, non-data selectors, and missing constructors
produce later validation diagnostics; they do not add fabricated routes.

Ground rules contain no independently supplied premise or conclusion fields.
They are definitionally determined by their structural identity:

```text
InterfaceRule W = RuleId W

interfaceRuleId : InterfaceRule W -> RuleId W
interfaceRuleId rule = rule

interfaceRuleId_injective :
  interfaceRuleId left = interfaceRuleId right -> left = right

rulePremises : RuleId W -> canonical List (InterfaceAtom W)
ruleConclusion : RuleId W -> InterfaceAtom W

StaticRuleState W = {
  candidates : canonical List (InterfaceAtom W),
  rules      : canonical List (RuleId W)
}
```

`rulePremises` and `ruleConclusion` are total pattern matches on `RuleCase.raw`.
The destination/premise table immediately above is their defining equation for
each constructor: the conclusion owner is the exporting module selected by the
key; its name is the displayed destination; its origin/constructor comes from
the route or source atom; and the module-binding conclusion uses the stored
proof-carrying target and destination. The premise list is exactly the
displayed row, converted to `InterfaceAtom`, sorted, and deduplicated. There is
no record constructor, override, lookup table, or fallback that can associate a
different premise list or conclusion with the same `RuleId`. Hence
`interfaceRuleId_injective` is the identity-function theorem.

For a state `S`, derive `enabledImportRoutes S M` by the `ImportRouteId` rule
above from entity atoms in `S.candidates`. Derive `entityRoutes S M name` as
the union of same-module catalog entities with that leaf and enabled import
routes with `localName = name`, after the exact per-namespace local suppression
rule. `constructorRoutes S M route` is the local constructor catalog when
`route` is local, or the target constructor candidates subordinate to the
route's exact source entity when it is imported. These are definitions, not
additional extensible cases.

`baseRules W` and `expandStaticRules W S` are the canonical union of exactly
these comprehensions:

1. each local-wildcard key and each local importable catalog entity creates one
   `localWildcardEntity` rule;
2. each local-item key and each matching `entityRoutes S` value creates one
   `localItemEntity` rule with the item's exact `opaque`, `all`, or `named`
   `SelectionCase`;
3. for that same item and route, `all` creates one `localItemConstructor` rule
   per `constructorRoutes S` value, `named` creates one per matching written
   `ConstructorNameKey`, and `opaque` creates none;
4. each remote-item key and each matching target entity candidate creates one
   `remoteItemEntity` rule; its `all` and `named` selections create the
   corresponding `remoteItemConstructor` rules from subordinate target
   constructor candidates, while `opaque` creates none;
5. each remote dot/braced-wildcard key and each target entity candidate creates
   one `remoteWildcardEntity` rule and one
   `remoteWildcardConstructor` rule for each subordinate target constructor
   candidate;
6. each local `allFrom` key creates the analogous `allFromEntity` and
   `allFromConstructor` rules from the resolved target candidates; and
7. each module-export key creates exactly one `moduleBinding` rule using its
   explicit alias or already validated default leaf.

The initial state is an equation, not an implementation convention:

```text
ruleEmbeddedAtoms : RuleId W -> canonical List (InterfaceAtom W)

rawBaseRules W = baseRules W
baseRuleAtoms W =
  canonicalUnion { ruleEmbeddedAtoms rule | rule in rawBaseRules W }

S0 W = {
  rules = rawBaseRules W,
  candidates = canonicalUnion (
    baseRuleAtoms W,
    canonicalUnion { rulePremises rule | rule in rawBaseRules W },
    canonicalSet { ruleConclusion rule | rule in rawBaseRules W })
}
```

`ruleEmbeddedAtoms` is the total `RuleCase.raw` projection of every atom stored in
an entity route, constructor route, remote source, or compatible source pair;
it is empty for a module binding. This gives “base-rule atom” one exact meaning.
`wrongStaticBase` means `certificate.rounds.head != S0 W` under the derived
`DecidableEq`, including either component. No replayer may choose a smaller
seed and recover omitted atoms in a later round.

Only cases 1 and 7 and the local-route instances of cases 2 and 3 are present
in `baseRules`; all others are added by `expandStaticRules`. Every expansion
also adds every `rulePremises` element and `ruleConclusion` of every new rule to
`S.candidates`.
The compiler never creates a constructor rule for an entity atom that is not
data, never treats `opaque` as a wildcard, never copies a module binding or
instance in cases 4 through 6, and never drops the full `ImportRouteId` from a
local-item route. These seven comprehensions and the displayed selector table
are the complete definition; there is no catch-all compiler branch.

Both components grow monotonically. The actual closed finite carrier types are
not prose-defined supersets:

```text
StaticAtomCarrier W = InterfaceAtom W
StaticRuleCarrier W = RuleId W

StaticWorkItem W =
  | atom (StaticAtomCarrier W)
  | rule (StaticRuleCarrier W)

StaticWorkState W = {
  state   : StaticRuleState W,
  pending : canonical List (StaticWorkItem W),
  exact   : every pending item is already in the corresponding state list,
  unique  : pending has no duplicate
}
```

The `Fintype` instances proved above for `InterfaceAtom`, the finite structural
key refinements, and the closed `RawRuleCase` sum plus `RuleCase.Valid` give
`Fintype (StaticAtomCarrier W)` and `Fintype (StaticRuleCarrier W)`. The rule carrier is
not an opaque ordinal and the atom carrier cannot contain an owner, target,
namespace, name, origin, or constructor that lacks the displayed proof.

`leastStaticRuleClosure` starts with `S0 W` and one pending item for each atom
and rule in that exact state. It
repeatedly removes the least pending item and recomputes exactly
`expandStaticRules W state`, hence all seven displayed comprehensions, from the
exact structural key lists and values already present in the state. Each newly
derived atom or `RuleId` is inserted in canonical order and, only if absent,
enqueued once; the popped item is only a proof-relevant wakeup and cannot alter
the comprehension result. The executable step never obtains
`Fintype.elems`, enumerates the carrier, or computes its cardinality.

Termination uses the erased well-founded relation on work states in which a
recursive successor either strictly enlarges the pair of seen finite sets, or
keeps both seen sets equal and strictly shortens `pending`. Strict inclusion of
subsets of the two closed finite carrier types is well founded, and the
duplicate-free pending list makes the equal-seen case finite. Thus no caller
fuel and no run-time carrier-cardinality computation exists.

`StaticRuleClosureOf` independently states base inclusion, closure under each
of the seven displayed comprehensions, and leastness. Soundness and completeness
prove that the worklist result contains exactly the least syntax-justified
atoms and rules. A declarative batch `expandStaticRules` remains the defining
successor used by certificates; worklist soundness and batch-replayer soundness,
together with `StaticRuleClosureOf.functional`, prove propositional equality of
their canonical results.

Let:

```text
candidateRuleState W = leastStaticRuleClosure W
A = candidateRuleState.candidates.length
R = candidateRuleState.rules.length
```

These are the only meanings of `A` and `R`.

### Interface saturation and selector validation

Let `U` be the least static candidate list and `rules` its ground rule list.
For `I` a subset of `U`:

```text
stepInterfaces(I) =
  I union { ruleConclusion rule |
            rule in rules and every rulePremises rule element is in I }
```

This transformer is inflationary and monotone. Iteration starts at the empty
set. Every non-fixed round adds at least one of the `A` candidates, so equality-
checked iteration with fuel `A` returns the least fixed point; one following
check must confirm equality. The independent `LeastInterfacesOf` judgment
states candidate membership, rule closure, and leastness without mentioning the
executor.

Kernel evaluation need not normalize a large nested fixed-point proof term.
The certificate forms are closed:

```text
StaticRuleClosureCertificate W = {
  rounds : NonemptyList (StaticRuleState W)
}

InterfaceSaturationCertificate W state = {
  rounds : NonemptyList (canonical List (InterfaceAtom W))
}

CertificateError =
  | wrongStaticBase
  | wrongStaticSuccessor (round : Nat)
  | staticNotFixed
  | wrongInterfaceBase
  | wrongInterfaceSuccessor (round : Nat)
  | interfaceNotFixed

replayStaticRuleClosure :
  StaticRuleClosureCertificate W ->
  Except CertificateError (StaticRuleState W)

replayInterfaceSaturation :
  InterfaceSaturationCertificate W state ->
  Except CertificateError (canonical List (InterfaceAtom W))
```

An untrusted build step may generate either list of rounds. The pure replayers
recompute every displayed comprehension, premise test, canonicalization, and
final equality; they do not trust stored deltas, counts, hashes, or a claimed
leastness proof. Replayer soundness plus monotonicity yields the independent
`StaticRuleClosureOf` and `LeastInterfacesOf` judgments. Replayer completeness
shows that certificates produced from executor traces are accepted. Direct-
executor soundness, replayer soundness, and functionality of the corresponding
judgment prove propositional equality of their canonical results; no theorem
claims definitional equality between separately implemented computations that
take different inputs.

After saturation, validation checks every selector occurrence and every module
interface. It checks named import/export existence, hiding existence,
constructor ownership and visibility, ambiguity, module-binding ambiguity, and
module/entity collisions. A constructor atom without its matching entity is an
executor invariant violation proved unreachable, not a language diagnostic.

Ambiguity evidence retains exact rule and import provenance:

```text
InterfaceContributionSite W =
  | rule (id : RuleId W)
  | importRoute (id : ImportRouteId W)

CandidateWitness W = {
  atom  : InterfaceAtom W,
  sites : canonical NonemptyList (InterfaceContributionSite W)
}

CanonicalAmbiguitySite
  (W : ParsedReachableWorkspace)
  (witnesses : canonical NonemptyList (CandidateWitness W)) = {
  site  : InterfaceContributionSite W,
  exact : site is the least element of the union of every witnesses.sites
}
```

For import environments, `sites` contains every exact `ImportRouteId` that
contributes the atom. For public-interface diagnostics, it contains every
satisfied immediate `RuleId` whose `ruleConclusion` is that atom. Candidate witnesses
are grouped by distinct atom and sorted structurally. Thus cross-import
ambiguity retains the import selector and route, and public ambiguity retains
the structural rule case that introduced every candidate.

`InterfaceContributionSite` has a total structural order. An import route is
ordered by its exact import selector site and then by its complete route fields.
A rule is ordered first by the primary source site embedded in its `RuleId`,
then by the complete `RuleCase.raw`; for an export rule the primary site is its
export selector or module-wildcard site, never a source atom's support site.
`CanonicalAmbiguitySite W witnesses` contains the least site in the union of
all `witnesses.sites`. Every ambiguity diagnostic without a unique triggering
selector stores this value and a proof of the defining equality. Thus changing
iteration or discovery order cannot move an ambiguity diagnostic.

### Typed selector and diagnostic keys

Selector keys are refinements of ADR-0016 occurrence identities or certified
structural sites when the selected syntax is a direct marker rather than an
`OccurrenceRole`:

```text
ImportSelectorKey
WildcardImportSelectorKey
ImportNameSelectorKey
ImportAliasKey
HidingSelectorKey
LocalExportSelectorKey
RemoteExportSelectorKey
ExportSelectorKey
ExportAliasKey
ModuleWildcardKey
ConstructorSelectionKey
AllConstructorSelectionKey
NamedConstructorSelectionKey
ConstructorNameKey
ModuleBindingKey
UnqualifiedConstructorKey
PragmaDataKey
```

Each type proves that its structural site selects the corresponding ADR-0015
node and exposes an `OccurrenceId` only when ADR-0016 has the required role.
`ImportNameSelectorKey` refines `ImportSelectorKey` to a named entry, and
`ExportSelectorKey` below refines the local/remote sums to an export item.
`ModuleWildcardKey` retains the exact module-reference payload and wildcard
marker. `ConstructorSelectionKey` retains the owning export item and complete
`all` or `named` selection as a certified structural site; an `all` marker is
not fabricated as an occurrence. `ConstructorNameKey` refines a named selection to
one exact constructor occurrence. A plain `Identifier` is never used as a
substitute for these identities. `UnqualifiedConstructorKey` contains a typed
`LookupUse` and `LookupPath` whose final occurrence is either a one-component
expression/call or a child-bearing one-component named pattern; it cannot be
constructed for a childless binding candidate. `PragmaDataKey` refines an exact
`pragmaTarget` occurrence to a `noGenericInstanceFor` target.

The closed diagnostic sums are:

```text
GraphDiagnostic =
  | undeclaredExternalLibrary GraphReferenceSite ExternalLibraryName
  | missingModule GraphReferenceSite ModuleId

Phase2Diagnostic =
  | surface SourceId (parserIndex : Nat) Multi.SurfaceDiagnostic
  | graph GraphDiagnostic

CatalogDiagnostic W =
  | duplicateDeclaration DeclarationNamespace Identifier
      (canonical NonemptyList (DeclarationId W))
  | duplicateMember MemberNamespace Identifier
      (canonical NonemptyList (MemberId W))
  | duplicateUnconditionalBinder (group : SimultaneousGroupKey W) Identifier
      (canonical NonemptyList (UnconditionalGroupMember W group))
  | multipleContractConstructors (ContractId W)
      (canonical NonemptyList (MemberId W))
  | multipleContractFallbacks (ContractId W)
      (canonical NonemptyList (MemberId W))
  | defaultBindingRequiresAlias (ModuleBindingKey W) PathSegment

InterfaceDiagnostic W =
  | unknownImportName (ImportNameSelectorKey W) Identifier
  | unknownHiddenName (HidingSelectorKey W) Identifier
  | unknownExportName (ExportSelectorKey W) Identifier
  | nonDataConstructorSelector (ConstructorSelectionKey W) (PublicEntityId W)
  | unknownExportConstructor (ConstructorNameKey W) Identifier
      (DataEntityId W)
  | ambiguousImport (ReachableModule W) EntityNamespace Identifier
      (candidates : canonical NonemptyList (CandidateWitness W))
      (site : CanonicalAmbiguitySite W candidates)
  | ambiguousExport (ExportSelectorKey W) Identifier
      (canonical NonemptyList (CandidateWitness W))
  | ambiguousPublicEntity (ReachableModule W) Identifier
      (candidates : canonical NonemptyList (CandidateWitness W))
      (site : CanonicalAmbiguitySite W candidates)
  | ambiguousPublicModule (ReachableModule W) Identifier
      (candidates : canonical NonemptyList (CandidateWitness W))
      (site : CanonicalAmbiguitySite W candidates)
  | publicModuleEntityCollision (ReachableModule W) Identifier
      (candidates : canonical NonemptyList (CandidateWitness W))
      (site : CanonicalAmbiguitySite W candidates)

LexicalDiagnostic W C =
  | duplicatePatternBinder (group : PatternBinderGroupKey W) Identifier
      (canonical NonemptyList (PatternBinderGroupMember W C group))
  | lookupFailure (LookupFailure W C)
  | unqualifiedConstructor (UnqualifiedConstructorKey W)
      (canonical NonemptyList (ConstructorTarget W))
  | unknownPragmaData (PragmaDataKey W) Identifier
```

`Phase2Diagnostic.Applies` has two disjoint source-reference cases. For an
external reference whose named library is undeclared, exactly
`undeclaredExternalLibrary` applies and target membership is not tested. For
every other reference, including a declared external reference, exactly
`missingModule` applies when its pure target is absent. A `surface source i d`
applies exactly when parsing that source returns an error list whose in-bounds
element satisfies `errors[i] = d`; every such index is emitted once. These are
the only phase-2 rules.

The interface diagnostic decision table is exact. In the following table,
candidate equality is structural atom equality and every candidate/support list
is canonical:

| Site or binding group | Zero candidates | One candidate | More than one distinct candidate |
| --- | --- | --- | --- |
| named import source | `unknownImportName` | valid selector | selector creates all routes; any resulting same-name/same-namespace local collision is the one binding-group `ambiguousImport` below |
| hiding name in target public entity set | `unknownHiddenName` | valid | valid; existence, not uniqueness, is tested |
| local or remote named export item | `unknownExportName`; suppress constructor diagnostics | validate the optional constructor selector as below | `ambiguousExport` at the exact export item; suppress per-candidate constructor diagnostics |
| final item-import local name and namespace after local suppression | no binding | valid binding | one `ambiguousImport` at its `CanonicalAmbiguitySite` |
| final public entity name | no entity | valid entity | one `ambiguousPublicEntity` at its `CanonicalAmbiguitySite` |
| final public module-binding name | no module binding | valid module binding | one `ambiguousPublicModule` at its `CanonicalAmbiguitySite` |

For the unique entity selected by an export item, absence of a constructor
selector is valid. An `all` or `named` selector on a non-data entity emits
exactly `nonDataConstructorSelector` at the whole selection and does not emit a
per-name missing-constructor error. `all` on data is valid even when its visible
constructor set is empty. For a named selection on data, each written
`ConstructorNameKey` with no constructor in the exact visible subset emits one
`unknownExportConstructor`; present names are valid and do not suppress missing
siblings. A final public name with both an entity and a module binding emits
`publicModuleEntityCollision`. That collision does not suppress an independently
applicable within-entity or within-module ambiguity, so all applicable closed
constructors coexist. Likewise a selector/import ambiguity does not suppress a
final public-interface ambiguity justified by the saturated candidate set;
phase 6 accumulates both exact keys and never short-circuits within the phase.

Catalog diagnostics likewise coexist for distinct keys. Each duplicate
constructor applies exactly to the complete sorted candidates with one
displayed namespace, owner/group, and spelling when that list has length at
least two. Each multiple-contract constructor applies exactly to all matching
unnamed members of its contract when that list has length at least two.
`defaultBindingRequiresAlias` applies exactly when a module-binding form omits
an alias and `PathSegment.asIdentifier?` returns `none`. Their candidate lists
prove these conditions rather than admitting an unrelated structural id.
Within the lexical phase, one lookup site yields exactly one farthest
`lookupFailure`, one `unqualifiedConstructor`, or a success; a childless binder
candidate is outside that trichotomy. `unqualifiedConstructor` applies only
after ordinary term/constructor lookup and the allowed same-name and class-
method fallbacks are empty, while its exact context has a nonempty generic user
constructor list. `unknownPragmaData` applies exactly to an empty local-data
match. `duplicatePatternBinder` contains every classified binder with one arm
and spelling, and applies exactly when that list has length at least two.
Missing pragma targets and duplicate classified binders are independently
accumulated with other lexical sites.

The executor packages the dependent phase index rather than erasing it:

```text
ResolutionFailure =
  | phase2
      (canonical NonemptyList Phase2Diagnostic)
  | catalog
      (W : ParsedReachableWorkspace)
      (canonical NonemptyList (CatalogDiagnostic W))
  | interface
      (W : ParsedReachableWorkspace)
      (canonical NonemptyList (InterfaceDiagnostic W))
  | lexical
      (W : ParsedReachableWorkspace)
      (C : PatternClassification W)
      (canonical NonemptyList (LexicalDiagnostic W C))
```

This is the closed source-failure type. Diagnostics from different phase
indices are never placed in one ill-typed list, and the constructor itself
records the first failing phase.

`ExportSelectorKey` is the sum of local and remote export-item keys; wildcard
and module-binding sites have their own disjoint key types.
`GraphReferenceSite` is the dependent pair of a `GraphReadyModule` and its
`Structural.ModuleReferenceSite`; it provides module and primary span before a
successful `ParsedReachableWorkspace` exists. The catalog phase uses
`LocalSiteId W` because no pattern classification exists yet; only the lexical
phase constructs proof-carrying pattern-binder `LocalId W C` values from the
final `PatternClassification W`.

Diagnostic trigger identity is a closed sum:

```text
Phase2Trigger =
  | surface (source : SourceId) (parserIndex : Nat)
  | graph (site : GraphReferenceSite)

CertifiedStructuralSite W = {
  key      : SyntaxNodeKey,
  selected : Structural.SelectedSite,
  exact    : exists G in W.index.modules,
               key.module = moduleId G and
               Structural.SelectsModule G.parsed key.address selected
}

ResolverTrigger W =
  | declaration (DeclarationId W)
  | member (MemberId W)
  | localSite (LocalSiteId W)
  | occurrence (OccurrenceId W)
  | structural (CertifiedStructuralSite W)
  | contribution (InterfaceContributionSite W)

structuralPrimarySpan : CertifiedStructuralSite W -> SourceSpan
contributionStructuralSite :
  InterfaceContributionSite W -> CertifiedStructuralSite W

phase2Trigger : Phase2Diagnostic -> Phase2Trigger
catalogTrigger : CatalogDiagnostic W -> ResolverTrigger W
interfaceTrigger : InterfaceDiagnostic W -> ResolverTrigger W
lexicalTrigger : LexicalDiagnostic W C -> ResolverTrigger W

phase2Module : Phase2Diagnostic -> ModuleId
phase2Span : Phase2Diagnostic -> Option SourceSpan
resolverModule : ResolverTrigger W -> ModuleId
resolverSpan : ResolverTrigger W -> SourceSpan
```

`structuralPrimarySpan` is the primary located ancestor retained by
ADR-0016 `SelectedSite`. `contributionStructuralSite` is the following total
case split: a named import route uses its source-name occurrence; a wildcard
import route uses its selected wildcard marker; a local wildcard rule uses its
local export wildcard marker; local/remote item rules use the export source or
constructor-selection site selected by the rule key; remote wildcard and
`allFrom` rules use their selected wildcard/module-reference site; and a module
binding uses its explicit alias occurrence when present and otherwise its
module-reference occurrence. Marker cases are certified direct structural
sites, not fabricated `OccurrenceId` values. This projection never uses an atom
support site. Module and span for a declaration/member/local/occurrence trigger
use ADR-0016 `primarySpan`; a structural trigger uses its key and
`structuralPrimarySpan`; and a contribution delegates to its certified
structural site.

`CertifiedStructuralSite` equality and ordering use only `key`; ADR-0016
selection functionality proves that `selected` is uniquely determined and its
proof is erased. Its order is the ADR-0016 module/source structural order, so a
direct marker and an occurrence identity participate in one canonical trigger
order without text or span tie-breaking.

The primary trigger projection for every source diagnostic constructor is the
following closed table. `least` means the head of the already canonical
nonempty candidate list, not an executor-discovery choice.

| Diagnostic constructor | Exact primary trigger |
| --- | --- |
| `surface source i d` | `Phase2Trigger.surface source i`; span is `d`'s ADR-0015 optional primary span |
| either `GraphDiagnostic` constructor | `Phase2Trigger.graph` of its stored `GraphReferenceSite` |
| `duplicateDeclaration` | declaration identity of the least stored candidate |
| `duplicateMember` | member identity of the least stored candidate |
| `duplicateUnconditionalBinder` | local-site identity of the least stored group member's `local.site` |
| `multipleContractConstructors` or `multipleContractFallbacks` | member identity of the least stored candidate |
| `defaultBindingRequiresAlias` | occurrence selected by the stored `ModuleBindingKey` |
| `unknownImportName` | occurrence selected by the stored `ImportNameSelectorKey` |
| `unknownHiddenName` | occurrence selected by the stored `HidingSelectorKey` |
| `unknownExportName` or `ambiguousExport` | occurrence selected by the stored `ExportSelectorKey` |
| `nonDataConstructorSelector` | certified whole-selection structural site stored by the `ConstructorSelectionKey` |
| `unknownExportConstructor` | constructor-name occurrence selected by the stored `ConstructorNameKey` |
| `ambiguousImport`, `ambiguousPublicEntity`, `ambiguousPublicModule`, or `publicModuleEntityCollision` | stored `CanonicalAmbiguitySite.site` as a contribution trigger |
| `duplicatePatternBinder` | local-site identity of the least stored group member's `binder.local.site` |
| `lookupFailure` | its stored farthest-failure occurrence `at` |
| `unqualifiedConstructor` | final component stored by `UnqualifiedConstructorKey` |
| `unknownPragmaData` | pragma-target occurrence stored by `PragmaDataKey` |

Thus every later-phase diagnostic has a non-optional `ResolverTrigger`; every
phase-2 diagnostic has a non-optional `Phase2Trigger`; and only a parser
diagnostic may have no source span. The `ReachableModule.id` stored by an
ambiguity constructor is proved equal to the module projected from its trigger.
Every other constructor's module is derived rather than independently stored.
There is no default projection case, arbitrary span field, first-candidate
fallback, or unstructured message constructor. Configuration-only
`StandardBundleError` has no source trigger: its exact ordering key is the
constructor rank followed by its stored or derived canonical file id, input
index, path bytes, and remaining displayed fields, as defined in the standard-
bundle section.

Each phase defines an independent `Diagnostic.Applies` relation with one rule
per displayed constructor. The executor proves, in both directions, that a
constructor occurs in the canonical first-failing-phase output exactly when its
`Applies` rule holds. Candidate and site lists are part of that equivalence.

Phase 2 uses its source/module/span order above, with the original position in
that module's parser list as the final tie-break. It never deduplicates a
`surface` element, even if two elements compare equal in every diagnostic
field. Each later phase sorts by displayed constructor rank, the module and
nonoptional primary span projected from `ResolverTrigger`, the complete trigger
identity, then all remaining fields. Lists are lexicographic and proofs are
erased. Exact
duplicates in those later resolver phases are removed only after sorting.

### Import and module-binding candidate environments

After interface validation, item-import candidates are keyed by local spelling
and `EntityNamespace`. Repeated paths to the same origin are idempotent. Two
different origins in the same namespace and local spelling produce one
`ambiguousImport` at the `CanonicalAmbiguitySite` of all contributing routes
unless a local declaration shadows that namespace. Candidates in different
entity namespaces may coexist, matching the language's separate term, type,
and class lookup.
If such candidates are later exported by the category-free `export {name}`
form, public-interface validation reports their cross-namespace ambiguity.

Module-import candidates are keyed separately by local spelling. Equal targets
are idempotent and distinct targets are all retained. A module binding may share
a spelling with a term, type, class, or contract binding; ADR-0017 does not
reject the workspace merely because the spelling is unused. Dotted-root priority
and the zero/one/many qualifier rule below make every use deterministic: a term
candidate forces receiver interpretation, while multiple category-valid
qualifiers produce a typed `LookupFailure.ambiguous`. Publicly exporting
colliding module and entity bindings remains an eager public-interface error
because a downstream module selector has no category annotation.

### Lexical frames and sequential suffix scopes

All declarations in one module are mutually visible to module bodies. All
named contract members are mutually visible within the contract. Source order
affects identity, diagnostics, and sequential body scope, not declaration
visibility.

Term lookup priority is:

1. the innermost lexical suffix/block/arm/loop/lambda local frame;
2. the current callable's simultaneous parameter frame;
3. contract fields and functions when inside that contract;
4. module-local term declarations;
5. selected-import term candidates; and
6. term intrinsics.

Type lookup priority is innermost type-variable frames, contract-local data and
type aliases, module-local data/type aliases/contracts, selected-import types,
then type intrinsics. Class lookup uses class declarations in the applicable
module scope, selected-import classes, then class intrinsics. The first
nonempty priority level shadows later levels; multiple distinct candidates at
one level are ambiguous.

The frame transitions are exhaustive:

- data and type-alias parameters are simultaneous and visible throughout their
  constructor types or alias body;
- class outer `forall` binders are simultaneous and visible in the class
  predicates, head, and every method signature; a method's own `forall` frame
  is nested inside the class frame;
- instance outer `forall` binders are simultaneous and visible in predicates,
  the instance head, and every method definition; callable method binders are
  nested inside the instance frame;
- contract type parameters are visible in nested data/type aliases, fields,
  functions, the contract constructor, and fallback; a member's own type frame
  is nested and may shadow the contract frame;
- function, method, constructor, and fallback `forall` groups are visible in
  predicates, parameter/return types, and bodies;
- callable parameter types are resolved before term parameters are installed;
  all parameters then enter one simultaneous parameter frame;
- a lambda resolves parameter types in the enclosing type environment, installs
  all lambda parameters simultaneously, and gives its body a child scope;
- a block gets an independent child scope and does not leak bindings;
- an `if` condition uses the current scope; then and optional else bodies are
  independent children and neither changes the continuation;
- match scrutinees use the current scope; constructor occurrences and comptime
  expressions in all arm patterns resolve before binders are installed; all
  binders of one arm form one simultaneous group visible only in that arm body;
- a loop creates one loop scope; initializer items run left to right, each
  initializer `let` affects later initializers, the condition, body, and post
  list; the body is a child that does not leak into post items; no loop binding
  escapes; and
- field initializers see contract type parameters and the complete contract
  owner table but no callable-local frame.

Every recursive type, expression, pattern, for-item, and statement child not
listed above is visited in ADR-0015/ADR-0016 child order under the inherited
current frame and does not mutate that frame. In particular, annotations,
calls, receivers, indexes, prefix/infix/assignment operands, return values,
conditions, post items, groups, tuples, proxy/comptime forms, and assembly
slices create no unlisted lexical scope. The displayed transitions are the
complete interpretation of every ADR-0016 `ScopeRole`; there is no generic
scope constructor.

Every body starts at its ADR-0016 `bodyEntry` scope. Processing an ordinary
non-`let` statement reuses the current `ScopeId`; ADR-0016 intentionally has no
virtual continuation site for it. An ordinary `let` annotation and initializer
resolve in the current scope, then processing advances to that statement's
unique `sequentialContinuation` scope and installs the binder there, even while
the lexical phase retains an independent diagnostic from the initializer. A
later `let` with the same spelling is valid shadowing and becomes the unique
innermost candidate from its continuation onward. A body `let` may likewise
shadow a parameter or match binder.

The same rule applies to the `LetBinding` inside a for initializer: its
annotation and initializer use the current loop-header/continuation scope, then
the exact for-init `sequentialContinuation` becomes current for later
initializers, the condition, the child body, and post items. A non-let for
initializer and every post item reuse the current scope. Thus the only suffix
scope identities are the ordinary-let and for-init-let sites exported by
ADR-0016; the resolver never fabricates a scope after another statement. This rule
is required by sequential repeated `ptr` and `prx` bindings in the canonical
standard sources.

### Typed lookup uses and paths

Every lookup request is tied to one exact ADR-0015 syntax shape:

```text
LookupUse W =
  | typeName
  | boundedClass
  | predicateClass
  | instanceClass
  | expressionTerm
  | patternConstructor
  | pragmaClass

LookupPath (W : ParsedReachableWorkspace) (use : LookupUse W) = {
  anchor     : SyntaxNodeKey,
  components : NonemptyList (OccurrenceId W),
  ...proof that anchor and components select exactly one of:
     - the QualifiedName of a TypeExpr.named for typeName,
     - the QualifiedName of a bounded forall for boundedClass,
     - the predicate class QualifiedName for predicateClass,
     - the instance class QualifiedName for instanceClass,
     - the maximal name/select spine of an expression or call callee for
       expressionTerm,
     - the QualifiedName of Pattern.named for patternConstructor, or
     - the one IdentifierOccurrence target of a class-kind pragma...
  ...proof that components are in AST order and carry the exact allowed
     OccurrenceRole for use...
}
```

An expression spine contains only a root `Expression.name` followed by exact
`Expression.select` field occurrences. A call may use that spine as its callee.
If a select receiver is any other expression, including a call result, it is a
receiver selector and not a qualifier component. Groups are retained and stop
spine extraction. No text-only dotted string can construct `LookupPath`.

The two specialized lexical diagnostic keys are exact refinements:

```text
UnqualifiedConstructorContext =
  | bareExpression | bareCall | childBearingPattern

UnqualifiedConstructorKey W = {
  use     : LookupUse W,
  path    : LookupPath W use,
  context : UnqualifiedConstructorContext,
  ...proof that path has exactly one component and that its anchor selects the
     displayed expression, call callee, or named pattern with nonempty children
     required by context...
}

PragmaDataKey W = {
  occurrence : OccurrenceId W,
  ...proof that occurrence selects the target of exactly one
     noGenericInstanceFor pragma...
}
```

The occurrence stored by either key is therefore recoverable without a text
search. In particular, `UnqualifiedConstructorKey` is uninhabited for a
childless one-component pattern candidate.

### Owner tables, targets, and qualifier automaton

Every visible data binding has a constructor owner table restricted to its
currently visible constructor subset. Every visible class binding has its
declared method table. Every visible contract binding has a type table containing
nested data and type aliases and a term/member table containing named fields and
functions. Contract constructors and fallbacks are unnamed. Member visibility
is lexical: `public` does not change the owner table. Import aliasing changes
only the leading visible owner name; structural origins never change.

Resolved values are proof-carrying refinements:

```text
ResolvedEntityKind =
  | function | data | typeAlias | class | contract | nestedData
  | nestedTypeAlias

ResolvedMemberKind =
  | dataConstructor | contractField | contractFunction | classMethod

ResolvedEntity W = {
  kind   : ResolvedEntityKind,
  origin : EntityId W,
  ...proof that origin selects exactly kind...
}

ResolvedMember W = {
  kind   : ResolvedMemberKind,
  origin : MemberId W,
  ...proof that origin selects exactly kind...
}

ResolvedTarget W C =
  | entity (ResolvedEntity W)
  | member (ResolvedMember W)
  | local (LocalId W C)
  | module (ReachableModule W)
  | intrinsic IntrinsicId

ExpectedTarget = module | type | class | term | constructor | classMethod

IntrinsicConstructorId =
  constructorTrue | constructorFalse | constructorUnit |
  constructorPair | constructorInl | constructorInr

IntrinsicTypeId =
  typeWord | typeBool | typeInteger | typeUnit | typeArrow |
  typePair | typeSum

IntrinsicClassId = classInvokable | classInt

ConstructorTarget W =
  | user (ConstructorId W)
  | intrinsic IntrinsicConstructorId

IntrinsicClassMethodId =
  methodInvokableInvoke | methodIntFromInteger

ClassMethodTarget W =
  | user (ClassMethodId W)
  | intrinsic IntrinsicClassMethodId
```

The compatibility relation is closed. `module` accepts only modules. `type`
accepts type variables, data, type aliases, contracts, nested contract types,
and type intrinsics. `class` accepts class entities and class intrinsics. `term`
accepts term locals, functions, fields, contract functions, constructors, and
term/constructor intrinsics. The remaining two categories accept only their
matching members or intrinsics. Every other pair is
`LookupFailureReason.wrongKind`.

Qualifier traversal uses the closed state sum:

```text
QualifierState W =
  | module (ReachableModule W)
  | data (OwnedDataId W)
  | class (ResolvedEntity W)
  | contract (ResolvedEntity W)
  | intrinsicType IntrinsicTypeId
  | intrinsicClass IntrinsicClassId

TerminalTarget W C =
  | resolved (ResolvedTarget W C)
  | constructor (ConstructorTarget W)
  | classMethod (ClassMethodTarget W)

LookupFailureReason W C =
  | unknown (expected : ExpectedTarget)
  | wrongKind (expected : ExpectedTarget)
      (canonical NonemptyList (ResolvedTarget W C))
  | ambiguous
      (canonical NonemptyList (ResolvedTarget W C))

LookupFailure W C = {
  use      : LookupUse W,
  path     : LookupPath W use,
  consumed : Nat,
  at       : OccurrenceId W,
  reason   : LookupFailureReason W C,
  ...proof that consumed < path.components.length and
     at = path.components[consumed]...
}
```

The expected category is a total function:

| `LookupUse` | `ExpectedTarget` |
| --- | --- |
| `typeName` | `type` |
| `boundedClass`, `predicateClass`, `instanceClass`, `pragmaClass` | `class` |
| `expressionTerm` | `term` |
| `patternConstructor` | `constructor` |

The transition table is exhaustive:

| State | Next component may select |
| --- | --- |
| module | one public module binding or entity in that module interface; subordinate constructor atoms are not direct module children |
| data | one visible constructor; it is terminal |
| class | one declared user class method; it is a terminal term target |
| contract | one nested data/type alias, field, or function; a nested data may continue to its constructor, while every term member is terminal |
| intrinsic type `bool` | `true` or `false`, terminal intrinsic constructors |
| intrinsic type `pair` | `pair`, a terminal intrinsic constructor |
| intrinsic type `sum` | `inl` or `inr`, terminal intrinsic constructors |
| intrinsic type `word`, `integer`, unit, or arrow | no component |
| intrinsic class `invokable` | only `invoke -> methodInvokableInvoke`, a terminal term target |
| intrinsic class `Int` | only `fromInteger -> methodIntFromInteger`, a terminal term target |

A module entity that is data, class, or contract enters the corresponding
state when components remain; a type alias or ordinary term is terminal.
Class methods never become qualifier states. If an expression traversal reaches
any terminal term with components remaining, that target becomes the receiver
base and the remaining select occurrences become deferred receiver selectors.
For non-expression uses, remaining components after a terminal target are a
wrong-kind failure.

Root selection and traversal are total:

1. For `expressionTerm`, perform ordinary term lookup first. The first nonempty
   lexical priority level wins. One target is the terminal base; multiple
   distinct targets are an ambiguity. Only an empty ordinary term lookup permits
   qualifier-root lookup.
2. Other uses start with their category-valid module, data, class, contract, and
   intrinsic qualifier roots. Except for the pattern case in step 3, a bare
   final component is also checked against the use's expected target category.
3. A one-component child-bearing `patternConstructor` bypasses that general
   bare-final check and runs this ordered decision: an intrinsic constructor
   first; otherwise the unique same-name user constructor; otherwise
   `unqualifiedConstructor` for the complete nonempty visible generic-user-
   constructor set; otherwise the ordinary unknown failure. A childless candidate is classified by
   `PatternClassification` and never constructs this `LookupUse`.
4. Traverse left to right with the table above, retaining every distinct state
   supported by the current component. Exact equal targets are idempotent.
5. One full target succeeds. Multiple distinct full targets are ambiguous. For
   an expression, one terminal term before the end succeeds as a receiver base;
   multiple distinct terminal bases are ambiguous.
6. If no target succeeds, select failures with the greatest `consumed` value.
   At that same farthest component, `ambiguous` outranks `wrongKind`, which
   outranks `unknown`; candidates of the selected reason are unioned, sorted,
   and deduplicated. Earlier failures are discarded.

Thus diagnostics always point at the farthest component justified by actual
AST traversal. A local, parameter, field, module-local, or imported term forces
receiver interpretation over an equally spelled qualifier. No later type fact
may reinterpret that root.

After ordinary bare-term lookup is empty, a one-component expression/call tries
the same-name constructor rule below and then the user-defined bare class-method
fallback. That fallback contains user `ClassMethodId` values only;
`methodInvokableInvoke` and `methodIntFromInteger` are available exclusively
through their qualified intrinsic-class transitions. If neither fallback
applies but one or more visible non-same-name user constructors have that leaf,
the resolver emits `unqualifiedConstructor` with exactly those sorted
`ConstructorTarget.user` candidates. Only when that list is also empty does it
report the ordinary farthest `LookupFailure`.

### Kind-dependent pragma resolution

Pragma targets do not share one string lookup rule:

- `noCoverageCondition`, `noPattersonCondition`, and
  `noBoundedVariableCondition` construct `LookupUse.pragmaClass` and use the
  ordinary class lookup, including the lowest-priority class intrinsics; and
- each `noGenericInstanceFor` target resolves to the canonical nonempty list of
  every data declaration in the same source module whose declared leaf equals
  the target: top-level data plus data nested directly in any local contract.
  It does not inspect imports, standard modules merely because they are roots,
  type aliases, contracts themselves, or intrinsics.

Multiple matching local data declarations for `noGenericInstanceFor` are the
intended result, not an ambiguity. An empty match produces
`unknownPragmaData` at the exact `pragmaTarget` occurrence. The resolved pragma
sum distinguishes `classTarget` from `localDataTargets`, so later consumers
cannot confuse the two policies.

```text
ResolvedPragmaTarget W C =
  | classTarget {
      occurrence : OccurrenceId W,
      target     : ResolvedTarget W C,
      exact      : occurrence selects one of the three class-kind pragmas and
                   target satisfies ExpectedTarget.class at that lookup
    }
  | localDataTargets {
      key     : PragmaDataKey W,
      targets : canonical NonemptyList (OwnedDataId W),
      exact   : targets are every same-source-module top-level or directly
                contract-nested data declaration with key's spelling
    }
```

### Same-name constructor shorthand

M2c admits exactly one user-defined unqualified constructor shorthand. Given a
local leaf `T`, perform type-namespace lookup with the exact priority above. The
first nonempty level must contain exactly one target and that target must be
data; a non-data target or multiple distinct targets yields no shorthand.
Inspect that data binding's visible constructor table. If it contains exactly
one constructor whose declared leaf is also `T`, then a one-segment expression
or call spelled `T` resolves to that constructor after ordinary term lookup has
found no candidate. The same rule classifies a one-segment pattern `T` or
`T(patterns...)` as that constructor.

Visibility and aliases are respected. A hidden constructor does not qualify.
An imported binding aliased from `T` to `U` still exposes the constructor as
`U.T`; because the declared leaf is not `U`, bare `U` is not same-name
shorthand. Exact `U.T` remains valid. Re-export/import paths cannot restore a
constructor absent from their source binding's visible subset; a separately
authorized route remains an independent contribution.

For a one-component childless named pattern, an intrinsic constructor or a
unique same-name user constructor classifies the site as a constructor. When
neither case applies, the site is a binder even if one or more visible generic
constructors have the same leaf `C`. Generic constructor visibility alone must
not capture a childless binding occurrence. The catalog and interface phases
have already rejected duplicate constructors and ambiguous type bindings, so a
successful classification cannot contain multiple same-name targets.

A one-component name with child patterns uses the same ordered decision:
intrinsic first, then the unique same-name case. Only if both are absent and its
leaf names any other visible user constructor,
`unqualifiedConstructor` is emitted with exactly the sorted
`ConstructorTarget.user` candidates. The same generic-bare rejection applies
to one-component expressions and calls, but never to a childless pattern.
Qualified `T.C` uses the owner table, and leading-dot constructors remain M2d
deferred selectors.

Resolver policy owns the following total classification; ADR-0016 supplies
only its structural candidate sites:

```text
PatternCandidateResult W =
  | binder
  | intrinsicConstructor IntrinsicConstructorId
  | sameNameConstructor (ConstructorId W)

PatternClassification W = {
  result : PatternCandidateSite W -> PatternCandidateResult W,
  ...proof that result follows the intrinsic, same-name, then binder
     priority above for every and only structural pattern candidate site...
}
```

Qualified, child-bearing, tuple, group, wildcard, comptime, and leading-dot
patterns are resolved by their own syntax cases and are not fabricated as
`PatternCandidateSite` values. After classification, binders from the same
match arm are checked as one simultaneous group; a repeated classified binder
produces `duplicatePatternBinder`. Constructor-classified sites never become
`LocalId` values.

ADR-0017 defines the refinement without adding another structural address:

```text
LocalId (W : ParsedReachableWorkspace) (C : PatternClassification W) = {
  site    : LocalSiteId W,
  witness :
    (exists unconditional : UnconditionalLocalSite W,
      unconditional.site = site) or
    (exists candidate : PatternCandidateSite W,
      candidate.site = site and C.result candidate = binder)
}

PatternBinderId W C = {
  local     : LocalId W C,
  candidate : PatternCandidateSite W,
  exactSite : candidate.site = local.site,
  classified : C.result candidate = binder
}

PatternBinderGroupKey W = {
  scope : ScopeId W,
  exact : scope.role = ScopeRole.matchArmBindings
}

PatternBinderGroupMember W C (group : PatternBinderGroupKey W) = {
  binder : PatternBinderId W C,
  owner  : Structural.localOwner binder.local.site = group.scope
}
```

Every unconditional local site constructs a `LocalId W C`; a pattern candidate
does so exactly when `C` classifies that site as a binder. Equality, ordering,
owner scope, and primary span delegate to `site`, and the classification proof
is erased. No caller supplies `C`.

This shorthand is required for canonical sources that use forms such as
`Error(...)`, `ABIDecoder(...)`, `Method`, `Fallback`, `Proxy`, and `storage`
where data and constructor leaves coincide.

### Deferred M2d selectors

M2c resolves only targets determined by lexical and module facts. Receiver
member choice, expected-type constructor choice, operators, index operations,
overload selection, literal conversion, callability, and instance applicability
remain M2d work.

```text
DeferredSelector W =
  | receiverField (OccurrenceId W) Identifier
  | receiverMethod (OccurrenceId W) Identifier
  | dotConstructor (OccurrenceId W) Identifier
      (canonical NonemptyList (ConstructorTarget W))
  | classMethod (OccurrenceId W) Identifier
      (canonical NonemptyList (ClassMethodId W))
  | prefixOperator (OccurrenceId W) PrefixOperator
  | infixOperator (OccurrenceId W) InfixOperator
  | assignmentOperator (OccurrenceId W) AssignmentOperator
  | index (OccurrenceId W)
```

A leading-dot constructor candidate list contains exactly the currently visible
user and intrinsic constructors with that leaf. An unqualified class-method fallback is considered
only when ordinary term lookup is empty and contains exactly all visible class
members with that spelling. Candidate lists are sorted, duplicate-free, and
nonempty. M2c never chooses their first element.

`receiverMethod` is used only when the selected field occurrence is the final
component of an exact call callee; every other receiver select is
`receiverField`. The operator occurrences select their exact located operator
leaves. The `index` occurrence selects the whole located
`ExpressionPayload.index` expression, because brackets are token evidence and
are not AST leaves. These cases exhaust the four ADR-0016 operator/index roles
and the receiver/select/dot fallback sites; there is no vague `Operator` or
untyped selector escape case.

### Source instance environment

For module `M`, the M2c source-only environment is exactly:

```text
sourceInstanceEnvironment W M =
  canonicalSet (
    localSourceInstances W M union
    union { localSourceInstances W T |
            SourceEdge W contains an edge with
            kind = import, source = M, and target = T })
```

Repeated edges are idempotent. Export edges and import edges of imported modules
do not add instances. This is intentionally non-transitive: for `A -> B -> C`,
`A` sees `A` and `B` local instances but not `C` local instances unless `A`
also imports `C` directly. The policy is independent of import selector mode.

The pinned Rust implementation recursively collects imported instances, while
the pinned Haskell behavior is closer to direct import visibility. This ADR
chooses the explicit equation above rather than either implementation's
incidental traversal.

Every element is an `InstanceId W` selected from source syntax. M2c adds no
intrinsic instance fact and does not test instance applicability. M2d separately
defines its intrinsic instances, combines them with this source-only value, and
performs applicability and overlap selection. Consequently an M2c result cannot
accidentally freeze M2d's intrinsic-instance policy.

### Closed successful-result algebra

Successful phase values are closed proof-carrying records. The catalog and
validated-interface snapshots are exactly:

```text
ValidatedCatalog W = {
  entities       : canonical List (EntityId W),
  publicEntities : canonical List (PublicEntityId W),
  ownedData      : canonical List (OwnedDataId W),
  constructors   : canonical List (ConstructorId W),
  classMethods   : canonical List (ClassMethodId W),
  instances      : canonical List (InstanceId W),
  exact          : each list is exactly its closed catalog-kind projection
                   from W.index,
  valid          : no CatalogDiagnostic W applies
}

ValidatedInterfaces W (state : StaticRuleState W) = {
  atoms : canonical List (InterfaceAtom W),
  least : LeastInterfacesOf W state atoms,
  valid : no InterfaceDiagnostic W applies to state and atoms
}
```

Import provenance remains present after validation:

```text
ImportedEntityBinding W = {
  owner      : ReachableModule W,
  localName  : StaticName W,
  namespace  : EntityNamespace,
  sourceAtom : EntityAtom W,
  routes     : canonical NonemptyList (ImportRouteId W),
  exact      : every route has the displayed owner, localName, sourceAtom,
               and sourceAtom.namespace = namespace,
  unique     : every final route for this owner/name/namespace is in routes
}

ModuleImportKey W = {
  key   : ModuleBindingKey W,
  exact : key selects an ImportMode.module declaration
}

ImportedModuleCandidate W = {
  site   : ModuleImportKey W,
  target : ReachableModule W,
  exact  : site's resolved target = target.id
}

ImportedModuleBinding W = {
  owner      : ReachableModule W,
  localName  : StaticName W,
  candidates : canonical NonemptyList (ImportedModuleCandidate W),
  exact      : candidates are exactly all module imports in owner with that
               explicit alias or validated default leaf
}

ImportEnvironment W = {
  entities : canonical List (ImportedEntityBinding W),
  modules  : canonical List (ImportedModuleBinding W),
  exact    : entities are exactly the enabled, non-suppressed item routes and
             modules are exactly the grouped module-import candidates,
  valid    : each entity owner/name/namespace has one sourceAtom and every
             route supporting it is retained
}
```

Distinct module targets remain together in one `ImportedModuleBinding`; a use
of that binding can therefore produce the specified lookup ambiguity. By
contrast, successful interface validation proves that an imported entity
binding has one structural source atom in its namespace, while retaining all
equal supporting routes.

The module and owner environments are closed sums over resolved origins:

```text
ModuleEntityBinding W =
  | local {
      owner : ReachableModule W,
      name  : StaticName W,
      value : ResolvedEntity W,
      exact : value.origin is locally declared under name in owner.id
    }
  | imported (ImportedEntityBinding W)

ModuleEnvironmentEntry W = {
  owner   : ReachableModule W,
  terms   : canonical List (ModuleEntityBinding W),
  types   : canonical List (ModuleEntityBinding W),
  classes : canonical List (ModuleEntityBinding W),
  modules : canonical List (ImportedModuleBinding W),
  exact   : the lists are exactly the local catalog plus ImportEnvironment
            entries of the corresponding derived namespace for owner
}

ModuleEnvironment W = {
  entries : canonical List (ModuleEnvironmentEntry W),
  total   : every ReachableModule W occurs exactly once
}

VisibleEntityBinding W =
  | lexical (ModuleEntityBinding W)
  | public (EntityAtom W)

DataOwnerEntry W = {
  binding      : VisibleEntityBinding W,
  data         : OwnedDataId W,
  constructors : canonical List (ConstructorId W),
  exact        : binding resolves to data and constructors are exactly the
                 constructor subset visible through that binding
}

ClassOwnerEntry W = {
  binding : VisibleEntityBinding W,
  methods : canonical List (ClassMethodId W),
  exact   : binding resolves to a class and methods are exactly its declared
            methods
}

ContractOwnerEntry W = {
  binding : VisibleEntityBinding W,
  types   : canonical List (ResolvedEntity W),
  terms   : canonical List (ResolvedMember W),
  exact   : binding resolves to a contract and the two lists are exactly its
            named nested type and term/member tables
}

OwnerEnvironment W = {
  data      : canonical List (DataOwnerEntry W),
  classes   : canonical List (ClassOwnerEntry W),
  contracts : canonical List (ContractOwnerEntry W),
  exact     : every and only visible owner binding of each kind occurs once
}
```

The closed intrinsic map is a fallback function and is not copied into any of
these source environments.

Lookup, pragma, and deferred outputs retain their exact AST keys:

```text
ResolvedLookupOutcome W C (use : LookupUse W) (path : LookupPath W use) =
  | terminal (TerminalTarget W C)
  | receiverBase {
      base       : ResolvedTarget W C,
      remaining  : canonical NonemptyList (OccurrenceId W),
      exact      : remaining is the unconsumed suffix of path.components,
      selectors  : canonical NonemptyList (DeferredSelector W)
    }
  | deferred (canonical NonemptyList (DeferredSelector W))

ResolvedLookup W C = {
  use     : LookupUse W,
  path    : LookupPath W use,
  outcome : ResolvedLookupOutcome W C use path,
  accepts : the closed qualifier/receiver automaton accepts exactly outcome
}

ResolvedLookupEnvironment W C = {
  entries : canonical List (ResolvedLookup W C),
  exact   : every AST-derived LookupPath accepted by the lexical phase occurs
            exactly once and no other entry occurs
}

ResolvedPragmaEnvironment W C = {
  entries : canonical List (ResolvedPragmaTarget W C),
  exact   : every class-kind and noGenericInstanceFor pragma target occurs
            exactly once with the kind-dependent result defined above
}

DeferredSelectorEnvironment W C = {
  entries : canonical List (DeferredSelector W),
  exact   : entries are exactly the union of deferred lookup outcomes and all
            receiver, leading-dot, operator, and index sites selected from
            W.index, with exact equal selectors idempotent
}

SourceInstanceEntry W = {
  owner     : ReachableModule W,
  instances : canonical List (InstanceId W),
  exact     : instances = sourceInstanceEnvironment W owner.id
}

SourceInstanceEnvironment W = {
  entries : canonical List (SourceInstanceEntry W),
  total   : every ReachableModule W occurs exactly once
}

ResolutionMeasures W = {
  N E A R O resolutionUnits : Nat,
  exact : the six values satisfy the equations in the next section
}
```

All displayed lists use their structural total order. `ModuleEnvironment`,
`OwnerEnvironment`, `ImportEnvironment`, `SourceInstanceEnvironment`, resolved
lookups, pragmas, and deferred selectors therefore have one canonical value;
none exposes a caller-supplied map or last-write-wins insertion order.

The successful result type is exactly:

```text
ResolvedWorkspace = {
  input          : ClosedWorkspace,
  reachable      : ParsedReachableWorkspace,
  graphExact     : ReachableGraphOf input reachable,
  sourceEdges    : canonical List (SourceEdge reachable),
  edgesExact     : sourceEdges are exactly the occurrence-preserving lifted
                   edges of reachable.localEdges,
  catalog        : ValidatedCatalog reachable,
  staticState    : StaticRuleState reachable,
  staticExact    : StaticRuleClosureOf reachable staticState,
  interfaces     : ValidatedInterfaces reachable staticState,
  imports        : ImportEnvironment reachable,
  modules        : ModuleEnvironment reachable,
  owners         : OwnerEnvironment reachable,
  classification : PatternClassification reachable,
  sourceInstances : SourceInstanceEnvironment reachable,
  lookups        : ResolvedLookupEnvironment reachable classification,
  pragmas        : ResolvedPragmaEnvironment reachable classification,
  deferred       : DeferredSelectorEnvironment reachable classification,
  measures       : ResolutionMeasures reachable,
  lexicalExact   : LexicallyResolves reachable classification modules owners
                     lookups pragmas deferred,
  covers         : every resolver-owned AST lookup, pragma, instance, and
                   deferred-selector site occurs in its exact output,
  nonDangling    : every structural origin is selected from reachable.index,
                   every module is a ReachableModule reachable, every support
                   site occurs in sourceEdges or a structural key enumeration,
                   and every intrinsic is a constructor of IntrinsicId
}
```

`ResolvedWorkspace` has no alternative constructor for a partial graph,
unchecked catalog, invalid interface, missing lookup output, externally chosen
intrinsic environment, or resource measure. Failures use the closed
`ResolutionFailure` sum and never construct this record.

### Exact executable resource metric

The metric is constructed in phase 4, only after diagnostic-free graph and
catalog phases and successful construction of the least static rule state.
Define:

```text
N = Structural.indexNodeMeasure W.index
E = (sourceEdges W).length
A = (candidateRuleState W).candidates.length
R = (candidateRuleState W).rules.length
O = length of Structural.allOccurrences W.index filtered to these exact roles:
    pragmaTarget, boundedClassComponent, predicateClassComponent,
    instanceClassComponent, typeNameComponent,
    expressionName, selectField, dotConstructorName,
    patternNameComponent, patternDotConstructorName,
    prefixOperator, infixOperator, assignmentOperator, indexExpression

resolutionUnits = N + E + A + (A + 1) * R + O
```

`N` charges the structural presence of every closed AST node once, including
module references, selectors, lexical occurrences, and retained assembly
slices, but not spans, trivia, identifier bytes, or source bytes. `E` separately
charges graph-edge demand, `R` charges compiled propagation demand, and `O`
charges lexical/deferred lookup demand. These are intentionally distinct charges
for one source node when it participates in more than one semantic phase.
`A + 1` charges every rule for all possible strict-growth rounds plus the final
fixed-point check. Arithmetic is unbounded `Nat` arithmetic.

This is a deterministic semantic-demand measure, not a claim about Lean
reductions, comparisons, allocations, sorting, or machine instructions. The
executor proves it invariant under ADR-0014 workspace equivalence and the
canonical ordering theorems from ADR-0016. Standard, parse, graph, or catalog
failure occurs before this value exists. Interface or lexical failure occurs
after it exists internally but never fabricates a `ResolvedWorkspace` merely to
expose it.

### Judgments, executors, and proof obligations

The specification provides independent relations at least for:

```text
Sha256.Digests
StandardBundleError.Applies
StandardBundle.Verifies
ClosedWorkspace.Assembles
ModuleReference.ResolvesTo
ReachableGraphOf
InterfaceRulesOf
StaticRuleClosureOf
LeastInterfacesOf
ImportEnvironmentOf
ModuleEnvironmentOf
OwnerEnvironmentOf
SourceInstanceEnvironmentOf
PatternClassificationOf
LexicallyResolves
ResolvedLookupEnvironmentOf
ResolvedPragmaEnvironmentOf
DeferredSelectorEnvironmentOf
Phase2Diagnostic.Applies
CatalogDiagnostic.Applies
InterfaceDiagnostic.Applies
LexicalDiagnostic.Applies
Resolves
Rejects
UserResolutionResultOf
```

Judgment modules do not import sibling executors. Executors do not import the
final judgments. Property modules alone connect them.

The pure boundaries are:

```text
verifyStandardBundle :
  RawStandardBundle ->
  Except (canonical NonemptyList StandardBundleError) VerifiedStandardBundle

assembleClosedWorkspace :
  ValidatedUserWorkspace -> VerifiedStandardBundle -> ClosedWorkspace

resolveWorkspace :
  ClosedWorkspace ->
  Except ResolutionFailure ResolvedWorkspace

ResolveUserWorkspaceFailure =
  | configuration (canonical NonemptyList StandardBundleError)
  | source ResolutionFailure

resolveUserWorkspace :
  ValidatedUserWorkspace -> RawStandardBundle ->
  Except ResolveUserWorkspaceFailure ResolvedWorkspace

resolveUserWorkspace user raw =
  match verifyStandardBundle raw with
  | Except.error errors => Except.error (.configuration errors)
  | Except.ok standard =>
      resolveWorkspace (assembleClosedWorkspace user standard)
        |>.mapError .source
```

`resolveUserWorkspace` is the exact outer M2c API. A caller cannot pass a
`VerifiedStandardBundle`, a preassembled `ClosedWorkspace`, an intrinsic
environment, a parsed module, a catalog, or an interface. The three preceding
functions remain separately testable pure kernels, but the outer executor calls
them only by the displayed equations. A standard error is preserved as the
complete canonical configuration-error list; a source failure is preserved
without changing its dependent phase package.

The intrinsic environment is the unique closed constant and is not an input.
The successful value is the exact `ResolvedWorkspace` record above; this API
does not erase any of its dependent indices or evidence fields.

The implementation proves at least:

```text
Sha256.digest_sound
Sha256.digest_complete
Sha256.Digests.functional
Sha256.replay_sound
Sha256.lowerHex_exact

verifyStandardBundle_sound
verifyStandardBundle_complete
standardBundleErrors_sound
standardBundleErrors_complete
StandardBundle.Verifies.functional
assembleClosedWorkspace_sound
ClosedWorkspace.Assembles.functional
assembleClosedWorkspace_exact_files

resolveModuleReference_sound
resolveModuleReference_complete
reachableGraph_sound
reachableGraph_complete
ReachableGraphOf.functional
sourceEdges_preserve_occurrences
sourceEdges_canonical_order
surfaceDiagnostics_preserved_one_for_one

staticRuleClosure_sound
staticRuleClosure_complete
StaticRuleClosureOf.functional
candidateRuleState_exact
interfaceRules_sound
interfaceRules_complete
interfaceRuleId_injective
replayStaticRuleClosure_sound
replayStaticRuleClosure_complete
interface_step_monotone
interface_step_inflationary
interface_invariant_preserved
interface_iteration_bound
leastInterfaces_sound
leastInterfaces_complete
LeastInterfacesOf.functional
replayInterfaceSaturation_sound
replayInterfaceSaturation_complete

patternClassification_total
patternClassification_sound
lexical_resolution_sound
lexical_resolution_complete
lexical_targets_nonDangling
deferred_candidates_wellFormed
scope_no_branch_leakage
scope_initializer_precedes_binder
scope_sequential_let_shadowing
dotted_root_priority_total
sameNameConstructor_sound
sourceInstanceEnvironment_exact
importEnvironment_canonical
moduleEnvironment_total
ownerEnvironment_exact
resolvedLookups_exact
resolvedPragmas_exact
deferredSelectors_exact
resolvedWorkspace_covers
resolvedWorkspace_nonDangling

resolveWorkspace_sound
resolveWorkspace_complete
resolveUserWorkspace_equations
resolveUserWorkspace_sound
resolveUserWorkspace_complete
UserResolutionResultOf.functional
Resolves.functional
Rejects.functional
Resolves.not_rejected
resolves_or_rejects
diagnostics_complete_for_first_failing_phase
resolutionUnits_deterministic
resolutionUnits_equivalent_workspace
```

Completeness covers cycles and every displayed diagnostic constructor. Public
theorems may depend only on the standard Lean foundations already audited by
this repository; the public-theorem audit permits only `propext`,
`Classical.choice`, and `Quot.sound` and must report no additional assumption.

The concrete parser theorem from ADR-0015, an exact byte bridge, and a resolver
theorem are mandatory, not optional integration tests:

```text
Multi.canonicalStandard_parses :
  for every file in Multi.canonicalStandardFixtures,
  exists certified, Multi.parseModule file = Except.ok certified

verifiedStandard_matches_parserFixtures :
  map (fun file => (file.id, file.content.toUTF8))
      canonicalVerifiedStandard.workspaceFiles =
  map (fun file => (file.id, file.content.toUTF8))
      Multi.canonicalStandardFixtures

canonicalStandard_verifies :
  verifyStandardBundle canonicalRawStandardBundle =
    Except.ok canonicalVerifiedStandard

canonicalStandard_resolves :
  resolveUserWorkspace canonicalStandardUser canonicalRawStandardBundle =
    Except.ok canonicalStandardResolved
```

`canonicalRawStandardBundle` contains the six exact `canonicalRawFiles` byte pairs
in deliberately noncanonical input order, exercising canonical assembly.
`canonicalStandardUser` is a validated caller workspace containing one empty
`main.solc` entry and no external libraries. The result must contain all six
standard roots. The byte bridge is proved from exact equality, not digest
collision resistance, and is required before ADR-0017 reuses any ADR-0015 parse
certificate. These theorems use the actual canonical byte constants and the
production verifier, assembler, parser, and resolver, not an abstract premise,
preverified input, or hand-built AST.

### Canonical resolver feasibility gate

Before this ADR can become Accepted, ordinary CI must run the production
shared-byte bridge and resolver over the actual six standard sources. The gate
must:

1. prove `canonicalStandard_verifies`,
   `verifiedStandard_matches_parserFixtures`, and
   `Multi.canonicalStandard_parses` from the shared
   `Solcore.Standard.CanonicalData` bytes;
2. construct the actual `ParsedReachableWorkspace`, catalogs, and least
   `candidateRuleState`, not a reduced fixture;
3. replay a `StaticRuleClosureCertificate` and record the resulting decimal
   `E`, `A`, and `R` values in this ADR and in a checked golden artifact;
4. replay an `InterfaceSaturationCertificate`, record its number of strict
   growth rounds and final atom count, and confirm the final equality check;
5. prove both replayer results equal the direct production executors; and
6. prove `canonicalStandard_resolves` through the outer
   `resolveUserWorkspace` equation.

The gate may use an untrusted generator only to produce certificate data. Lean
must check the data with the pure replayers and kernel theorems under the
repository's ordinary CI settings, without `native_decide`, new axioms,
increased heartbeat or recursion limits, a hand-built AST/interface, or a
second source-byte literal. The production executor must use the worklist
equations above and may not enumerate `StaticAtomCarrier`, enumerate
`StaticRuleCarrier`, or compute either carrier's cardinality. If the exact
production run, certificate sizes, or
proof replay are impractical, the representation must be revised here. Until
the concrete decimal `E`, `A`, `R`, strict-round, and final-atom values have been
recorded and independently reproduced, this gate is open and the ADR remains
Proposed.

An independent source review currently estimates `E = 11`, `A` and `R` near
256 from approximately 229 entity-export contributions plus 27 constructor
contributions, and about two strict interface-growth rounds. Those figures are
planning evidence only: they are neither normative values nor a substitute for
the measured, replayed decimals required by this gate.

### Module DAG and implementation order

ADR-0015 owns the neutral `Solcore/Standard/CanonicalData.lean` module and its
`Solcore/Standard` kernel-policy root; ADR-0016 owns its structural DAG.
ADR-0017 consumes both and adds only:

```text
Solcore/Foundation/Sha256/{Syntax,Judgment,Execution,Certificate,Properties}.lean
Solcore/Foundation/Sha256.lean

Solcore/Resolution/Intrinsic.lean
Solcore/Resolution/Standard/{Syntax,Judgment,Execution,Certificate,Properties}.lean
Solcore/Resolution/ClosedWorkspace/{Syntax,Judgment,Execution,Properties}.lean
Solcore/Resolution/Graph/{Syntax,Diagnostic,Judgment,Execution,Properties}.lean
Solcore/Resolution/Catalog/{Syntax,Diagnostic,Judgment,Execution,Properties}.lean
Solcore/Resolution/Interface/{Syntax,Diagnostic,Judgment,Execution,Certificate,Properties}.lean
Solcore/Resolution/Scope/{Syntax,Diagnostic,Judgment,Execution,Properties}.lean

Solcore/Resolution/Syntax.lean
Solcore/Resolution/Judgment.lean
Solcore/Resolution/Execution.lean
Solcore/Resolution/Properties.lean
Solcore/Resolution.lean
```

`Solcore.Standard.CanonicalData` is neutral: it imports neither parser nor
resolver and contains the sole six source-byte literals and their raw metadata.
ADR-0015 parser fixtures and ADR-0017 standard verification both import that
module. The phase dependency order is exactly `Standard -> ClosedWorkspace ->
Graph -> Catalog -> Interface -> Scope -> Resolution`; `Intrinsic` is imported
by `Scope`, and SHA-256 and `CanonicalData` are imported by `Standard`. There is
no reverse phase import.

Within a phase directory, `Diagnostic` when present imports only that phase's
`Syntax`; `Judgment` and `Execution` share `Syntax` and `Diagnostic` but do not
import each other. A `Certificate` module imports syntax and executable replay
primitives, never a judgment or property theorem. `Properties` is the first
module allowed to import both judgment and execution/certificate sides. The
standard certificate module contains generated SHA replay data but no trusted
conclusion; the interface certificate module contains the fixed-point
certificate forms and pure replayers above. No resolved AST stores an equation
asserting that it came from an executor.

Implementation order is:

1. consume the neutral shared canonical bytes and pass the isolated SHA-256
   feasibility gate;
2. implement and prove exact standard verification and closed-workspace
   assembly;
3. implement pure module references and reachable graph discovery;
4. implement the Catalog phase, typed catalog keys, and default-binding checks;
5. implement the least static candidate/rule closure, its certificate replay,
   interface saturation, validation, and interface diagnostics;
6. implement module, owner, import, and source-instance environments;
7. implement pattern classification, suffix scopes, typed lookup paths, the
   qualifier automaton, pragmas, same-name constructors, and deferred selectors;
8. connect the independent judgments and prove the shared-byte, verifier,
   parser, and resolver theorems;
9. pass the actual canonical resolver feasibility gate and record its exact
   counts; and
10. add the public `Solcore.Resolution` umbrella only after every proof and
    audit passes.

The semantic-kernel scan in `scripts/check-kernel.mjs` must contain the exact
combined roots below. The first pair is introduced by ADR-0015 and must remain;
the other pairs are added by ADR-0017:

```text
Solcore/Standard
Solcore/Standard.lean
Solcore/Foundation/Sha256
Solcore/Foundation/Sha256.lean
Solcore/Resolution
Solcore/Resolution.lean
```

ADR-0015 separately keeps `Solcore/Standard`, its umbrella, and the Multi
Surface root in the same audit; ADR-0016 adds its structural identity root. Full
build, tests, metadata, semantic-kernel, English-text, formatting,
forbidden-trust, and public-theorem assumption audits gate every slice.

### Compatibility divergence ledger

| Topic | Pinned Haskell evidence | Pinned Rust evidence | M2c decision |
| --- | --- | --- | --- |
| module lookup | host roots and first-existing candidate | filesystem snapshot and loaded-file map | exact closed-workspace membership |
| `std.a` | configured standard root | existence-dependent fallback paths | always standard; no fallback |
| `lib.a` | current library root | editor multi-root can alter meaning | exact current logical library root |
| bare `std` payload | standard root reference | standard path special case | empty standard tail; distinct from `std.std` syntax |
| keyword default leaf | parser/name conversion varies by path | path and identifier layers differ | explicit alias required when leaf is not an `Identifier` |
| duplicate references | maps and list order can collapse sites | tracked maps can coalesce targets | occurrence-keyed edges and selector keys |
| wildcard constructor visibility | normalization merges optional lists | visible/opaque sets are merged | local wildcard opaque; remote wildcard copies exact visible subset |
| constructor selectors on non-data | later resolver/type errors | phase-dependent diagnostics | typed `nonDataConstructorSelector` |
| same-name constructor | explicit `isSameNameConstructor` fallback | explicit same-name lookup | exact visible `T.T` shorthand after term lookup |
| generic bare constructor | generally rejected outside special paths | rejected or deferred by context | rejected in expressions, calls, and child-bearing patterns; a childless pattern remains a binder |
| repeated sequential lets | environment replacement can occur | body scopes retain shadow chains | each let creates a suffix scope and may shadow earlier lets |
| dotted root collision | resolver heuristics vary by occurrence | namespace heuristic inspects several maps | ordinary term lookup first, qualifier lookup only when empty |
| recursive interfaces | heuristic SCC round cap | incremental query convergence | finite positive least fixed point bounded by `A` |
| duplicate imports/exports | map/list order may choose one | ordered maps may retain one | equal atoms idempotent; distinct origins ambiguous with sites |
| instance imports | closer to direct imported module facts | recursive graph collection | local plus direct-import target locals only |
| branch bindings | audited paths can leak or overwrite | audited paths vary by body kind | independent child and suffix scopes |
| intrinsic identity | string-keyed environment | string lookup into enums | exact closed `IntrinsicId` |
| resolved identity | names and reconstructed qualifiers | interned compiler identities | ADR-0016 structural identities |

Parser-only divergences, including optional `else`, optional `return`, contract
fallback forms, contract-local aliases, postfix calls, Unicode, and separator
rules, belong to the ADR-0015 ledger. They are not silently reopened here.

## Consequences

- Module discovery is pure and every source reference retains its occurrence.
- Unreachable malformed caller files remain unobserved, while all six standard
  files are mandatory roots.
- Recursive interfaces have one finite least-fixed-point meaning.
- Constructor visibility cannot be escalated through import/export paths.
- Same-name constructor syntax required by the canonical bundle is supported
  without permitting arbitrary unqualified constructors.
- Sequential lexical shadowing is represented without branch leakage or
  same-frame map overwrite.
- Cross-import and public ambiguities retain canonical contributing source
  sites.
- Standard source identity is exact byte equality; Git provenance remains CI
  evidence rather than a kernel claim.
- M2c stops before type-directed selection, callability, overloads, instance
  applicability, literal conversion, and Semantic Core elaboration.

The cost is a fixed-point candidate/rule compiler and certificate-backed hash
and saturation boundaries. Those costs are explicit in the metric and
acceptance gates; the old cartesian interface universe is not materialized.

## Rejected alternatives

### Keep parser and structural identity inside this ADR

Rejected because a resolver cannot close grammar and address questions while
also treating them as certified prerequisites. ADR-0015 and ADR-0016 are
independently reviewed proof boundaries.

### Resolve compiler HIR directly

Rejected because compiler HIR contains implementation-owned recovery,
allocation, and prior-resolution choices.

### Verify only standard digests

Rejected because digest equality is not exact byte equality without a
cryptographic collision assumption. The verifier checks the raw bytes directly
and separately recomputes the recorded digests.

### Treat a Git revision label as a kernel fact

Rejected because bytes do not prove repository provenance. CI checks the pinned
repository; Lean proves properties of the exact bytes it receives.

### Supply a pre-resolved standard interface

Rejected because it would create a second semantic path. The production parser
and resolver process all six sources.

### Use DFS order, source order, or first-wins maps

Rejected because semantically irrelevant enumeration order would choose a
different program meaning.

### Make every wildcard copy constructors

Rejected because local declaration export and provider-interface re-export have
different visibility boundaries. Their exact rules are intentionally separate.

### Reject every import/export cycle

Rejected because positive cyclic re-exports have a finite least-fixed-point
meaning.

### Use an arbitrary interface round cap

Rejected because a cap can reject a valid long chain. Atom cardinality is a
proved sufficient bound.

### Propagate instances transitively

Rejected for m2c-v1. Transitive visibility makes an unrelated intermediate
import change downstream solving context. The direct-import equation is
explicit and testable.

### Resolve receiver and leading-dot selectors in M2c

Rejected because their target depends on type and expected-type facts owned by
M2d.

## Conformance requirements

The M2c conformance suite must include at least:

- every pure module-reference constructor in main, standard, and external
  libraries, including distinct `std` and `std.std` occurrences with one target;
- bare `lib`, undeclared external libraries, missing declared modules, and
  keyword-shaped default leaves with and without explicit aliases;
- occurrence-distinct repeated source edges, their exact structural-site sort,
  no source/target deduplication, and repeated module wildcards;
- unreachable malformed files remaining unobserved and multiple reachable parse
  failures on one frontier, preserving every parser `SurfaceDiagnostic` element
  one-for-one;
- exact raw-byte bundle success, every duplicate/missing/extra path error,
  all specified error-coexistence combinations, invalid UTF-8, the SHA size
  boundary, and one-byte mutations of every file and the manifest;
- SHA-256 known vectors, block boundaries, largest-file replay, and executor
  correspondence without runtime-only proof shortcuts;
- exact no-third-files assembly equations and caller entry/declaration
  preservation;
- plain, aliased, wildcard, named, aliased-named, and hiding imports;
- integration with ADR-0015 rejection of every duplicate source, resulting
  binding, hiding name, export selector, `ModuleReferenceShape`, and constructor
  selector, proving that none reaches resolver execution;
- local wildcard opacity and remote wildcard constructor preservation;
- non-data constructor selection, missing constructors, hidden constructors,
  and constructor-subset unions through cycles;
- the seven exact interface-rule comprehensions, import-route provenance,
  static-closure replay, and exact `A` and `R` counts;
- cyclic interfaces requiring the full finite bound, leastness, monotonicity,
  functionality, and invariant preservation;
- idempotent equal atoms and ambiguous distinct origins with all canonical
  contributing sites;
- same-name constructors in expressions, calls, and patterns, including
  canonical names and an alias that disables the shorthand;
- rejection of a unique but generic bare constructor in an expression, call,
  and child-bearing pattern, plus classification of the childless spelling as a
  binder;
- sequential repeated lets, initializer-before-binder, body-let shadowing of
  parameters/patterns, class and instance outer binders, contract nested types,
  independent branches/arms, loops, lambdas, and blocks;
- every qualifier-automaton transition, dotted-root collision class, term-first
  priority, and farthest-failure tie-break;
- all four pragma kinds, including multiple same-module local data matches and
  no imported or intrinsic `noGenericInstanceFor` target;
- source-instance import and the `A -> B -> C` non-transitive case, with no M2c
  intrinsic instance facts;
- every intrinsic, exact `invoke`/`invokable.invoke`/`Int.fromInteger`
  distinction, intrinsic shadowing, no bare `fromInteger`, empty tuple and
  function-type mappings, and rejection of unlisted aliases;
- every deferred selector constructor and canonical candidate order;
- exact `N`, `E`, `A`, `R`, `O`, and `resolutionUnits` values;
- equal results under ADR-0014 workspace equivalence;
- the exact outer `resolveUserWorkspace` configuration/source split; and
- the concrete `canonicalStandard_verifies`, byte-bridge,
  `canonicalStandard_parses`, static-closure/saturation replay, and
  `canonicalStandard_resolves` kernel theorems.

## Acceptance gates and deferred work

The resolver choices above are a proposal, not a completeness claim. This ADR
cannot become Accepted until:

1. the now-Accepted ADR-0015 and ADR-0016 prerequisite names and invariants used
   here remain exact; any incompatible prerequisite change reopens this gate;
2. the SHA-256 feasibility gate succeeds under ordinary CI constraints;
3. the canonical resolver feasibility gate records and independently reproduces
   the actual decimal `E`, `A`, `R`, strict-round, and final-atom counts under
   ordinary CI constraints;
4. the exact interface-rule compiler, lookup automaton, and every diagnostic
   `Applies` rule receive an implementation-level independent adversarial
   review; and
5. the phase-local module DAG, certificate replayers, shared-byte bridge, and
   outer API pass the semantic-kernel and public-theorem assumption audits.

M2d separately decides type checking, overload and instance selection, literal
conversion, receiver/member admissibility, callability, and elaboration to
Semantic Core. Publication separately decides new wire versions, profile
limits, Oracle query shape, comparison verdicts, and golden streams.
