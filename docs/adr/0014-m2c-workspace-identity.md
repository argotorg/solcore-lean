# ADR-0014: M2c workspace identity and validation

- Status: Accepted
- Decision date: 2026-08-18
- Scope: M2c workspace identity kernel

## Reader summary / Current implementation

- **Decision:** Give a closed caller workspace canonical logical paths,
  source/module identities, deterministic structural validation, and exact
  finite measures without consulting the host filesystem.
- **Current implementation:** Complete and proof-audited. Independent judgments,
  the pure validator, correspondence and uniqueness theorems, canonical error,
  permutation, and measure tests, and the public Workspace umbrella are present.
- **Boundary:** This kernel does not parse a multi-file workspace, assemble the
  standard library, resolve modules or names, or publish a new wire/profile.
- **Suggested reading:** Read the identity and validation parts of “Decision”,
  then “Conformance requirements”; resolver questions move to ADR-0017.

## Context

ADR-0013 publishes a parser for one source file. Its `path` is an opaque,
nonempty label: Surface v1 and Oracle v4 do not interpret separators, derive a
module, compare a filesystem location, or perform file I/O. That published
meaning cannot be widened in place.

M2c will eventually resolve a closed source workspace. Before module syntax or
name resolution can be specified, the kernel needs a pure identity boundary
that answers four smaller questions:

1. Which raw source labels are canonical workspace paths?
2. When do two source records identify the same logical source and module?
3. Which structural workspace errors exist, and in what deterministic form are
   they returned?
4. Which exact validated value is supplied to later parsing and resolution?

The primary implementation evidence is pinned by `metadata/baselines.json`:

- Haskell commit `1d490d8bb5f374356f06e0720655496482eb1fb4`; and
- Rust commit `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`.

Both implementations distinguish logical library/module identity from an
absolute path, but both also consult host roots. Their lexical normalization
does not establish canonical symlink identity or safe containment. Rust has an
existence-dependent `std` fallback and multi-root editor behavior. Haskell can
derive different logical identities for two paths to one physical file. These
are implementation and driver behaviors, not language semantics.

The first ADR-0014 draft also attempted to fix imports, exports, cyclic public
interfaces, local scopes, instances, constructor visibility, and intrinsic
names. Independent review found that those rules require a closed multi-module
Surface algebra that does not exist yet. In particular:

- Surface v1 has one function and no import or export items;
- a public interface must distinguish entities, module aliases, constructor
  visibility, and instances;
- the canonical standard-library source depends on an explicit intrinsic
  environment before it can be resolved; and
- member selection and constructor shorthand include type-directed
  occurrences that must remain unresolved until checking.

This decision therefore closes only workspace identity and validation. A
separate Accepted resolver ADR is required before any import, export,
declaration, local-name, standard-interface, or occurrence resolver is added.

## Decision

### Additive internal boundary

ADR-0014 introduces an internal Workspace Identity Kernel. It does not change
Surface v1, parse-result v1, Oracle v1 through v4, any language version, any
profile, any schema, any feature status, or any existing capability or golden
bytes. In particular, the Oracle v4 source label remains opaque and the frozen
Oracle v1 `Workspace` is not reused.

No workspace feature becomes published merely because the internal validator
exists. The proposed `modules.import-export` feature remains blocked until the
later resolver and publication gates are complete.

### Canonical path atoms

Workspace paths are logical values, not host paths. The kernel defines an ASCII
path segment with this exact grammar:

```text
ascii-letter = "A".."Z" | "a".."z"
ascii-digit  = "0".."9"
segment      = ascii-letter (ascii-letter | ascii-digit | "_")*
```

`PathSegment` is a refined value containing one accepted segment.
`ModulePath` is a nonempty list of `PathSegment`s. `CanonicalSourcePath` wraps
one `ModulePath`; its rendering joins the segments with `/` and appends exactly
one lowercase `.solc` suffix.

Consequently, accepted source-path text has this grammar:

```text
source-path = segment ("/" segment)* ".solc"
```

Comparison is byte-for-byte and case-sensitive. The parser performs no Unicode
normalization or case folding. An empty or absolute path, empty component, `.`
or `..` component, backslash, colon, NUL, query or fragment syntax, percent
escape, alternate separator, trailing separator, or wrong extension is
invalid. Invalid text is rejected rather than normalized.

The segment category is deliberately independent of language keywords. A
keyword-shaped segment is a valid logical path component. A later module
grammar must either accept that contextual path component or explicitly narrow
the source syntax while retaining this identity layer. This differs
intentionally from the pinned Haskell lexer, which admits Unicode letters but
excludes reserved identifiers in module paths. ASCII-only identity avoids
host- and Unicode-version-dependent spelling.

`ExternalLibraryName` wraps exactly one `PathSegment`. Empty, dotted, slashed,
Unicode, hyphenated, or otherwise non-segment external names are invalid.

The executable path parser and renderer satisfy:

- parsing a rendered value returns that value;
- a successful parse satisfies an independent `CanonicalPathOf` judgment;
- every `CanonicalPathOf` derivation is accepted by the parser;
- `CanonicalPathOf` is functional; and
- rendering is injective.

Because a source path is represented by its `ModulePath`, suffix removal and
path splitting do not require a second fallible conversion.

### Structured identity

The identity layer defines:

```text
LibraryId = main | standard | external(ExternalLibraryName)
SourceId  = { library : LibraryId, path : CanonicalSourcePath }
ModuleId  = { library : LibraryId, path : ModulePath }
```

`SourceId.toModuleId` retains the library and unwraps the source path. It is
injective. Source content, source-vector position, host location, spelling
alias, hash, timestamp, and compiler allocation identity do not participate.

Equal contents at two different `SourceId`s remain two distinct sources and
modules. There is no same-file, inode, realpath, or symlink coalescing. Main,
standard, and external sources with the same relative path are distinct because
their `LibraryId`s differ.

The workspace and resolved layers will use `SourceId` in source spans. Surface
v1 continues to use its opaque string. A future wire ADR may define a canonical
presentation for `SourceId`; no presentation string is fixed here and no raw
string becomes internal identity.

Declaration, member, body, scope, local, instance, and intrinsic identities are
not defined by this ADR. Their structural role tags depend on the later closed
module Surface algebra. In particular, a plain list of child indices is not an
acceptable substitute because field zero, method zero, and constructor zero
must not collide.

### Exact raw workspace shape

The user-supplied value is exactly:

```text
RawSourceFile = {
  path : String,
  content : String
}

RawExternalLibrary = {
  name : String,
  sources : List RawSourceFile
}

RawWorkspace = {
  entry : String,
  mainSources : List RawSourceFile,
  externalLibraries : List RawExternalLibrary
}
```

The entry is a path inside the main library. An external library declaration is
retained even when its source list is empty, so an empty declared library is
distinguishable from an undeclared library. The raw value cannot contain a
standard-library source.

All `String` contents are retained exactly. The kernel performs no I/O and does
not consult a root, cwd, environment variable, executable path, URL, directory,
or file-existence predicate.

### Validated user workspace

Successful validation returns:

```text
WorkspaceFile = {
  id : SourceId,
  content : String
}

ValidatedUserWorkspace = {
  entry : SourceId,
  declaredExternalLibraries : List ExternalLibraryName,
  files : List WorkspaceFile,
  ...proofs of canonical order, uniqueness, and entry membership...
}
```

The entry has library `main`. Every file has library `main` or `external`; no
file has library `standard`. Declared external-library names are canonical,
strictly sorted, and unique, including names of empty libraries.

Files are flattened into one canonical, strictly sorted list. Main sources
precede external sources. External libraries are ordered by name. Sources
within one library are ordered by `CanonicalSourcePath.render`. Every
`SourceId` is unique, and the entry occurs exactly once. Every external
`WorkspaceFile` names a library present in `declaredExternalLibraries`.

The canonical order is an executor and diagnostic traversal order. It does not
make the raw list order semantic. Reordering main sources, external-library
records, or sources within an external library cannot change validation.

### Closed validation errors

Validation returns every applicable structural error as one canonical sorted,
duplicate-free list. It never leaves a choice between collecting errors and
selecting one. The closed error constructors, in ascending constructor order,
are:

```text
invalidEntryPath(rawEntry : String)
invalidExternalLibraryName(rawName : String)
duplicateExternalLibraryName(rawName : String)
invalidMainSourcePath(rawPath : String)
invalidExternalSourcePath(rawLibraryName : String, rawPath : String)
duplicateMainSourcePath(path : CanonicalSourcePath)
duplicateExternalSourcePath(
  libraryName : ExternalLibraryName,
  path : CanonicalSourcePath)
missingEntry(path : CanonicalSourcePath)
```

`duplicateExternalLibraryName` applies when the same raw library name occurs at
least twice, whether or not the name is otherwise valid. A repeated invalid
name therefore produces both the invalid-name and duplicate-name errors.
`invalidExternalSourcePath` applies to every invalid source path in an external
library record even when that record's library name is also invalid.

`duplicateMainSourcePath` applies when at least two main source records parse to
the same canonical path. `duplicateExternalSourcePath` applies when at least
two source records under the same canonical external name parse to the same
canonical path, including records split across duplicate external-library
declarations. Contents do not affect duplicate identity.

`missingEntry` applies only when the raw entry parses successfully and no main
source has that canonical path. If the entry text is invalid, only the
invalid-entry error applies to entry membership; unrelated library and source
errors are still collected. An empty main source list with a valid entry
therefore produces `missingEntry`.

More precisely, `ValidationError.Applies raw error` has exactly these cases:

- `invalidEntryPath text` iff `text = raw.entry` and canonical path parsing of
  `text` fails;
- `invalidExternalLibraryName name` iff a raw external declaration has exactly
  `name` and external-name parsing of `name` fails;
- `duplicateExternalLibraryName name` iff at least two raw external
  declarations have exactly `name`;
- `invalidMainSourcePath path` iff a raw main source has exactly `path` and
  canonical path parsing of `path` fails;
- `invalidExternalSourcePath name path` iff a raw external declaration has
  exactly `name`, one of its sources has exactly `path`, and canonical path
  parsing of `path` fails, independently of whether `name` is valid;
- `duplicateMainSourcePath path` iff at least two raw main source occurrences
  parse successfully to `path`;
- `duplicateExternalSourcePath name path` iff `name` is the successful parse of
  a raw external name and at least two source occurrences across all raw
  declarations with that exact external name parse successfully to `path`;
  and
- `missingEntry path` iff `raw.entry` parses successfully to `path` and no raw
  main source path parses successfully to `path`.

Occurrence counts retain repeated records. Error-list deduplication does not
change those counts.

Errors are ordered first by the constructor order above and then
lexicographically by their arguments. Raw strings use lexicographic Unicode
scalar-value order over `String.toList`; canonical segments and paths use their
ASCII rendering. Equal errors are emitted once.

The independent propositions are:

```text
ValidationError.Applies(raw, error)
ValidationErrorsFor(raw, errors)
Workspace.Validates(raw, validated)
Workspace.Rejects(raw, errors)
```

`ValidationErrorsFor` means that `errors` is canonical, sorted, duplicate-free,
and contains exactly the errors satisfying `Applies`. `Rejects` means
`ValidationErrorsFor` plus a nonempty list. `Validates` is defined from path
judgments, uniqueness, entry membership, and the exact canonical construction;
it does not call the executor or mention an executor result.

When no validation error applies, the canonical construction parses the raw
entry, every external name, and every source path; maps main sources to
`LibraryId.main`; maps each external source to the parsed external library;
sorts the parsed external declarations by name; flattens and sorts all mapped
files by `SourceId`; and retains every content string exactly. `Validates raw
workspace` holds exactly when `workspace.entry`,
`workspace.declaredExternalLibraries`, and `workspace.files` equal those three
constructed values and their stated invariants hold. It does not permit extra,
missing, or reordered output fields.

The executor has this boundary:

```text
validate :
  RawWorkspace ->
  Except (List ValidationError) ValidatedUserWorkspace
```

It returns `.error errors` exactly when the canonical error list is nonempty.
Otherwise it returns the unique validated workspace.

### Raw workspace equivalence

`RawWorkspace.Equivalent` captures validation-observational equality of raw
records. It requires:

- equal raw entry text;
- equal multiplicity of every complete `RawSourceFile` in `mainSources`;
- equal multiplicity of external-library declarations by raw name; and
- equal multiplicity of every complete source record associated with each raw
  external-library name after flattening all declarations of that name.

This definition retains duplicate-name multiplicity, empty external libraries,
paths, and contents while ignoring the three list orders. It also permits
sources to be redistributed among duplicate declarations with the same raw
external name, because validation deliberately flattens that invalid group.
It is an equivalence relation. Equivalent raw workspaces produce equal
validation results, including the complete structural error list.

### Standard-library assembly is a separate boundary

The raw validator neither accepts nor inserts standard sources. Its output is
`ValidatedUserWorkspace`, not a closed resolver workspace.

A later layer will define `VerifiedStandardBundle`. Construction of that value
must recompute and verify the exact six-file set, raw bytes, per-file digests,
manifest digest, upstream revision, and language-version binding fixed by
ADR-0007. A byte or digest mismatch is server configuration failure, not a
source-workspace error and not a language rejection.

Only after verification may an assembly function combine the user workspace
and standard sources into `ClosedWorkspace`. That value will use global
canonical library order `main`, `standard`, then external libraries by name.
The standard bundle is not caller-overridable.

Byte verification alone does not provide parsed declarations, resolved
interfaces, intrinsic targets, or resolution derivations. The subsequent
resolver ADR must define the closed intrinsic dependency set and require the
canonical standard sources to be parsed and resolved by the same semantic
pipeline. It may not silently replace them with an unproved pre-resolved map.

Neither `VerifiedStandardBundle` nor `ClosedWorkspace` is part of the first
implementation slice.

### Measures and future resource precedence

The Workspace Identity Kernel defines executable measures on raw and validated
user workspaces:

- `sourceFiles` is the number of main and external source records;
- `sourceBytes` is the sum of `content.utf8ByteSize` over those records.

Paths, external names, JSON syntax, and the fixed standard bundle do not
contribute to `sourceBytes`. Empty external-library declarations do not
contribute to `sourceFiles`.

The first internal validator has no operational limit. A future strict wire and
handler must apply stages in this order:

1. bounded strict decoding and JSON-shape validation;
2. workspace structural validation;
3. caller-supplied `sourceFiles` and `sourceBytes` preflight;
4. server-side standard-bundle verification; and
5. reachable parsing and resolution under separately fixed limits.

Thus malformed workspace structure is a protocol error even when its source
contents would exceed a semantic resource limit. Exact limits proceed, and one
unit over is inconclusive. A decoder must enforce its own allocation bounds
before building an unbounded raw value.

### First implementation slice and layering

The first code slice consists of:

```text
Solcore/Workspace/Path.lean
Solcore/Workspace/Syntax.lean
Solcore/Workspace/Error.lean
Solcore/Workspace/Judgment.lean
Solcore/Workspace/Validation.lean
Solcore/Workspace/Properties.lean
Solcore/Workspace.lean
```

The dependency direction is:

```text
Path -> Syntax
Path -> Error
Syntax + Error -> Judgment
Syntax + Error -> Validation
Judgment + Validation -> Properties
```

`Judgment` and `Validation` do not import each other. `Properties` alone links
the independent propositions to the executor. No proof-carrying syntax
structure stores an equation about `validate`.

`Path` does not import Surface wire, Oracle, Profile, or a host-path library.
`Syntax` defines its own raw file record rather than reinterpreting a frozen
wire type. The Workspace root is added to the semantic-kernel policy in the
same commit that introduces it. It is imported by the public `Solcore`
umbrella only after its proof boundary is complete.

The first slice proves at least:

```text
CanonicalPathOf.functional
parseCanonicalPath_sound
parseCanonicalPath_complete
CanonicalSourcePath.parse_render
CanonicalSourcePath.render_injective
SourceId.toModuleId_injective
ExternalLibraryName.parse_sound
ExternalLibraryName.parse_complete

validate_sound
validate_complete
Workspace.Validates.functional
validate_errors_sound
validate_errors_complete
Workspace.Rejects.functional
Workspace.Validates.not_rejected
validates_or_rejects

ValidatedUserWorkspace.lookupSource_unique
ValidatedUserWorkspace.entry_lookup
ValidatedUserWorkspace.external_file_declared
validate_preserves_sourceFiles
validate_preserves_sourceBytes
RawWorkspace.equivalent_refl
RawWorkspace.equivalent_symm
RawWorkspace.equivalent_trans
validate_equivalent
```

The theorem names may follow Lean namespace conventions, but their statements
must retain this boundary. Kernel theorems contain no undeclared trust
assumptions beyond the standard Lean foundations already audited in this
repository.

### Deferred resolver decisions

No resolver executor is authorized by ADR-0014. Before implementation, a
separate Accepted ADR must close all of the following:

- a versioned multi-module Surface AST and the exact accepted declaration,
  import, export, binder, and occurrence forms;
- which occurrences are lexically resolved in M2c and which type-directed
  selectors remain for M2d;
- tagged declaration, member, body, scope, local, instance, and intrinsic
  identities with no structural-role collisions;
- exact relative, library-root, standard, and named-external module-reference
  forms, including the decision for bare `@name`;
- reachability through import and export edges and deterministic behavior when
  reachable parsing fails;
- closed import selection, alias, wildcard, and hiding syntax with one exact
  error phase for every malformed form;
- explicit export constructors and whether any entity export alias is added;
- interface facts for entities, public module bindings, and instances;
- the constructor-visibility lattice and finite join used by reexports;
- the finite least-fixed-point universe and sufficient saturation bound for
  cyclic interfaces;
- module, entity, class, constructor, member, and field qualification rules;
- exact namespace and duplicate policy;
- every lexical frame, binder-numbering rule, and shadowing boundary;
- the complete structured intrinsic set required to resolve the canonical
  standard sources;
- source-error and resource precedence after reachable parsing begins; and
- soundness, completeness, determinism, uniqueness, non-dangling, and scope
  non-leakage theorems for the exact accepted fragment.

The later ADR must record deliberate divergences from the pinned compilers,
including ASCII contextual module components, rejection of malformed selector
forms, one default module qualifier, candidate-set ambiguity instead of
first-wins, corrected lexical scopes, pure standard-library selection, and
structured target identity.

## Consequences

- Workspace identity is deterministic without importing host filesystem
  behavior.
- Invalid spelling has one meaning: rejection, never silent normalization.
- Empty external libraries and duplicate declarations remain observable to
  structural validation.
- Successful validation has one canonical order and is invariant under raw
  record permutation.
- Standard-library identity remains explicit without pretending that a digest
  is a resolution derivation.
- Full resolver implementation remains blocked until its Surface algebra and
  semantic choices are independently accepted.

The split adds one ADR and one implementation phase, but it removes false proof
claims and lets the first kernel establish complete soundness and completeness
over a genuinely closed domain.

## Rejected alternatives

### Use a host canonical path or realpath

Rejected because symlinks, mounts, case rules, permissions, cwd, and platform
behavior would enter the language and make identical fixtures nonportable.

### Reuse Oracle v1 or reinterpret Oracle v4

Rejected because both are frozen contracts and neither carries a proof of
canonical workspace identity.

### Normalize invalid source paths

Rejected because multiple raw spellings would identify one source and could
hide caller ambiguity or traversal mistakes.

### Store only nonempty external libraries

Rejected because an explicitly declared empty library must remain distinct
from an undeclared library.

### Return the first structural error found

Rejected because raw list order would affect the result. The validator returns
the complete canonical error set.

### Add declaration identities before a module Surface algebra exists

Rejected because untagged child indices collide across fields, methods,
constructors, bodies, and scopes.

### Treat a verified standard digest as a resolved interface

Rejected because byte identity alone proves neither parsing nor resolution and
does not supply structured targets for intrinsic dependencies.

## Conformance requirements

The Workspace Identity Kernel test matrix includes:

- one-segment and nested canonical paths;
- uppercase, digits, underscores, and keyword-shaped segments;
- empty, absolute, dot, parent, repeated-separator, trailing-separator,
  backslash, colon, NUL, percent, query, fragment, Unicode, wrong-case suffix,
  missing-suffix, and repeated-suffix paths;
- valid and invalid external-library names;
- empty main sources, missing entry, duplicate main paths, duplicate external
  names, and duplicate external paths within and across repeated declarations;
- simultaneous errors in exact canonical order with duplicates removed;
- explicitly declared empty external libraries;
- equal source text under different source IDs remaining distinct;
- path parse/render inversion and source-to-module injectivity;
- lookup and entry uniqueness;
- raw main, external-library, and nested source permutations producing the
  identical success or identical complete error list; and
- exact `sourceFiles` and UTF-8 `sourceBytes` measures, including multibyte
  contents.

Full build, test, metadata, semantic-kernel, English-text, formatting, and
kernel-axiom audits are required before the slice is committed.
