# Memory arrays and slices

Updated: 2026-11-13.

Row 4 of the roadmap table "Following upstream's semantics: the next units" brings solcore-rs #145
to Lean's source language: memory arrays `T[]`, `new T[](n)`, element reads and writes, `a.length`,
read-only slices, and Solidity's panic codes `0x32`, `0x31` and `0x41`. #145 is the pin itself:
`e2eef194` is its merge. Lane E's generator side already compares the compiled paths with Core
references for this row (the `runtime-memory-arrays` and `runtime-array-abi` profiles, roadmap
"Memory arrays, slices and their panics: probe and definitions"). This note covers the Lean side:
the parser, typing, the source semantics and the lowering to Core.

It records:

- upstream's behaviour at the pin, with file and line, and a probe of the pinned Rust paths;
- what Lean has and lacks in each layer;
- a design, the differences from upstream it keeps, and the steps in order with their sizes;
- the effect on the generators, the gate's corpus runs and the smoke;
- the decisions it needed, with their answers.

Decisions 1, 2, 4, 5 and 6 were made on 2026-11-13, each as recommended, and decision 3 on
2026-11-17, by the user, as recommended ([open decisions](#open-decisions)).

## Upstream at `e2eef194`

Paths are relative to the pinned checkout, and `std.sol` is `std/std.sol`.

### Syntax

- **`T[]`.** A type takes any number of `[]` suffixes, folded left to right, so `T[][]` is an
  array of `T[]` (`crates/parser/src/parse/types.rs:186-224`). A size inside the brackets is
  rejected: "fixed-size arrays `T[k]` are not supported; use `T[]`" (`:196`).
- **`new T[](n)`.** `new` is a contextual keyword (`crates/parser/src/parse/common.rs:112`). It
  allocates only before an array type and a parenthesized length. Anything else backtracks, so a
  function named `new` stays callable (`crates/parser/src/parse/expr_pat.rs:244-269`).
- **Indices and slices.** `a[i]` indexes. With a colon, `a[s:e]`, `a[s:]`, `a[:e]` and `a[:]`
  slice. A conditional bound keeps its own colon (`a[c ? x : y:]`), and `a[]` is rejected
  (`crates/parser/src/parse/expr_pat.rs:316-341`).
- **Members.** `a.length` and method calls take any receiver expression, so `f().length` and
  `xs[i].push(v)` need no temporary (`crates/hir/src/nameres/body_resolver.rs:514-537`,
  `crates/specialize/src/specialize/call_resolver.rs:602-640`).
- **Compound assignment.** `lhs op= rhs` is parsed as `lhs = lhs op rhs`
  (`crates/parser/src/parse/stmt.rs:49-80`), on an element as on a local.

### Typing

**Location by context** (`crates/hir-ty/src/lower.rs:103-113`, `:196-225`, `:245-251`,
`:271-285`):

| Where `T[]` is written | Meaning |
| --- | --- |
| a local, a parameter, a return type, a constructor payload, a struct field | the memory array `memory<DynArray<T>>` |
| a contract field (`:409-412`) | the storage array `array<T>` |
| inside `storage<…>`, `mapping(…)` or `calldata<…>` | `array<T>` |
| inside `memory<…>` | `DynArray<T>` |

The constructor payload and struct field rows come from the probe below.

- **Elements.** Every memory array operation requires `t: Typedef<word>`: `new`
  (`crates/hir-ty/src/infer/expr.rs:344-369`), reads and writes
  (`crates/hir-ty/src/infer/storage.rs:359-370`, `:128-150`) and std's instances (`std.sol:3081`,
  `:3115`). Among the types Lean has, these are `word`, the twelve integer types and memory arrays.
  The probe rejects `bool`, tuples, `()`, enums and closures with SC0207. Generic code must state
  the bound (`where t: Typedef<word>`).
- **`new T[](n)`** has the type `T[]`. The comment at `crates/hir-ty/src/infer/expr.rs:344-345`
  says its length is a `uint256`, but the probe found the checker does not enforce this. A `word`
  length passes the checker, and a `let`-bound literal length is reported ambiguous.
- **Literals** `[e1, …, en]` unify their elements (`crates/hir-ty/src/infer/expr.rs:329-342`).
  Open literal elements take their type from their uses, and otherwise `uint256`. `[]` takes the
  expected type.
- **Reads** (`crates/hir-ty/src/infer/expr.rs:82-124`).
  - A memory array or a slice takes an index of any word-sized type: `word` or one of the twelve.
  - A calldata array takes its own instance.
  - Any other user type is indexed through its own `RValueIdxAccess` instance
    (`crates/hir-ty/src/infer/storage.rs:422-443`).
- **Writes** `a[i] = v` give `v` the element type (`crates/hir-ty/src/infer/storage.rs:128-150`).
  Slices and calldata arrays are read-only: "expected assignable index (array slices are
  read-only)" (`:152-203`).
- **Slices** take `uint256` bounds and a base with a `Length` instance. They have the type
  `arraySlice<B>`, nested for a slice of a slice (`crates/hir-ty/src/infer/storage.rs:205-256`).
- **`a.length`** is `Length.length(a)`, a `uint256`, unless the value has a field named `length`
  (`crates/hir-ty/src/infer/storage.rs:384-420`, `crates/hir-ty/src/infer/expr.rs:160-174`).
  `a.length()` works too.
- **Rejected.**
  - `push` and `pop` on a memory array, with the hint "memory arrays have a fixed length"
    (`crates/hir-ty/src/infer/diagnostics.rs:662-667`).
  - `==` on arrays, since they have no `Eq`.
  - An assignment to `a.length`.

### Specialization

Each form becomes a call of a std function (`crates/specialize/src/specialize/body.rs`):

| Form | Call | Lines |
| --- | --- | --- |
| `a[i]` on a memory array | `ridx(a, i)` | `:702-711`, `:2410-2422` |
| `a[i] = v` | `assignRef(lidx(a, i), v)` | `:389-394`, `:2464-2498` |
| `new T[](n)`, `new T[][](n)` | `newArray(n)`, `newNestedArray(n)` | `:2424-2439`, `:3203-3222` |
| `a[s:e]`, `a[s:]`, `a[:e]`, `a[:]` | `sliceRange(a, s, e)`, `sliceFrom(a, s)`, `sliceTo(a, e)`, `sliceAll(a)` | `:2441-2462` |
| `a.length` | `Length.length(a)` | `:2525-2536` |
| `c[i]` on another user type | `ridx(c, i)` | `:702-711` |

So `lidx(a, i)` checks the element place before the right side is evaluated. The parser has
already rewritten `a[i] += v` to `a[i] = a[i] + v`, so a compound assignment takes the same path
and evaluates `a` and `i` twice, once in `lidx(a, i)` and once in `ridx(a, i)`.

### std's layout and helpers

- **Pointers.** `memory<t>` is `enum memory<t> { memory(word) }` with a `Typedef<memory<t>, word>`
  instance (`std.sol:1229-1244`). So `Typedef.rep(a)` is an array's address, and `Typedef.abs(w)`
  makes an array of any word.
- **Allocation.**
  - The free memory pointer is at `0x40` (`std.sol:1316-1329`).
  - `allocate_memory(size)` panics with `0x41` when the end wraps (`:1331-1340`).
  - `allocate_zeroed_memory(size)` clears the region with `calldatacopy` (`:1342-1353`).
- **Layout.** An array is its length word at its address, then one word per element: element `i`
  is at `p + 32 + 32·i` (`std.sol:1371-1382`).
- **`new T[](n)`** has two `0x41` checks (`newArray(n)` and the helper under it,
  `std.sol:1412-1441`). It panics when `n ≥ ⌊(2^256 − 1)/32⌋ = 2^251 − 1`, then allocates
  `(n + 1)·32` zeroed bytes through `allocate_zeroed_memory(size)`, which panics when the end
  wraps. In `new T[][](n)`, every element points at the empty array at `0x60` (`:1419-1430`).
- **Literals** allocate first, without zeroing, then write the elements one by one
  (`arrayLitNew(n)`, `arrayLitInit(a, i, v)`, `allocateDynamicArray(prx, n)`, `std.sol:1384-1411`).
- **Elements.**
  - `memref<t>` is `enum memref<t> { memref(word) }`. Its constructor is not exported and it has no
    `Typedef<word>`, so a reference cannot be forged, offset or stored (`std.sol:3073-3098`).
  - The memory instance of `LValueIdxAccess<…>` checks `i < length` (`0x32`) and gives
    `memref(p + 32 + 32·i)`. `RValueIdxAccess` loads through it (`:3100-3119`).
  - `lidx(c, i)`, `ridx(c, i)` and `assignRef(r, v)` are at `:3143-3155`. `Assign<r, v>` comes
    from `CanStore` (`:2716-2730`).
  - `Length` of a memory array reads its length word (`:2635-2639`).
- **Slices.**
  - `arraySlice<coll>` is `enum arraySlice<coll> { arraySlice(coll, uint256, uint256) }`,
    exported with its constructor (`std.sol:3163-3165`).
  - Its `Length` is the stored length. A read checks `i < length`, then reads the base's element
    `start + i`, which the base checks again (`:3167-3197`).
  - `sliceRange(base, s, e)` checks `s ≤ e ≤ Length.length(base)` with `0x32`. The other three
    forms fill in the missing bounds (`:3199-3222`).
  - `toArray(s)` copies a slice into `newArray(n)` (`:3224-3232`).
  - No `LValueIdxAccess<…>` instance exists for slices.

### Panics

`panic(code)` reverts with Solidity's `Panic(uint256)`: the selector `0x4e487b71`, then the code as
a word (`std.sol:721-726`).

| Code | Sites |
| --- | --- |
| `0x32` | `out_of_bounds()` (`std.sol:220-223`) from a memory array index (`:3107`), a slice index (`:3186`), a slice bound (`:3203`, `:3206`), a calldata array index (`:2321`) and a storage array index (`:3041`) |
| `0x31` | `pop` of an empty storage array (`:2680`) |
| `0x41` | an allocation that wraps (`:1336`), a literal's or `new`'s length (`:1404`, `:1435`), a storage array offset (`:2648`), `push` at the greatest length (`:2696`) |

### ABI

A memory array of word-sized elements may be a public parameter, decoded into memory, or a
result, encoded from it. Both sign as `T[]` (`crates/hir-ty/src/contract/abi.rs:468-479`,
`std/dispatch.sol:160-166`, `std.sol:1940`, `std.sol:2237`).

### The ten fixtures

The last column lists the functions that Lean's native pipeline could run as top-level functions,
which needs no contract storage and no ABI (see [Lean today](#lean-today)).

| Fixture | Lines | Uses | Functions Lean could run |
| --- | ---: | --- | --- |
| `array-syntax` | 91 | `T[]` parameters, results and locals, literals and nested literals, `.length` of a call's result and of `new`; storage `uint256[]` and `uint256[][]` fields with `push`, `setLength` and `.length`; `mapping(address => uint256[])`; a struct field named `length` | sumAll(xs), pair(a, b), local(a, b), returned(a, b), nested(), callResultLength(n): 6 of 12 |
| `mem-array` | 100 | `new` with zeroed elements, writes and reads, `0x32`, `0x41`, loops, a compound element write, rows of `new T[][]`, aliasing, `memref` through `lidx` and `CanStore`, `Length.length(m)` | all 11, bump(r) and bumpElement(v) with `memref` |
| `array-slice` | 122 | the four slice forms of a call's result, a slice's `.length` and reads, slices of slices, bound panics, `toArray`, aliasing through a view, a conditional bound, slices of a storage array | build() and 11 of the 13 public functions; not storageSlice(i) and storageSliceLength() |
| `calldata-slice` | 34 | slices of `calldata<uint256[]>` parameters through the public ABI | none |
| `memory-array-abi` | 60 | `T[]` public parameters and results, `address[]` with a dirty address, a `uint256[][]` result, `toArray(xs[1:3])` | the bodies of ret(n), sum(xs), echo(xs), grid(n) and slices(xs), adapted to word arguments and results |
| `user-collection-index` | 38 | a program's own `RValueIdxAccess` instance, `Typedef.rep(j)` at a generic index, `out_of_bounds()` | none |
| `memory-allocation-bounds` | 36 | `allocateDynamicArray(prx, n)`, `mload`, `get_free_memory()`, an address as a word, `0x41` | none |
| `allocator-bounds` | 22 | `get_free_memory()`, `set_free_memory(p)`, `allocate_memory(size)`, `0x41` | none |
| `abi-sum-padding` | 100 | `abi_encode(v)` of sums into dirty scratch memory, `mstore`, `mload`; #145 does not change it | none |
| `array-ops` | 58 | a storage `array<uint256>` with `ArrayPush.push`, `Array.pop` (`0x31`), `Length.length` and `Array.setLength` | none |

## Probe of the pinned Rust paths

Lane D probed the pinned driver offline in two parts. Its inputs and outputs are kept with the
lane's records under `.upstream/lane-d-unit3-memory-arrays/probe/`.

- **Compile probe.** 48 sources went through the checked frontend alone.
- **Runtime probe.** One contract of 42 calls was exported to Sonatina O0 and O2 and to Yul, then
  run on Anvil. The Lean Hull runner was not run.

The compile probe accepted 31 sources, among them:

- `word` and `int8` elements.
- `Typedef.rep` and `Typedef.abs` at `uint256[]`.
- `arraySlice(m, 1, 5)`, built and matched by hand, and annotations `arraySlice<uint256[]>` and
  `arraySlice<arraySlice<uint256[]>>`.
- Indices of type `word`, `uint8` and `int8`, and an open literal index.
- `[1, 2]` as `uint256`, or as `word` through a use, and `[]` with or without an expected type.
- `T[]` in a constructor payload and in a struct field, as memory arrays.
- Generic code with `where t: Typedef<word>`, and `memory<uint256[]>` as `uint256[]`.
- A function named `new`, `m.length()`, and `.length` after `new` and after a literal.
- Three sources the checker passes but specialization rejects:
  - `[1, 300]` and `m[0] = 300` at `uint8`, with SC0411;
  - `new uint256[](n)` with `n: word`, with SC0405.

It rejected these 17:

- `bool`, tuple, `()`, enum and closure elements (SC0207).
- A `word` slice bound (SC0201).
- A plain or compound write through a slice (SC0201).
- `lidx` of a slice and a `bool` index (SC0207).
- Mixed literal elements (SC0201).
- `toArray` of an array (SC0201 and SC0299).
- `let n = 3; new uint256[](n)` (SC0299).
- `new uint256(3)` (SC0001, a parse error at `uint256`).
- An assignment to `m.length` (SC0201).
- `==` on arrays (SC0207).
- Generic `t[]` code without the bound (SC0207).

The runtime probe gave these outcomes. "Halt" is an exceptional halt, which Anvil reports as
InvalidOperandOOG.

| Call | O0 | O2 | Yul | What it shows |
| --- | --- | --- | --- | --- |
| `m[5] = boom(1)` on a two-element array, where `boom(1)` overflows | `0x32` | `0x32` | `0x32` | the element place is checked before the right side |
| `m[next(c)] += 5`, where `next(c)` adds 1 to `c[0]` | 205 | 205 | 205 | `next` runs twice |
| `m[next(c)] = 7` | 107 | 107 | 107 | `next` runs once |
| a closure, an argument, a tuple and a constructor payload holding an array, then a write | 5, 2, 3, 11 | the same | the same | arrays are references |
| `let m = [1, 2]; return m[1] + m[0];` | 3 | 3 | 3 | open elements default to `uint256` |
| an index of `word` 1, then of `int8` −1 | 5, `0x32` | the same | the same | any word-sized index; −1 is the greatest word |
| `get_free_memory()` at entry, and the first array's address | 896 | 352 | 128 | the free pointer depends on the backend |
| `[[1], [2]]`: the second row's address minus the outer one's | 160 | 160 | 160 | the outer array is allocated before its elements |
| both rows of `new uint256[][](2)`, summed as addresses | 192 | 192 | 192 | both rows are the empty array at `0x60` |
| `new uint256[](n)` for n = 2^251 − 1, 2^251 − 2, 2^251 − 5 and 2^256 − 1 | `0x41` | `0x41` | `0x41` | |
| n = 2^251 − 6 and 2^251 − 12 | `0x41` | `0x41` | halt | the end wraps only past Yul's free pointer |
| n = 2^251 − 20 | `0x41` | halt | halt | |
| n = 2^32 | out of gas | out of gas | out of gas | |
| `new` over memory dirtied past the free pointer | 0 | 0 | 0 | new elements are zero |
| an element write and a nested row replaced, read back | 7 | 7 | 7 | |
| a write to an element of an empty row | `0x32` | `0x32` | `0x32` | |
| `toArray(a[1:3])`, then a write to the copy | 29 | 29 | 29 | `toArray` copies |
| `arraySlice(m, 1, 5)` over three elements: its length, then a read at 2 | 5, `0x32` | the same | the same | the base checks a hand-built view |

The two forms of the `new` length are recorded in the main checkout's `questions.md` (2026-11-13),
beside its 2026-11-04 observation of `new uint256[](uint256(2))`. No other upstream defect was met.

## Lean today

- **Parser** (`Solcore/Syntax`).
  - Types have no array form (`Solcore/Syntax/Type.lean:13-34`).
  - `a[i]` (`Solcore/Syntax/Term.lean:38-41`) and array literals (`:57`) parse.
  - There is no `new`, which is an ordinary identifier, and no slice.
  - The parser is proved against the grammar of `Solcore/Syntax/Grammar`, so a new form needs
    grammar and proof work too. Row 3's shift syntax took 34 files of `Solcore/Syntax`
    (+736/−504).
- **Typing** (`Solcore/TypeSystem`, `Solcore/Frontend/SourceInference`).
  - `a[i]` is typed only on mappings: the base is unified with `mapping(K => V)`
    (`Solcore/Frontend/SourceInference/Expression.lean:1941-1949`, places `:2036-2046`).
  - Array literals are rejected with `unsupportedExpression` (`:1965`).
  - `e.name` is read only as a constructor (`:1950-1964`), and assembly is rejected (`:2445`).
  - The builtin types are `unit`, `bool`, `word`, `integer` and the twelve (`BuiltinType`,
    `Solcore/TypeSystem/Type.lean:143-150`).
  - There is no std, so there is no `Length`, `CanStore` or `RValueIdxAccess`, and no `struct`.
- **Source semantics** (`Solcore/SourceSemantics`).
  - Values are mathematical and copied (`Dynamic.Value`,
    `Solcore/SourceSemantics/Dynamic/Value.lean:87-103`). A mapping is a value holding its
    entries.
  - The heap holds one cell per local (`Dynamic.Heap`,
    `Solcore/SourceSemantics/Dynamic/Heap.lean:30-39`). No value refers to a heap location, and
    there is no byte memory.
  - The index rules read mappings only (`Solcore/SourceSemantics/Dynamic/Evaluation.lean:749-771`,
    places `:791-816`).
  - Builtin functions are pure: `Dynamic.BuiltinApplies` relates arguments to a result without
    the heap (`Solcore/SourceSemantics/Dynamic/Primitive.lean:1105`).
  - Panics exist as `SemanticFault.panic`.
- **Lowering** (`Solcore/Frontend/SourceCore`). Places compile to Core getter and updater
  functions. A mapping is an `OrderedMapping` value in its local's cell
  (`Solcore/Frontend/SourceCore/DataPlaces.lean:134-171`). There is no memory.
- **Core.**
  - It has no memory primitive and no host function for memory
    (`Solcore/Core/Syntax.lean:129-143`).
  - It has cells, cell references and data types (`:36-46`, `:712-727`).
  - Byte memory is ordinary Core code over a cell holding a `WordMapping`
    (`Solcore/Frontend/RustHull/Memory.lean:1-25`, `memoryType` at `:23`), shared by the Hull
    importer and the generators.
- **Hull importer.** Nothing is missing.
  - The ten fixtures are in the pinned contract inventory: six in `scripts/rust-method-parity.json`
    and four in `scripts/rust-scenario-parity.json`.
  - All 1,699 constructor and call observations of that inventory match on Core
    ([README](../../README.md#running-solcore-rs-output)).
- **Contracts and the ABI in the native pipeline.**
  - Contract declarations are catalogued, but their members are not typed
    (`ProgramContractSignature`, `Solcore/Frontend/ProgramSignatures.lean:603-611`).
  - Persistent storage and external calls are not connected, and the ABI wrapper takes static
    words only ([README](../../README.md#proof-status)).
  - So storage arrays, `calldata<T[]>`, `T[]` in public signatures and std's raw memory functions
    have no native counterpart.
- **Generators** (`Solcore/Synthesis`).
  - `runtime-memory-arrays` and `runtime-array-abi` (`Solcore/Synthesis/Internal/Arrays.lean`)
    print `T[]` sources for the pinned compiler. They compare its paths with Core references that
    hold an array as a length cell and element cells.
  - `allocationLimit` is 2^251 − 1 (`:208`). A drawn length is at most 7 or at least 2^255, so no
    case falls in the window near 2^251 that the probe found.

**Core itself needs nothing, for row 4 too.** Core already has the cells, cell references, data
types and byte memory code that both lowerings in [Design](#design) use. The Hull path runs all ten
fixtures on Core today. No Core primitive, host function or typing rule is needed. The Hull
importer needs nothing either.

## Design

The design follows the [decisions](#open-decisions), each as decided.

Memory arrays become builtins, as the twelve integer types did in row 1. They take upstream's typing
and std's checks. The source semantics holds arrays as objects in its heap, and an array value is a
reference to one. The lowering gives each array a Core cell. Lean ports what its native pipeline can
express: memory arrays inside functions. Storage arrays, calldata arrays, the ABI and raw memory
wait for the native pipeline's contracts and ABI.

### Syntax

- `TypeExprValue` gains the array form: `T[]` suffixes on any type, folded left to right. A size is
  rejected with upstream's message.
- `ExprValue` gains `new T[](n)` and the four slice forms. `new` allocates only before an array
  type and a parenthesized length. Otherwise it stays an identifier, as upstream's contextual
  keyword does, except that after `new T[](` the length and the `)` are required (difference 12).
  `a[]` is rejected.
- `e.length` and `e.length()` parse already, as a field and a call of a field.
- The grammar and the parser's correctness proofs take the new forms. Inference and type
  resolution reject them until the step that gives them a meaning. Inference rejects the new
  expression forms in its last arm, a catch-all, because the proofs by functional induction on
  `inferExprFuel` name its cases by number, and an arm of their own would shift every later
  case. The step that gives a form its meaning gives it its own arm and renumbers those cases:
  at 1b-ii, up to 285 case names in 14 files.

### Typing

- **Types.** `BuiltinType` gains the memory array and the slice, applied to their argument, and
  `memref` in step 7. They are spelled `T[]`, `arraySlice<B>` and `memref<T>`.
- **Element types.** `T[]` is well formed when `T` is `word`, one of the twelve types or a memory
  array: the types with `Typedef<word>` upstream that Lean has.
- **`new T[](n)`** has the type `T[]`. Its length has the type `uint256`, and an open literal length
  defaults to it.
- **Literals.** The elements take one type `T`, and the literal has the type `T[]`. `[]` needs an
  expected type. Open literal elements wait as row 1's literals do, then default to `uint256`. As
  built in step 4b, inference infers the elements with no expected type, as a tuple's, and unifies
  their types with one fresh element type, as upstream's `infer_array_expr` does, so `[]` takes its
  element type from the expected type or from the elements beside it, as in `[[a], []]`.
  Finalization defaults an open literal element to `uint256` (`operatorMentions`) and rejects an
  element type a memory array cannot hold with `operatorNotSupported "Typedef"`
  (`validateArrayLiteral`), as upstream's `bool: Typedef<word>` fails. An unannotated `let`
  generalizes a literal's element type that is still open there, as it generalizes any open type, so
  in `let m = [];` no use fixes it, and finalization rejects that open type with
  `operatorNotSupported "Typedef"`, whether the local is used or not (difference 8).
- **Reads.** `a[i]` on an array or a slice takes `i` at `word` or one of the twelve types. An open
  literal index defaults to `uint256`, and the read has the element type. On a mapping, or on a base
  whose type is still open, `a[i]` keeps today's mapping rule. As built in step 3b, inference
  records `a[i]` on a base whose resolved type is a memory array as the read, at the element type,
  and infers the index on its own. Finalization defaults an open literal index to `uint256` and
  rejects another index type with `operatorNotSupported "Typedef"` (`validateArrayIndex`), as
  upstream's `bool: Typedef<word>` fails. As built in step 6g-i, the index arm decides on its base's
  view, the element type of a memory array or of a slice's base (`Ty.viewElement?`), so `s[i]` on a
  slice is a read at its base's element type, and the read's proofs take the view. A write through a
  slice takes the place arm's mapping rule and is rejected, as upstream's slices have no assignable
  index.
- **Writes.** `a[i] = v`, the compound assignments, in-place `~` and the unchecked forms take the
  element type, with row 1's rules for each type. A write through a slice is rejected. As built in
  step 5a-ii, inference's place arm takes `a[i]` on a base whose resolved type is a memory array as
  an element place, as the read's arm does: the place's type unifies with the element type and the
  index is inferred on its own (`placeIndexEquation`, `placeIndexExpected`, `placeIndexProjection`),
  so `a[i][j] = v` takes two element projections, and on any other base the place keeps the mapping
  rule. Finalization defaults an open literal index to `uint256` (`placeIndexMentions`) and rejects
  another index type with `operatorNotSupported "Typedef"`, as a read's (`validatePlaceElements`).
  As built in step 5b, a compound assignment, its unchecked forms and an in-place `~` take an
  element place too, and finalization checks its indexes as a plain write's; the element's type
  takes the operator's rules, so `rows[0] += xs` or `rows[0] ~=;` on a row is rejected by
  unifying the row with `word`, as a compound assignment or an in-place `~` on any array is. A
  write's base is a place rooted at a local (difference 16), a compound one's too. The element place's static
  rule takes no index kind: its run faults on an index that is not a word, and finalization admits
  a read's index types.
- **Slices** take `uint256` bounds and a base that is an array or a slice, and have the type
  `arraySlice<B>`. As built in step 6a, `arraySlice<B>` resolves to a slice type once aliases are
  expanded, as an intrinsic that a user type of the same name hides, as `integer` is
  (`resolveBuiltinFallback`), with one argument (`typeArityMismatch` otherwise).
  `Ty.arraysWellFormed` admits it when `B` is a memory array or a slice
  (`Ty.arraySliceBaseAllowed`), and `Ty.containsArray` counts it, so a mapping that holds a slice is
  rejected with `unsupportedArrayType`, as is an array of slices, whose element
  `Ty.arrayElementAllowed` does not admit (difference 17). Elaboration and both catalogs reject
  every slice type until step 6h; as built in step 6h, the compatible catalog projects one (see
  Lowering), and elaboration and the strict catalog still reject it. As built in step 6f-ii,
  inference infers a slice's base, then its present bounds, with no expected type, as a tuple's
  elements, and takes the base only when its resolved type is a memory array or a slice there, as a
  read decides on its base; another base is rejected with `unsupportedExpression "slice"`
  (difference 18). It unifies the bounds' types with `uint256`s, as a literal's elements' with its
  element type, so an open literal bound takes `uint256` and a bound of another type is rejected,
  and records the slice at the slice of the base's resolved type (`ExpressionForm.arraySlice`,
  `sliceBoundIds`).
- **Memrefs.** `memref<T>` is std's checked reference to one element of a memory array of `T`:
  `lidx(a, i)` makes one, and `CanStore.load(r)` and `CanStore.store(r, v)` read and write through
  it, in step 7. As built in step 7a, `memref<T>` resolves to a memref type once aliases are
  expanded, as an intrinsic that a user type of the same name hides (`resolveBuiltinFallback`), with
  one argument (`typeArityMismatch` otherwise). `Ty.arraysWellFormed` admits it when `T` is a type a
  memory array holds (`Ty.arrayElementAllowed`), and `Ty.containsArray` counts it, so a mapping that
  holds a memref is rejected with `unsupportedArrayType`, as is an array of memrefs, whose element
  `Ty.arrayElementAllowed` does not admit (difference 21). Elaboration and both catalogs reject
  every memref type until step 7f; as built in step 7f, the compatible catalog projects one (see
  Lowering), and elaboration and the strict catalog still reject it.
- **Lengths.** `a.length`, `a.length()` and `Length.length(a)` on arrays and slices have the type
  `uint256`. `Length.length` is a builtin qualified call when no namespace `Length` exists, as
  `Typedef.abs` is (`typedefCall?`). As built in step 2b-ii-b, `lengthCall` finds the name, and the
  call is recorded as the length's own typed form, whose evaluation reads the array's cell, rather
  than as a builtin function, whose evaluation reads no heap. Its one argument's type must be a
  memory array once its arguments are inferred, as `Typedef.rep`'s must be `word` or a fixed-width
  type. As built in steps 2b-ii-c and 2b-ii-d, `a.length` is a field that names no constructor,
  whose base, inferred with no expected type, must be a memory array, and `a.length()`, a call of it
  with no arguments whose callee inference takes it, is recorded as a group over that field. As
  built in step 6g-i, a length's base may be a slice too: `arrayLengthOf` reads `Ty.viewElement?`.
- **Builtins.** `toArray(s)` is a builtin, and so are `lidx(a, i)`, `CanStore.load(r)` and
  `CanStore.store(r, v)` from step 7. As built in step 6g-ii, `toArrayCall` finds `toArray` when no
  source function, local or compiler function has the name, as `Length.length` is found when no
  namespace or local is named `Length`. The call's one argument must be a slice once its arguments
  are inferred, and its base's view gives the copy's element (`sliceCopyArgument`). The call is
  recorded as the copy's own typed form at an array of that element (`ExpressionForm.toArray`), so
  `toArray(m[1:3])` has the type `uint256[]` where `m` has, and `toArray(rows[0:1])` the type
  `uint256[][]` where `rows` has. A slice still open there is rejected (difference 19), and only a
  call names `toArray` (difference 20). As built in step 7d, `lidxCall` finds `lidx` the same way.
  The call's two arguments are its array, whose type must be a memory array once its arguments are
  inferred, and its index (`elementRefArguments`), and the call is recorded as the memref's own
  typed form at the memref of the array's element (`ExpressionForm.elementRef`), so `lidx(m, i)` has
  the type `memref<uint256>` where `m` has the type `uint256[]`. Its index waits for finalization,
  as a read's does, and must have `word` or one of the twelve types (`validateArrayIndex`). Unlike a
  read's, an open literal index takes no default, so `lidx(m, 1)` is rejected as ambiguous, as the
  pinned driver rejects it. An array still open there is rejected, and only a call names `lidx`
  (difference 22). As built in step 7e-i, `loadCall` finds `CanStore.load` when no namespace or
  local is named `CanStore`, as `lengthCall` finds `Length.length`. The call's one argument must be
  a memref once its arguments are inferred (`memrefLoadArgument`), and the call is recorded as the
  load's own typed form at the memref's element (`ExpressionForm.memrefLoad`), so
  `CanStore.load(lidx(m, i))` has the type `uint256` where `m` has the type `uint256[]`. A memref
  still open there is rejected, and only a call names `CanStore.load` (difference 23). As built in
  step 7e-ii, `storeCall` finds `CanStore.store` the same way. The call's two arguments are its
  memref, whose type must be a memref once its arguments are inferred, and its value
  (`memrefStoreArguments`); the value's type then unifies with the memref's element, as a literal's
  elements' types unify with its element type, so `CanStore.store(r, 7)` stores a `uint8` where `r`
  has the type `memref<uint8>`, and a value of another type is rejected. The call is recorded as the
  store's own typed form at `()` (`ExpressionForm.memrefStore`). A memref still open there is
  rejected, and only a call names `CanStore.store` (difference 24).
- **Rejected.** `Typedef` at an array type, `==` on arrays, `push` and `pop`, and assignment to a
  length. A mapping key or value of an array type is rejected too: upstream's meaning there is a
  storage array. A contract field of an array type parses and, like every contract member, is not
  typed.

### Source semantics

- **Values.** `Dynamic.Value` gains four forms:
  - an array reference, which carries its element type and the location of its object, as Core's
    `cellRef` does;
  - an array object, which holds the elements and lives only in its heap cell;
  - a slice, which holds its base value, its start and its length;
  - in step 7, a `memref`. As built in step 7b, a memref (`Dynamic.Value.memref`) holds its array's
    element type, the location of its cell and its position.
- **Heap.** An array object is a heap cell, whose type is `arrayObject T`, a builtin type that no
  source type names. An allocation appends a cell, so `Dynamic.Heap`, `Dynamic.Heap.Allocates` and
  `Dynamic.Heap.AllocatesCopy` keep their text. Objects never move, grow or shrink, so a reference
  and a `memref` stay valid.
- **Rules.** Each rule comes with its fault rules and its sized copies, as row 1's rules did. The
  staged traces that the source-to-Core theorems are stated over (`Staging.Recursive.Expression`)
  take no array form, as decision 6 keeps arrays outside the meaning proofs.
  - `new T[](n)` panics with `0x41` when `n ≥ 2^251 − 1`. Otherwise it allocates an object of `n`
    zero elements. For an array element type, the elements are `n` references to one fresh empty
    array, as std's `0x60` is.
  - A literal allocates its object first, then evaluates and stores its elements from left to right.
    As built in step 4a, the literal is its own typed form (`ExpressionForm.arrayLiteral`), which
    evaluates its elements from left to right and then allocates the cell holding them: no element
    can observe the object, so where the allocation falls changes no result. Unlike `new`'s, its
    static rule checks no element type; inference's finalization does, in step 4b.
  - A read panics with `0x32` when `i ≥ length`. A read through a slice checks the slice's length,
    then the base's at `start + i`. As built in step 3a, the read is its own typed form
    (`ExpressionForm.arrayIndex`), whose index is a word at `word` or one of the twelve types
    (`ArrayIndexType`), and it faults with the base's fault, the index's, an index that is not a
    word, or `0x32` (`arrayIndexOutOfBounds`). As built in step 6d, a read through a slice is a case
    of the read's rules: the read takes its element through `ViewReads`, which checks a slice's
    length and reads its base at the slice's start plus the position, down to the array's cell, and
    a position out of a view's bounds, the slice's or its base's, panics with `0x32`
    (`ViewOutOfBounds`). The length rule reads `ViewLength`, a slice's own length. Both static rules
    take a base whose type is a memory array or a slice, with its element type (`ViewElement`).
  - An element place `a[i]` evaluates `a` and `i` once and checks `i < length` before the right
    side, as `lidx(a, i)` does. The write replaces the element.
    As built in step 5a-i, an element place is a place whose last projection is an element
    (`PlaceProjection.element`): its leading place resolves first, to an array reference, then the
    index, and the place resolves to the array object's own cell with the element's position as its
    one evaluated projection (`SourcePlaceResolves.element`), so a write replaces the element there
    through `ProjectionsUpdate`'s element case and `ResolvedPlaceWrites` keeps its text. It faults
    with its leading place's fault, the index's, an index that is not a word, `0x32` from the length
    on, or, when its leading is a local not yet initialized, `uninitializedLocation`, as reading
    that local does, all before the right side. The staged traces stage no element place:
    `Staging.Recursive.ProjectedTarget.keys` stops at an element projection.
  - A slice panics with `0x32` when `s > e` or when `e` exceeds the base's length. As built in step
    6c, a slice is its own typed form (`ExpressionForm.arraySlice`), whose start and stop are
    optional, so the four slice forms share it. It evaluates the base, then its present bounds from
    left to right, each a `uint256` word, and fills an absent start with 0 and an absent stop with
    the base's length (`SliceBounds`), as std's `sliceFrom`, `sliceTo` and `sliceAll` do. Once
    `s ≤ e ≤ length`, where the length is an array cell's element count or a slice's own
    (`ViewLength`), it holds the base from `s` on for `e − s` elements. It faults with the base's
    fault, a bound's, a bound that is not a word, or `0x32` (`arraySliceOutOfBounds`).
  - The length rules read the object or the slice, and `toArray(s)` allocates a copy. As built in
    step 6e, `toArray(s)` is its own typed form (`ExpressionForm.toArray`), which evaluates the
    slice, reads its elements in order (`ViewCopies`) and then allocates a fresh array's cell
    holding them, as the literal does: no element can observe the fresh cell, so where the
    allocation falls changes no result. Its result is an array of the slice's element type
    (`ViewElement`), and it faults only with the slice's fault, since a slice's positions lie within
    its base's bounds once it is made.
  - `lidx(a, i)` checks `i < length`, as a read does, and gives a memref to element `i`, through
    which `CanStore.load(r)` reads and `CanStore.store(r, v)` writes. As built in step 7b,
    `lidx(a, i)` is its own typed form (`ExpressionForm.elementRef`), whose index is a word at
    `word` or one of the twelve types (`ArrayIndexType`). It evaluates the array, then the index,
    and below the array's length (`ViewLength`) gives a memref to the element at the index; it
    faults with the base's fault, the index's, an index that is not a word, or `0x32` from the
    length on (`elementRefOutOfBounds`), as std's `LValueIdxAccess` does. As built in step 7c,
    `CanStore.load(r)` and `CanStore.store(r, v)` are their own typed forms
    (`ExpressionForm.memrefLoad`, `ExpressionForm.memrefStore`). The load evaluates the memref and
    reads the element at its position in its array's cell (`ViewReads`). The store evaluates the
    memref, then the value, and the element at the memref's position takes the value
    (`ValuesReplaceAt`), as a plain element write's place does; its value is `()`. Each faults only
    with its operands' faults, since a memref's position lies within its array's bounds once it is
    made.
- **Preservation.** A reference has the type `T[]` when the cell it names has the type
  `arrayObject T`, as Core's runtime typing reads a `cellRef`'s cell in its world, and an object's
  elements each have its element type. A later heap keeps every cell's type, so a reference keeps
  its type, and `Dynamic.HeapWellTyped` keeps its text. As built in step 6b, a slice
  (`Dynamic.Value.arraySlice`) holds its base value, its start and its length, and has the type
  `arraySlice<B>` when its base has the type `B`, a memory array or a slice
  (`ValueHasType.arraySlice`). Its typing reads no bound: a slice is made only once its bounds are
  checked, and a read through it checks them again, so a later heap keeps its type too. As built in
  step 7b, a memref has the type `memref<T>` when the cell it names has the type `arrayObject T`, as
  a reference does (`ValueHasType.memref`), so `lidx(a, i)`'s memref has its array's element type
  (`ValueHasType.memref_of_arrayRef`). As built in step 7c, a load has its memref's element type,
  read through the array's reference (`ValueHasType.arrayRef_of_memref`), and a store keeps the heap
  well typed: the cell's object keeps its type (`ValueHasType.arrayElementWrite`).
- **Panics** reuse `SemanticFault.panic`.

### Lowering

- An array is a Core cell. The cell holds the length, the default element (zero, or the shared
  empty array for an array element type) and the present elements in an `OrderedMapping` from index
  to element. A source array value is the cell's `cellRef`, and nested arrays hold `cellRef`s.
- `new` allocates the cell with no entries, so an absent element reads as the default. Reads and
  writes check the length, then look up or update the entry.
- As built in step 2b-iii, the public compiler lowers through the compatible profile, so its
  catalog (`SourceCoreCompatibleCatalog`) registers `T[]`'s element mapping as `mapping(word => T)`
  and projects `T[]` to the cell of a word, the element's Core type and that mapping, and its data
  lowering (`SourceCoreCompatibleDataExpressions`) lowers `new` and the length. The projection tests
  an application's runtime head, so that a type and its runtime type project alike. A nested
  element's default is one fresh empty array per `new`. The strict representation's catalog and
  direct linking still reject `T[]`.
- As built in step 3c, that data lowering lowers `a[i]` on a memory array: it evaluates the array,
  then the index, panics with `0x32` from the cell's length on, and otherwise looks the index up in
  the cell's mapping, an absent element reading as the cell's default element
  (`SourceCoreDataExpressions.arrayIndex`). The index's Core value is its word, so a negative signed
  index panics, as upstream's `Typedef.rep(j)` gives it a word from 2^255 on.
- As built in step 4c, that data lowering lowers `[e₀, …, eₙ₋₁]`: it evaluates the elements from
  left to right, packed as a call's arguments are, and then allocates the cell of the length `n`,
  the default element and the element at each index below `n`
  (`SourceCoreDataExpressions.arrayLiteral`), as the source semantics evaluates the elements before
  it allocates.
- As built in step 5a-iii-a, the place lowering lowers a plain write to an element of a memory
  array, a root local followed by elements (`SourceCoreCompatibleDataPlaces.lowerElements`); every
  other place keeps its route (`lowerRoute`). It reads the root's array, failing with the place's
  reason when the root is not yet initialized, then each index, panicking with `0x32` from its
  array's length on, and for an inner index the next array, as a read does. Only then does it
  evaluate the right side, and the last array's cell takes the value at its index
  (`arrayElementWrite`). That is the source semantics' order and upstream's `lidx(a[i], j)`; the
  route's `execute` evaluates every key first, so it could not be reused. The compatible fault-site
  pass reserves the write's place reason, as a projected route's
  (`SourceCoreCompatibleDataPlaceFaultSites.prepare`). The place lowering's receipt takes the
  write's plain-ness (`CompatiblePlaceCompilerCertificates.generated_of_lower`), which a bare place,
  an in-place `~` and a mapping route give (`Route.elementFree`), and the statement recognizers'
  value-assignment cases and the heads that reach the receipt take the place's element-freeness, as
  a field or a hypothesis.
- As built in step 5b, the place lowering sends every write to an element there, plain, compound,
  unchecked or an in-place `~` (`SourceCoreCompatibleDataPlaces.lower` on `takesElement`). After
  the last index's `0x32` check, a compound assignment or an in-place `~` reads the element present
  at the index or the array's default element, as a read does, then evaluates the right side, and
  the last array's cell takes `modified`'s leaf after `guard`'s check (`elementStore`), with the
  route's modifier, wrap and checks (`placeModifier`, `placeWrap`), as its `execute` gives a local
  or a mapping. So the place is evaluated once, its element is read before the right side, and
  `Panic(0x11)` and `Panic(0x12)` come after it, as in the source semantics, whose element place
  already resolved once (`SourcePlaceResolves.element`) and whose compound rules take any place.
  The place receipt takes the place's element-freeness (`takesElement_of_free`) instead of the
  write's plain-ness, which an in-place `~` no longer gives: the projected in-place `~` receipts,
  heads and certificates and the recognizers' projected in-place `~` cases take it as a field or a
  hypothesis, from their mapping route (`Route.elementFree`).
- A slice is a Core product of its base, its start and its length.
- As built in step 6h, the compatible catalog projects `arraySlice<B>` to the product of `B`'s Core
  type and two words, and registers `B`. The data lowering reads a view's shape from its Core type
  (`SourceCoreDataExpressions.viewShape?`): a memory array's cell inside some slices. A slice
  evaluates its base, then its present bounds from left to right, fills an absent start with 0 and
  an absent stop with the base's length, and panics with `0x32` unless `s ≤ e ≤ length`, else holds
  the base, `s` and `e − s` (`arraySlice`). A slice's length is its own (`sliceLength`). A read
  through a slice panics with `0x32` from the slice's length on, then reads the base at the slice's
  start plus the index, down to the array's cell, whose read is 3c's (`viewIndex`, `viewRead`), as
  the source semantics' `ViewReads` does. `toArray(s)` evaluates the slice, reads its elements from
  position 0 on with a recursive Core helper, a self closure in a cell as `OrderedMapping`'s lookup
  is (`sliceCopyBody`), and then allocates the cell of the slice's length, the default element of
  the array under it and those elements (`sliceCopy`), as the source semantics' `ViewCopies` and its
  allocation do. Core does not change.
- As built in step 7f, the compatible catalog projects `memref<T>` to the product of `T[]`'s Core
  type and a word, its array and its position, and registers `T[]`'s mapping. `lidx(a, i)` evaluates
  the array, then the index, panics with `0x32` from the array's length on, and otherwise holds the
  array and the index (`SourceCoreDataExpressions.elementRef`), as std's `LValueIdxAccess` does.
  `CanStore.load(r)` evaluates the memref and reads the element at its position as a read does
  (`memrefLoad`). `CanStore.store(r, v)` evaluates the memref, then the value, and the array's cell
  takes the value at the memref's position, keeping its length and default element, as an element
  write's last array does (`memrefStore`). A memref's position is below its array's length, which no
  write changes, so the load's check passes. Core does not change.
- Arrays stay outside `StaticProfile` and the proved subset, as row 1's conversions did. The
  meaning proofs and their statements do not change.

### Public API

A root whose signature mentions an array or a slice is rejected. Tests reach arrays through
functions over words, as row 1's fixture ports did.

As built in step 5a-iii-b, the array fixtures test runs mem-array's `setGet`, `fillAndSum`,
`nestedReplace` and `alias` as upstream wrote them. It runs memory-array-abi's `ret`, `sum` and
`grid` as upstream wrote them too, behind word wrappers, since a root's signature takes no array:
`retAt(n, i)` and `retLength(n)` read `ret(n)`; `sumFour(a, b, c, d)` and `sumNone()` pass `sum` the
literals `[a, b, c, d]` and `[]`; and `gridLength(n)`, `gridRowLength(n, i)` and `gridAt(n, i, j)`
read `grid(n)`. The wrappers change only how an array arrives, a literal of word arguments instead
of the ABI's decoding, and how one leaves, read back by index or length instead of ABI-encoded. So
the fixture's `ret(3) -> [0,2,4]` is checked as 0, 2 and 4 at indexes 0 to 2 and length 3,
`ret(0) -> []` as length 0, `sum([1,2,3,4]) -> 10` and `sum([]) -> 0` as those sums, and
`grid(2) -> [[],[0]]` as length 2, rows of lengths 0 and 1, and 0 at `[1][0]`.

As built in step 6h, the array fixtures test runs array-slice's `build()` and its 11 public
functions that need no storage as upstream wrote them: `rangeLen`, `rangeGet`, `fromLen`, `toLen`,
`allLen`, `reslice`, `bounds`, `materialise`, `aliasing`, `spec` and `ternaryBound`. `build()` and
`aliasing()` write through step 5a's element writes. It runs memory-array-abi's `slices(xs)` as
upstream wrote it, behind a word wrapper, `slicesAt(x0, x1, x2, x3, i)`, which returns
`slices([x0, x1, x2, x3])[i]`. The wrapper changes only how the array arrives, a literal of word
arguments instead of the ABI's decoding, and how the copy leaves, read back by index instead of
ABI-encoded, so the fixture's `slices([10,20,30,40]) -> [20,30]` is checked as 20 at index 0, 30 at
1 and `0x32` at 2. No other function was adapted.

As built in step 7f, the array fixtures test runs mem-array's `bump(r)` and `bumpElement(v)` as
upstream wrote them, with the contract's method as a function, so the fixture's
`bumpElement(7) -> 8` is checked through `bump`, which loads and stores through `lidx`'s memref. No
other function was adapted.

As built in step 5b, the array fixtures test runs mem-array's `compound(v)` as upstream wrote it,
so `#[(10) -> 13]` holds, and memory-array-abi's `echo(xs)` as upstream wrote it, behind word
wrappers, as `ret`, `sum` and `grid` are: `echoAt(x0, x1, i)` returns `echo([x0, x1])[i]` and
`echoLength(x0, x1)` its length, so the fixture's `echo([7,8]) -> [8,9]` is checked as 8 at index
0, 9 at 1 and length 2. No other function was adapted. The lane's probe's `compoundTwice()` gives
105, where upstream gives 205 (difference 1), and `plainOnce()` 107, as upstream.

### Outside row 4's Lean side

- Storage arrays, so no `0x31`; calldata arrays; and `T[]` in the ABI. These need the native
  pipeline's contract storage and calldata ABI first.
- User collections indexed through `RValueIdxAccess`. They need std's traits, and `Typedef` at a
  type parameter, which is row 1's open gap.
- Raw memory: `get_free_memory()`, `allocate_memory(size)`, `mload`, `mstore` and
  `abi_encode(v)`.
- The meaning proofs for arrays (decision 6).

## Differences from upstream that Lean would keep

1. **One evaluation of an element place in a compound assignment** (decision 3).
   `m[next(c)] += 5` runs `next` once, so the probe's 205 is 105 in Lean. This is row 1's choice for
   compound assignments ([row 1's compound assignments](integer-types-unchecked-shifts.md#row-1s-compound-assignments-checked-at-the-guard-outside-the-meaning-proofs)).
2. **`0x41` only from the length check** (decision 2).
   - For lengths just below 2^251 − 1, the pinned backends disagree with each other. Each panics
     where its own free pointer makes the end wrap, and halts otherwise. Lean allocates.
   - Lengths that exhaust EVM memory run out of gas there and allocate in Lean, whose Core does not
     meter gas.
3. **No addresses.** `Typedef.rep` and `Typedef.abs` at an array type, `memory<…>` and
   `DynArray<…>`, and std's allocation functions are rejected. So is an array used as an index, with
   `operatorNotSupported "Typedef"`: upstream's read takes any `i: Typedef<word>` (`std.sol:3115`),
   which `memory<t>` has (`std.sol:1229-1244`), so the pinned driver compiles `a[b]` with `b` an
   array, whose read takes `b`'s address as the index
   (`.upstream/lane-d-unit3-memory-arrays/probe/compile/index-array`).
4. **`arraySlice<B>` is a type only.** A program cannot build or match a slice by hand, while
   upstream exports the constructor.
5. **`T[]` only where the native pipeline has a meaning for it.** Storage and calldata arrays,
   mappings of arrays and `T[]` in public signatures are rejected.
6. **Element types are checked where the type is formed.**
   - `bool[]` is rejected even where upstream accepts it, which is until an operation requires
     `Typedef<word>`.
   - Generic `t[]` is rejected, since Lean cannot write `where t: Typedef<word>`. This is row 1's
     gap for generic code over std's instances.
7. **`new`'s length is a `uint256`, an open literal included.** Upstream's checker passes a `word`
   length on to specialization (SC0405) and finds a `let`-bound literal length ambiguous (SC0299).
   Both are recorded in `questions.md`.
8. **An unannotated `let m = [];` is rejected, used or not.** The `let` generalizes the literal's
   open element type, as Lean generalizes any open type at a `let`, so no use fixes it, and
   finalization rejects it with `operatorNotSupported "Typedef"`, as an open `Typedef` call is. An
   annotation (`let m: uint256[] = [];`) or an expected type (`return [];`, an argument) gives the
   type. Upstream accepts it and takes the type from its uses.
9. **The suffix room is 127 at every depth.** Upstream's room is 128 less the type's depth, so it
   is smaller inside `<…>`, `(…)` or `@`. Lean bounds no type depth, and counts only the suffixes
   on one type.
10. **Past the room, Lean keeps every suffix in the AST.** Upstream truncates the type to its
    room. Both report the nesting error.
11. **A size is bounded by the window.** `T[k]` runs to the first `]` in the parser's window, so a
    `[` with no `]` after it ends the type, and the enclosing parser reports the `[`. Upstream's
    size runs to the next `]` anywhere in the file, and it reports its furthest failure for an
    unclosed `[`.
12. **Lean commits after `new T[](`.** Once `new`, an array type and the `(` are read, the length
    and the `)` are required, and their errors are reported. Upstream backtracks its whole
    alternative, so for `new T[](<bad>` it reports a later error at `T`.
13. **Lean parses on after `a[]`.** Its brackets hold an error node after upstream's error, as
    `T[k]` keeps `T[]`. Upstream's index fails there, and its recovery skips the rest of the
    statement. The reports agree where the rest of the statement parses and where only a later
    statement fails. They differ where the same statement fails later: `return a[] + ;` gets
    upstream's error over the `[]` at the pin, and in Lean the `;` and then the `]`, as
    `return a[1] + ;` does, since Lean's recovery of a failed statement does not keep the `[]`'s
    error (`.upstream/lane-d-unit3-memory-arrays/step1/1c-probe`).
14. **A length needs its array known where the length is.** `Length.length(a)`, `a.length` and
    `a.length()` are rejected with `operatorNotSupported "Length"` when `a`'s type is still open
    there, as an open `Typedef` call is
    ([row 1's conversions](integer-types-unchecked-shifts.md#row-1s-conversions-a-word-becomes-a-value-only-when-canonical)).
    Only the array must be known, not its element: `arrayLengthOf` reads the resolved type's
    `arrayElement?`, so an array whose element type is still open is accepted. Upstream's `Length`
    constraint waits for later uses to fix the type. As with the open `Typedef` call, deferring the
    choice to finalization could lift this, and nothing schedules it.
15. **A read needs its array known where the read is.** `a[i]` on a base whose type is still open
    there takes the mapping rule, as the Typing section says, so a base that later turns out to be a
    memory array is rejected with a type mismatch. Upstream's `RValueIdxAccess` constraint waits for
    later uses to fix the type. As with difference 14, deferring the choice to finalization could
    lift this, and nothing schedules it.
16. **An element write's base is a local, or an element of one.** Lean's assignment target is a
    place rooted at a local: an identifier, a group, or an index of a place. So `same(m)[1] = v`,
    whose base is a call's result, is rejected with `invalidAssignmentTarget`, while the pinned
    driver accepts it, as it accepts a struct field's element `s.xs[1] = v`
    (`.upstream/lane-d-unit3-memory-arrays/step5a/probe`); Lean has no `struct`. Binding the array
    to a local first, `let r = same(m); r[1] = v;`, writes the same object, since an array is a
    reference. No element place has a member or a mapping index before its elements, since
    inference's places hold no member and a mapping of arrays is rejected (difference 5), so the
    lowering takes a local followed by elements only.
17. **A slice views a memory array or a slice, and no array or mapping holds a slice.** Lean forms
    `arraySlice<B>` only over the bases of the four slice forms, so `arraySlice<uint256>` is
    rejected with `unsupportedArrayType`, while the pinned driver forms it, since its
    `arraySlice<coll>` is an enum over any `coll`, whose values over other bases only its
    constructor makes (difference 4). An array of slices is rejected where the type is formed, as
    `bool[]` is (difference 6): the pinned driver accepts the annotation `arraySlice<uint256[]>[]`,
    and fails `new arraySlice<uint256[]>[](2)` with SC0207, since a slice has no `Typedef<word>`. A
    mapping that holds a slice is rejected as one that holds an array is (difference 5), while the
    pinned driver accepts a contract field of that type
    (`.upstream/lane-d-unit3-memory-arrays/step6/probe`).
18. **A slice needs its base's type known where the slice is.** `a[s:e]`, `a[s:]`, `a[:e]` and
    `a[:]` on a base whose type is not a memory array or a slice there are rejected with
    `unsupportedExpression "slice"`, as a read on such a base takes the mapping rule (difference
    15). Upstream's `Length` constraint waits for later uses to fix the type. As with differences 14
    and 15, deferring the choice to finalization could lift this, and nothing schedules it.
19. **A copy needs its slice known where the copy is.** `toArray(s)` is rejected with
    `operatorNotSupported "toArray"` when `s`'s type is not a slice there, as a length is on an
    array still open (difference 14). The pinned driver compiles `lam(s) { return toArray(s); }`
    applied to `m[0:2]`, as it compiles `lam(s) { return Length.length(s); }` applied to `m`, since
    its constraints wait for later uses to fix the type
    (`.upstream/lane-d-unit3-memory-arrays/step6/probe-6gii`). Only the slice must be known, not its
    element: an element still open is the copy's. As with differences 14, 15 and 18, deferring the
    choice to finalization could lift this, and nothing schedules it.
20. **`toArray` and `Length.length` are only called.** Lean has them as compiler forms that a call
    names, as row 1 has `Typedef.abs`, so `let copy = toArray;` is rejected with
    `unknownVariable "toArray"`, and `let size = Length.length;` with `unknownVariable "Length"`.
    The pinned driver compiles both, since std's `toArray` and `Length.length` are functions there
    (`.upstream/lane-d-unit3-memory-arrays/step6/probe-6gii`).
21. **A memref refers to an element a memory array holds, and no array or mapping holds a memref.**
    `memref<bool>` is rejected where the type is formed, as `bool[]` is (difference 6), and so are a
    memref of a slice and of a memref; generic `memref<t>` is rejected as generic `t[]` is. The
    pinned driver accepts the annotation `memref<bool>`, and generic `memref<t>` with
    `where t: Typedef<word>`. An array of memrefs is rejected where it is formed: the pinned driver
    accepts the annotation `memref<uint256>[]` and fails `new memref<uint256>[](2)` with SC0207,
    since a memref has no `Typedef<word>`. A mapping that holds a memref is rejected as one that
    holds an array is (difference 5), while the pinned driver accepts a contract field of that type
    (`.upstream/lane-d-unit3-memory-arrays/step7/probe`).
22. **`lidx` needs its array known where the call is, and is only called.** `lidx(a, i)` is rejected
    with `operatorNotSupported "lidx"` when `a`'s type is not a memory array there, as a copy is on
    a slice still open (difference 19), and `let at = lidx;` with `unknownVariable "lidx"`, as
    `toArray` is (difference 20). The pinned driver compiles
    `lam(a) { return lidx(a, uint256(1)); }` applied to `m`, and `let at = lidx;` applied to `m` and
    `uint256(1)`, since std's `lidx` is a function there whose constraints wait for later uses
    (`.upstream/lane-d-unit3-memory-arrays/step7/probe`). Only the array must be known, not its
    element. As with differences 14, 15, 18 and 19, deferring the choice to finalization could lift
    the first, and nothing schedules it.
23. **`CanStore.load` needs its memref known where the call is, and is only called.**
    `CanStore.load(r)` is rejected with `operatorNotSupported "CanStore"` when `r`'s type is not a
    memref there, as a memref is on an array still open (difference 22), and
    `let get = CanStore.load;` with `unsupportedExpression "field"`, as `Length.length` is only
    called (difference 20). The pinned driver compiles `lam(r) { return CanStore.load(r); }` applied
    to `lidx(m, uint256(1))`, and `let get = CanStore.load;` applied to the same memref, since std's
    `CanStore` instance resolves once later uses fix the type
    (`.upstream/lane-d-unit3-memory-arrays/step7/probe`). Only the memref must be known, not its
    element. As with differences 14, 15, 18, 19 and 22, deferring the choice to finalization could
    lift the first, and nothing schedules it.
24. **`CanStore.store` needs its memref known where the call is, and is only called.**
    `CanStore.store(r, v)` is rejected with `operatorNotSupported "CanStore"` when `r`'s type is not
    a memref there, as a load is (difference 23), and `let put = CanStore.store;` with
    `unsupportedExpression "field"`, as `let get = CanStore.load;` is. The pinned driver compiles
    `lam(r) { CanStore.store(r, uint256(5)); }` applied to `lidx(m, uint256(1))`, and
    `let put = CanStore.store;` applied to the same memref and `uint256(5)`
    (`.upstream/lane-d-unit3-memory-arrays/step7/probe`). The value's type, unlike the memref's, may
    still be open: it unifies with the element. Both drivers reject a value of another type, the
    pinned driver with SC0207. As with difference 23, deferring the choice to finalization could
    lift the first, and nothing schedules it.

Differences 2 and 4 to 8 were accepted with the decisions, 9 to 12 on 2026-11-13, 13 and 14 on
2026-11-14, 15 and 16 on 2026-11-15, when 8 was also widened from an unused `let m = [];` to any
unannotated one, 17 to 22 on 2026-11-16, and 23 and 24 on 2026-11-17. Differences 9 to 13 change
only a diagnostic or the room of a resource limit, and 8 and 14 to 24 only reject some programs that
upstream accepts. None of them changes what an accepted program means. Difference 1 does, and was
accepted with decision 3 on 2026-11-17.

## Steps

The yardstick is row 1's step 3c, 36 files, +868/−224. Each step stays within twice 3c: 72 files,
+1,736/−448. Every step adds tests through the public API and keeps every array form outside the
meaning proofs. A program that mentions no array keeps all its proofs.

| Step | Content | Estimate | Ports |
| --- | --- | --- | --- |
| 1a | Syntax: `T[]`, with `T[k]` rejected and the suffixes counted against the nesting limit, the grammar and its proofs; type resolution rejects array types. Two commits: 1a-i, the suffix layer as a refactor that accepts no new syntax, then 1a-ii, the suffix | 25–32 files, +1,600–2,000/−350–450; 1a-i measured at 6 files, +156/−57 | parser tests from upstream's `crates/uitest/tests/fixtures/parse/fixed_size_array_rejected` and `crates/parser/tests/formatting.rs` cases |
| 1b-i | Syntax: the head `new T[](`, with its grammar and every lemma, and direct tests of its parser; no atom reaches it yet | 10–12 files, +700–900; measured at 10 files, +636/−0 | none |
| 1b-ii | Syntax: `new T[](n)` in the name atom, falling back to the identifier `new` where no head starts; inference rejects it | 18–26 files, +900–1,100/−50–150; measured at 27 files, +1,412/−199 | `crates/parser/tests/formatting.rs` and `crates/parser/src/parse/mod.rs` cases |
| 1c-i | Syntax: the bracket contents layer, as a refactor that accepts no new syntax: what a `[` after an expression holds has its own parser, grammar and lemmas, and an index is its one form | 10–12 files, +650–750/−150–200; measured at 12 files, +696/−182 | none |
| 1c-ii-a | Syntax: the optional bound that an index and a slice's start and stop read, with its grammar and every lemma, and direct tests of its parser; no bracket reads it yet | 10–12 files, +500–600; measured at 10 files, +560/−4 | none |
| 1c-ii-b | Syntax: the slices, with `a[]` rejected, as the bracket contents' other forms; inference rejects the slices | 18–22 files, +1,200–1,400/−250–300; measured at 21 files, +1,374/−283 | parser tests from `crates/uitest/tests/fixtures/parse/empty_index_rejected`, `crates/parser/tests/formatting.rs` and `crates/parser/src/parse/mod.rs` cases |
| 2a-i | The array type: `T[]` resolves to a memory array once aliases are expanded, type resolution checks its element and rejects a mapping that holds an array, and type formation admits it; no value has an array type yet, and elaboration rejects every array type | 25–35 files, +300–500/−20–60; measured at 27 files, +458/−75 | none |
| 2a-ii | The store: an array object, a reference to it and their typing, with the typing's laws; no expression makes one yet | 20–40 files, +400–800/−50–150; measured at 17 files, +214/−18 | none |
| 2b-i | `new T[](n)` and `0x41`: inference, evaluation and its fault, the sized and staged copies and preservation. Three commits: 2b-i-a, `new`'s own arm in inference, which still rejects it and renumbers the cases of the proofs by functional induction on `inferExprFuel`; 2b-i-b, the typed form `new` with its static rule, evaluation, faults, sized copies, stage and preservation, which no source produces yet; then 2b-i-c, inference's typing of `new` | 35–60 files, +900–1,500/−100–300; 2b-i-a measured at 15 files, +293/−286, 2b-i-b at 28 files, +338/−6, 2b-i-c at 25 files, +799/−19 | none |
| 2b-ii | The lengths: `a.length`, `a.length()` and `Length.length(a)`. Four commits: 2b-ii-a, the typed form of a memory array's length with its static rule, evaluation, fault, sized copies, stage and preservation, which no source produces yet; 2b-ii-b, inference's typing of `Length.length(a)`, a compiler function's qualified name as `Typedef.abs` is; 2b-ii-c, inference's typing of `a.length`, a field that names no constructor, whose base is a new child of inference's call tree; then 2b-ii-d, `a.length()`, a call of that field with no arguments | 30–50 files, +600–1,000/−100–200; 2b-ii-a measured at 27 files, +160/−10, 2b-ii-b at 19 files, +484/−10, 2b-ii-c at 23 files, +602/−90, 2b-ii-d at 20 files, +593/−51 | none |
| 2b-iii | The lowering: the Core cells of `new` and the lengths | 15–30 files, +400–800/−50–150; measured at 10 files, +175/−6 | newLen(n), oversized(n) |
| 3a | Element reads: the typed form of `a[i]` on a memory array with its static rule, evaluation, faults with `0x32`, sized copies, stage and preservation, which no source produces yet | 28–32 files, +400–550/−5–15; measured at 27 files, +352/−10 | none |
| 3b | Element reads: inference's typing of `a[i]` on a memory array, whose index waits for its type until finalization checks that it is `word` or one of the twelve types | 26–32 files, +800–1,000/−100–180; measured at 28 files, +1,156/−57 | none |
| 3c | Element reads: the lowering, with `0x32` | 4–6 files, +120–200; measured at 4 files, +73/−13 | defaultZero(n, i), nestedEmpty(n) |
| 4a | Literals: the typed form of `[e₀, …, eₙ₋₁]` with its static rule, evaluation, fault, sized copies, stage and preservation, which no source produces yet | 28–32 files, +350–500/−5–15; measured at 27 files, +192/−6 | none |
| 4b | Literals: inference's typing of `[e₀, …, eₙ₋₁]` at one element type, with `[]` taking it from the expected type, open literal elements defaulting to `uint256` and finalization's check of the element type | 26–34 files, +900–1,300/−30–80; measured at 24 files, +1,005/−19 | none |
| 4c | Literals: the lowering | 4–7 files, +150–300/−5–20; measured at 3 files, +91/−3 | pair(a, b), local(a, b), returned(a, b), nested(), callResultLength(n), sumAll(xs) |
| 5a-i | Plain element writes: the typed element place `p[i]` (`PlaceProjection.element`), with its static rule, its resolution to the array object's cell, its five faults, `0x32` from the length on before the right side, sized copies, stage and preservation, which no source produces yet | 30–45 files, +500–900/−10–60; measured at 58 files, +890/−65 | none |
| 5a-ii | Plain element writes: inference's typing of `a[i] = v` on a memory array, a nested place such as `a[i][j] = v` included, whose index finalization checks as a read's; a compound assignment or an in-place `~` to an element stays rejected | 40–60 files, +1,300–2,200/−150–400; measured at 36 files, +1,129/−647 | none |
| 5a-iii-a | Plain element writes: the lowering, with `0x32` before the right side, the fault-site pass's case and the element-freeness that the statement meaning proofs take | 4–8 files, +200–400/−5–30 at first; measured at 55 files, +706/−261 | none |
| 5a-iii-b | Plain element writes: the ports | 1–2 files, +100–200; measured at 1 file, +104/−2 | setGet(n, i, v), fillAndSum(n), nestedReplace(n, v), alias(v); ret(n), sum(xs), grid(n) adapted |
| 5b | Compound assignments to an element, with in-place `~` and the unchecked forms, after decision 3, which evaluate the place once | 25–40 files, +600–1,100/−50–150; measured at 20 files, +381/−152 | compound(v); echo(xs) adapted |
| 6a | Slices: the slice type `arraySlice<B>`, which resolves once aliases are expanded, over a memory array or a slice; type formation admits it, an array or a mapping that holds one is rejected, and elaboration rejects every slice type | 25–30 files, +300–500/−20–60; measured at 27 files, +386/−62 | none |
| 6b | Slices: the slice value, which holds its base value, its start and its length, and its typing in a heap, with the typing's laws; no expression makes one yet | 15–20 files, +200–400/−10–20; measured at 9 files, +101/−10 | none |
| 6c | Slices: the typed form of `a[s:e]`, `a[s:]`, `a[:e]` and `a[:]` with its static rule, evaluation, faults with `0x32` from its bounds, sized copies, stage and preservation, which no source produces yet | 28–32 files, +350–550/−5–15; measured at 27 files, +361/−9 | none |
| 6d | Slices: reads and lengths through a slice, as cases of 3a's and 2b-ii-a's rules, with their faults, sized copies, stage and preservation | 28–32 files, +350–550/−5–15; measured at 15 files, +203/−102 | none |
| 6e | Slices: the typed form of `toArray(s)` with its static rule, evaluation, fault, sized copies, stage and preservation, which no source produces yet | 28–32 files, +300–500/−5–15; measured at 26 files, +207/−7 | none |
| 6f-i | Slices: the slices' own arm in inference, which still rejects them and renumbers the cases of the proofs by functional induction on `inferExprFuel` | 14–15 files, +285–295/−285–295; measured at 15 files, +292/−289 | none |
| 6f-ii | Slices: inference's typing of the four slice forms on an array or a slice, with `uint256` bounds | 24–30 files, +800–1,100/−20–50; measured at 22 files, +1005/−15 | none |
| 6g-i | Slices: inference's typing of reads and lengths through a slice: the read's arm and the lengths take the view of a memory array or of a slice (`Ty.viewElement?`), and the read's and the lengths' proofs take it | 18–25 files, +250–450/−100–200; measured at 23 files, +210/−110 | none |
| 6g-ii | Slices: inference's typing of `toArray(s)` | 15–25 files, +450–700/−10–30; measured at 19 files, +553/−11 | none |
| 6h | Slices: the lowering, a slice as a Core product of its base, its start and its length, and `toArray(s)`'s copy | 4–9 files, +200–400/−10–20; measured at 9 files, +286/−12 | array-slice's build() and its 11 portable public functions, build() and aliasing() through 5a's writes; slices(xs) through slicesAt(x0, x1, x2, x3, i) |
| 7a | Memrefs: the memref type `memref<T>`, which resolves once aliases are expanded and which type formation admits over a type a memory array holds; no value has it yet, and elaboration and both catalogs reject it | 25–30 files, +350–500/−20–70; measured at 27 files, +385/−57 | none |
| 7b | Memrefs: the memref value and the typed form of `lidx(a, i)`, with its static rule, evaluation, faults with `0x32`, sized copies, stage and preservation, which no source produces yet | 28–34 files, +400–650/−10–30; measured at 34 files, +409/−19 | none |
| 7c | Memrefs: the typed forms of `CanStore.load(r)` and `CanStore.store(r, v)`, with their static rules, evaluation, faults, sized copies, stage and preservation, which no source produces yet | 28–34 files, +450–700/−10–30; measured at 26 files, +426/−11 | none |
| 7d | Memrefs: inference's typing of `lidx(a, i)`, a compiler call whose index waits for finalization as a read's | 22–30 files, +650–950/−10–40; measured at 22 files, +641/−42 | none |
| 7e-i | Memrefs: inference's typing of `CanStore.load(r)` | 18–24 files, +450–650/−10–30; measured at 20 files, +518/−5 | none |
| 7e-ii | Memrefs: inference's typing of `CanStore.store(r, v)`, whose value's type unifies with the element type | 22–30 files, +700–1,100/−10–40; measured at 20 files, +663/−4 | none |
| 7f | Memrefs: the lowering, a memref as a Core product of its array's cell and its index, and the loads and stores through it | 8–12 files, +250–450/−10–30; measured at 9 files, +151/−5 | bump(r), bumpElement(v) |
| 8 | All ports in one test, as row 1's step 8e | 2–4 files, +250–450 | the 34 functions above |

In all, that is about 785 to 1,079 file changes, +20,535 to 30,895 and −2,015 to 3,880 lines over
forty-six commits: about one to one and a half times row 1, whose 23 commits added about 21,700
lines, much of them meaning proofs. Step 1 was one row of 35–50 files, +900–1,300/−400–600, until
its first measure: it adds three AST forms through the proved parser, so it became 1a to 1c. 1b's
first measure, about +1,800, split it again into 1b-i and 1b-ii. 1c split as 1a did, before its
forms: 1c-i's measure and 1c-ii's estimate together pass the cap. 1c-ii's first measure, +1,854,
split it again as 1b did, into 1c-ii-a and 1c-ii-b.

Step 5 splits in two (2026-11-15): 5a, plain element writes, which decision 3 does not touch, since
a plain write checks its place before the right side and evaluates its index once, as upstream's
does, and 5b, compound assignments to an element, which wait for decision 3. 5a comes before step 6,
since every array-slice port builds its array with plain writes.

Step 5a was one row of 70–95 files, +1,900–3,100/−100–300, already over the cap, until its first
measure: about 70 to 100 file changes, +2,150 to 3,500/−80 to 270. The element place takes a
projection with its static rule, its resolution, five faults and their sized rules, as the read did
in 3a, and every proof that cases on place projections or place rules takes it; the lowering's
data-place proofs, whose route rejects an element, take an element-free hypothesis that their
compiled path supplies. Inference's place arm takes an array branch whose index waits for its type
until finalization checks it, as 3b's read. So it split into 5a-i, the typed place, 5a-ii,
inference's typing, and 5a-iii, the lowering.

5a-ii measured 36 files, +1,129/−647, past the cap's −448 in deletions. Its deletions are rewritten
proofs: the two typing routes came to share one proof of the place index arm, and the mapping-only
proofs became splits on the base's type. It was kept as one commit on 2026-11-15. 5a-iii passed its
row many times over once begun: an element place satisfies the place typing that the statement
meaning proofs assume, so once the lowering accepts a write to one, every proof that inverts the
place lowering's receipt must rule it out, and the fault-site pass must reserve the write's fault
word. So it split into 5a-iii-a, the lowering with those proofs, and 5a-iii-b, the ports.

Step 5b stayed one commit after decision 3's answer (2026-11-17). The source semantics needed
nothing, since its element place already resolves once and its compound rules take any place, and
inference only its finalization check. The lowering took the element path's last write, and an
in-place `~` stopped giving a write's plain-ness, so the projected in-place `~` receipts and the
recognizers' projected in-place `~` cases took the place's element-freeness, as 5a-iii-a's value
assignments had.

Step 2 was one row of 60–72 files, +1,300–1,700/−300–450, until its first measure: about 110 to 150
files, +3,000 to 4,500/−400 to 800. `new` and the lengths each take a typed form with its
evaluation, fault and sized rules, as row 1's 3c did, and every induction over types takes the
array's case. So it split into 2a, the type and the store, then 2b, `new`, the lengths and the
lowering, and each again by what one part prepares for the next. `new` took its own arm in inference
in a commit that only renumbers the cases of the proofs by functional induction on `inferExprFuel`
and still rejects `new`: 281 lines in 14 files, within 1b-ii's estimate of 285. Each later step
stops on the same size condition, and on any change to a statement named in the
[open decisions](#open-decisions) beyond the ones listed there.

Step 3 was one row of 35–55 files, +800–1,200/−200–350, until its first measure: about 58 to 70 file
changes, +1,300 to 1,750/−100 to 200. The read takes a typed form with its evaluation, its four
faults and their sized rules, as `new` did in 2b-i-b, and inference's index arm takes an array
branch whose index waits for its type until finalization checks it, as row 1's shift amounts do. So
it split into 3a, the typed form, 3b, inference's typing, and 3c, the lowering.

Step 4 was one row of 30–45 files, +600–900/−100–250, until its first measure: about 58 to 73 file
changes, +1,400 to 2,100/−40 to 115. The literal takes a typed form with its evaluation, fault and
sized rules, as `new` did in 2b-i-b, and inference's array arm infers the elements at one element
type, which finalization checks, as 3b's index. So it split into 4a, the typed form, 4b, inference's
typing, and 4c, the lowering.

Step 6 was one row of 45–65 files, +1,000–1,400/−200–400, until its first measure: about 170 to 215
file changes, +3,100 to 5,000/−100 to 250. The slice is a new type and a new value, as `T[]` was in
2a, besides its forms: the slice itself, reads and lengths through a slice and `toArray(s)` each
take a typed form or a rule's case with its evaluation, faults and sized rules, and each takes its
inference, as in steps 2b to 4. The lowering copies a slice for `toArray(s)` with a recursive Core
helper over its indices, as `OrderedMapping`'s lookup is. So it splits into 6a to 6h, each within
the cap, whose estimates add up to that measure.

6f split as 2b-i did: the slices first took their own arm in inference, which still rejects them, in
a commit that only renumbers the cases of the proofs by functional induction on `inferExprFuel`
(6f-i): the arm is case 23, so every later case moves up by one, and the four proofs that name the
rejecting arms name it too. 6f-ii then gives the arm its typing. The totals gain 6f-i's estimate and
one commit. 6g split before its code, since its read and lengths change the existing arms' proofs
while `toArray(s)` takes a new call: 6g-i, the reads and lengths through a slice, and 6g-ii,
`toArray(s)`; the totals take the two estimates for 6g's and one commit.

Step 7 was one row of 30–45 files, +600–900/−100–250, until its first measure: about 151 to 194 file
changes, +3,250 to 5,000/−80 to 270. The memref is a new type and a new value, as the slice was in
6a and 6b, besides its forms: `lidx(a, i)`, `CanStore.load(r)` and `CanStore.store(r, v)` each take
a typed form with its evaluation, faults and sized rules, and each takes its inference, as in step
6. `lidx(a, i)` is a compiler call with no qualifier, as `toArray(s)` is, whose index waits for
finalization, as a read's does. `CanStore.load` and `CanStore.store` are qualified compiler calls,
as `Length.length` is, and the store unifies its value's type with the element type, as a slice's
bounds unify with `uint256`. So it splits into 7a to 7f, each within the cap, whose estimates add up
to that measure. 7e splits before its code into 7e-i, the load, and 7e-ii, the store, since the
store's unification reaches every proof the load's call does.

## Generators, corpora and the smoke

- **No generated case changes.** No step changes `Solcore/Synthesis`, a corpus, a fixture or a
  generated case. The generators print sources for the pinned compiler and compare its paths with
  original Core references, and Lean's native compiler takes part in neither.
- **The gate's 31 corpus runs** re-emit the same sources and are unchanged. Four of them concern
  memory: the memory-value, memory-call, memory-array and array ABI validators in
  `Tests/scripts`.
- **The smoke and RustParity.** The smoke's nine runs are unchanged, among them memory-fixed-o2,
  abi-fixed-yul, memory-random-o0, abi-random-o2 and fuzz-o0. RustParity's 31 cases contain no
  array, so they are unchanged too.
- **The source-to-Rust harnesses** compare Core references with the Rust paths and are unchanged.
- **Lean tests.** The existing tests that change in step 1a are those that state the type parser's
  exact result: a type followed by another token gains the premise that the token is not `[`, and a
  dispatch test states the base form's dispatch. Upstream's snapshot
  `crates/uitest/tests/fixtures/parse/struct_field_missing_semicolon/diagnostics.snap` gained `[`
  in its expected tokens. Lean's expected tokens after a type do not change, since Lean reports
  only the failing parser's own expectation. In step 1b-ii, three atom tests change: the name
  branch leaves the branches that ignore both child parsers, since `new T[](n)` reads its length
  with the nested one, and two names' dispatch traces gain the proof that no head `new T[](`
  starts. In step 1c-i, three trace tests' proofs wrap their index in the bracket contents' index
  form, and no test's statement changes. In step 1c-ii-b, `[]` is `a[]` whatever an index child
  would do, so three theorems about a child that does not advance state the empty index and its
  error, and the other index traces gain the bound's premises. Everything else is new tests.

## Open decisions

Each decision lists its options, the recommendation, upstream's code and the statements each option
changes. The statements are README and its Proof status, the names the guides cite, and
core-lowering's table of [definitions and theorems you build on](../guide/core-lowering.md#definitions-and-theorems-you-build-on).

On 2026-11-13, decisions 1, 2, 4, 5 and 6 were made as recommended, under the delegation. Decision
3, the one choice that changes a result upstream gives for a program it accepts, was made by the
user on 2026-11-17, as recommended.

### 1. How the source semantics holds arrays

- **Decided: (a)**, on 2026-11-13.
- **(a) Recommended: objects in the heap.** Array objects live in `Dynamic.Heap` beside the
  cells. An array value is a reference that carries its element type, and `Dynamic.HeapWellTyped`
  covers the objects.
- **(b) Byte memory.** The source state holds std's layout, and an array value is its address.
- **Upstream.** `std.sol:1229-1244`, `:1371-1382`, `:3100-3119`.
- **Statements under (a).**
  - These named definitions gain forms or a field: `Dynamic.Value`, `Dynamic.ValueHasType`,
    `Dynamic.Heap`, `Dynamic.HeapWellTyped`, `Dynamic.Heap.Allocates` and
    `Dynamic.Heap.AllocatesCopy`, which keep the store. They are named in
    [source-semantics.md](../guide/source-semantics.md#dynamic-semantics).
  - As built in step 2a-ii, the objects are heap cells, so only `Dynamic.Value` and
    `Dynamic.ValueHasType` gain forms, and the other four keep their text
    ([Source semantics](#source-semantics)).
  - As built in step 2b-i-b, the two whole-language theorems reach `new`. The two staged ones keep
    their text but do not, since the staged traces take no array form (decision 6).
  - These theorems keep their text and come to cover arrays: `Dynamic.WholeLanguagePreservation`,
    `ProgramWellFormed.wholeLanguagePreservation`,
    `Staging.Recursive.SelectedPreservation.expression` and
    `Staging.Recursive.FaultPreservation.expression`.
  - README's Proof status sentence on the source semantics' type preservation stays true.
  - Nothing in the build-on table changes.
- **Statements under (b).** `Dynamic.ValueHasType` and `Dynamic.HeapWellTyped` take the memory, so
  every cited statement that uses them changes its text, and preservation needs typed regions of
  memory.

### 2. How the lowering stores arrays, and when `new` panics with `0x41`

- **Decided: (a)**, on 2026-11-13. The roadmap's "Lowering: std's layout" changes with it.
- **(a) Recommended: one Core cell per array.** The cell holds the length, the default element and
  an `OrderedMapping` of elements, and is referenced by `cellRef`. `0x41` comes exactly when
  `n ≥ 2^251 − 1`. There is no free pointer.
- **(b) std's layout.** All arrays share one Core memory cell (`memoryType`), with a free pointer
  that starts at `0x80`. Both of std's checks apply, so `0x41` matches Yul exactly.
- **(c) Cells and a counter.** As (a), plus a free-pointer counter in the source state and in Core,
  for both checks without the layout.
- **Upstream.** `std.sol:1331-1340` and `:1400-1441`. In the probe, the free pointer at entry is
  896 on O0, 352 on O2 and 128 on Yul.
- **Statements under (a).** None of the cited ones. The cells are the ones Core already allocates.
- **Statements under (b) and (c).** Every function that allocates needs a memory or counter cell,
  as an administrative binder or a global. `DataHeap.EnvRepresents` and the slot arithmetic behind
  `CellAwareInvocationAcceptedFlow.body_preserves` read those binders. If the cell were threaded
  through every function, those build-on statements could change.

### 3. Compound assignment to an element

- **Decided: (a)**, on 2026-11-17, by the user: "一回だけ評価する。" ("evaluate it once"). Step 5b
  follows it; step 5a, plain element writes, did not wait for it.
  - Under either answer, the place is resolved and its current value read before the right side,
    then the write, as Lean's places do today. Under (a), only the second evaluation of the base
    and the index differs from upstream.
  - The main checkout's `questions.md` records the double evaluation (2026-11-13), and since
    2026-11-17 as the upstream bug candidate Q015, with this decision. It cites the comment in
    `crates/parser/src/parse/stmt.rs:49-80`, which says the rewrite is deliberate.
- **(a) Recommended: one evaluation of the place**, as row 1's compound assignments do.
- **(b) Upstream's rewrite** to `a[i] = a[i] op v`.
- **Upstream.** `crates/parser/src/parse/stmt.rs:49-80`, and the probe's 205 against 107.
- **Statements under (a).** None beyond the step's own place rules.
- **Statements under (b).** The compound rules of every place would change: locals and mappings
  too, to stay consistent. That reaches the cited `Dynamic.CompoundAssignmentApplies`,
  `CompatibleBareAssignment.of_lower` and `inferAssignedValueFuel_success_sound`, and reverses row
  1's decision.

### 4. What row 4's Lean side covers

- **Decided: (a)**, on 2026-11-13. Storage arrays, calldata arrays and `T[]` in the ABI wait for
  the native contract storage and calldata ABI, which are not scheduled.
- **(a) Recommended: memory arrays in functions.** The types, `new`, literals, reads, writes, the
  lengths, slices of arrays and slices, `toArray` and `memref`: steps 1 to 8.
- **(b) Without `memref`.** Step 7 goes, and bump(r) and bumpElement(v) are not ported.
- **(c) With storage arrays, calldata arrays and `T[]` in the ABI.** These need the native
  pipeline's contract storage and calldata ABI, which are units of their own and come before any
  array work.
- **Statements.** None. The options differ in size only.

### 5. Arrays at the public API

- **Decided: (a)**, on 2026-11-13.
- **(a) Recommended.** A root whose signature mentions an array or a slice is rejected.
- **(b) A new public value form**, a list of elements, for array arguments and results.
- **Upstream.** The ABI of `T[]`, above.
- **Statements under (a).** None.
- **Statements under (b).** The public values of `SourceCoreExecution`, described in README's
  [Using the frontend](../../README.md#using-the-frontend) and in the runtime API overview.

### 6. Meaning proofs

- **Decided: (a)**, on 2026-11-13. The proofs for arrays become a later unit.
- **(a) Recommended: compiled, outside the meaning proofs in row 4**, as row 1's conversions were.
  A later unit relates array objects to their Core cells.
- **(b) Prove the lowering of arrays in row 4.**
- **Statements under (a).** Nothing in README, its Proof status or the build-on table changes.
  [What remains](../guide/core-lowering.md#what-remains) in core-lowering.md gains arrays.
- **Statements under (b).** These are build-on table changes:
  - `GenericHeap.HeapRepresents` gains the array objects;
  - the premises of `CellAwareInvocationAcceptedFlow.body_preserves` and `body_reflects`
    (`Covered`, `Expressions`) gain the array forms.

## Consequences for existing programs

- **`new` stays an identifier** unless an array type and a parenthesized length follow it.
- **No program changes its meaning.** No source that Lean's own tests compile writes a type
  followed by `[`. The `T[]` sources in `Solcore/Test/Synthesis` are printed for the pinned driver,
  and Lean's parser never reads them.
- **Array literals**, rejected today, become accepted in step 4. No existing test expects their
  rejection.
- **`unsupportedExpression "field"`** stays the answer for other names after a dot. The tests that
  expect it use `provider.hidden`, `WordBox.Wrap` and `provider.Box.Wrap`.
