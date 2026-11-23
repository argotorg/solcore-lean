# Memory arrays and slices

Updated: 2026-11-18.

Row 4 of the roadmap's
[upstream table](next-implementation-roadmap.md#following-upstreams-semantics-the-next-units) brings
solcore-rs #145 to Lean's source language: memory arrays `T[]`, `new T[](n)`, element reads and
writes, `a.length`, read-only slices, and Solidity's panic codes `0x32`, `0x31` and `0x41`. #145 is
the pin itself: `e2eef194` is its merge.

**Status.** Row 4 is done for memory arrays in functions. The types, `new`, literals, reads, element
writes and compound assignments, lengths, slices, `toArray(s)`, `memref<T>`, `lidx(a, i)`,
`CanStore.load(r)` and `CanStore.store(r, v)` parse, are typed, have their source semantics and
compile to Core through the compatible profile, outside the meaning proofs
([decision 6](#6-meaning-proofs)). Storage and calldata arrays, `T[]` in the ABI and the meaning
proofs remain ([what remains](#what-remains)).

The generator profiles `runtime-memory-arrays` and `runtime-array-abi` compare the pinned compiler's
paths with Core references that hold an array as a length cell and element cells
([definitions](../../scripts/SEMANTIC_DIFFERENTIAL.md#compare-solcore-memory-arrays-and-their-abi)).
Lean's native compiler takes part in neither. This note covers the Lean side: the parser, typing,
the source semantics and the lowering to Core.

## Upstream at `e2eef194`

Paths are relative to the pinned checkout, and `std.sol` is `std/std.sol`. Some facts come from a
probe of the pinned driver, whose inputs and outputs are kept in
`.upstream/lane-d-unit3-memory-arrays/`.

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

The constructor payload and struct field rows come from the probe.

- **Elements.** Every memory array operation requires `t: Typedef<word>`: `new`
  (`crates/hir-ty/src/infer/expr.rs:344-369`), reads and writes
  (`crates/hir-ty/src/infer/storage.rs:359-370`, `:128-150`) and std's instances (`std.sol:3081`,
  `:3115`). Among the types Lean has, these are `word`, the twelve integer types and memory arrays.
  The pinned driver rejects `bool`, tuple, `()`, enum and closure elements with SC0207. Generic
  code must state the bound (`where t: Typedef<word>`).
- **`new T[](n)`** has the type `T[]`. The comment at `crates/hir-ty/src/infer/expr.rs:344-345`
  says its length is a `uint256`, but the checker does not enforce this: a `word` length passes the
  checker and fails in specialization (SC0405), and a `let`-bound literal length is reported
  ambiguous (SC0299).
- **Literals** `[e1, …, en]` unify their elements (`crates/hir-ty/src/infer/expr.rs:329-342`).
  Open literal elements take their type from their uses, and otherwise `uint256`. `[]` takes the
  expected type.
- **Reads** (`crates/hir-ty/src/infer/expr.rs:82-124`). A memory array or a slice takes an index of
  any word-sized type: `word` or one of the twelve. A calldata array takes its own instance. Any
  other user type is indexed through its own `RValueIdxAccess` instance
  (`crates/hir-ty/src/infer/storage.rs:422-443`).
- **Writes** `a[i] = v` give `v` the element type (`crates/hir-ty/src/infer/storage.rs:128-150`).
  Slices and calldata arrays are read-only: "expected assignable index (array slices are
  read-only)" (`:152-203`).
- **Slices** take `uint256` bounds and a base with a `Length` instance. They have the type
  `arraySlice<B>`, nested for a slice of a slice (`crates/hir-ty/src/infer/storage.rs:205-256`).
- **`a.length`** is `Length.length(a)`, a `uint256`, unless the value has a field named `length`
  (`crates/hir-ty/src/infer/storage.rs:384-420`, `crates/hir-ty/src/infer/expr.rs:160-174`).
  `a.length()` works too.
- **Rejected:** `push` and `pop` on a memory array, with the hint "memory arrays have a fixed
  length" (`crates/hir-ty/src/infer/diagnostics.rs:662-667`); `==` on arrays, since they have no
  `Eq`; an assignment to `a.length`.

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
- **Allocation.** The free memory pointer is at `0x40` (`std.sol:1316-1329`).
  `allocate_memory(size)` panics with `0x41` when the end wraps (`:1331-1340`).
  `allocate_zeroed_memory(size)` clears the region with `calldatacopy` (`:1342-1353`).
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

### The fixtures

The last column lists the functions that Lean's native pipeline runs, as top-level functions: they
need no contract storage and no ABI.

| Fixture | Uses | Functions Lean runs |
| --- | --- | --- |
| `array-syntax` | `T[]` parameters, results and locals, literals and nested literals, `.length` of a call's result and of `new`; storage `uint256[]` and `uint256[][]` fields with `push`, `setLength` and `.length`; `mapping(address => uint256[])`; a struct field named `length` | sumAll(xs), pair(a, b), local(a, b), returned(a, b), nested(), callResultLength(n) |
| `mem-array` | `new` with zeroed elements, writes and reads, `0x32`, `0x41`, loops, a compound element write, rows of `new T[][]`, aliasing, `memref` through `lidx` and `CanStore`, `Length.length(m)` | all, bump(r) and bumpElement(v) through `memref` |
| `array-slice` | the four slice forms of a call's result, a slice's `.length` and reads, slices of slices, bound panics, `toArray`, aliasing through a view, a conditional bound, slices of a storage array | build() and every public function but storageSlice(i) and storageSliceLength() |
| `calldata-slice` | slices of `calldata<uint256[]>` parameters through the public ABI | none |
| `memory-array-abi` | `T[]` public parameters and results, `address[]` with a dirty address, a `uint256[][]` result, `toArray(xs[1:3])` | ret(n), sum(xs), echo(xs), grid(n) and slices(xs), behind word wrappers |
| `user-collection-index` | a program's own `RValueIdxAccess` instance, `Typedef.rep(j)` at a generic index, `out_of_bounds()` | none |
| `memory-allocation-bounds` | `allocateDynamicArray(prx, n)`, `mload`, `get_free_memory()`, an address as a word, `0x41` | none |
| `allocator-bounds` | `get_free_memory()`, `set_free_memory(p)`, `allocate_memory(size)`, `0x41` | none |
| `abi-sum-padding` | `abi_encode(v)` of sums into dirty scratch memory, `mstore`, `mload`; #145 does not change it | none |
| `array-ops` | a storage `array<uint256>` with `ArrayPush.push`, `Array.pop` (`0x31`), `Length.length` and `Array.setLength` | none |

The Hull importer runs all ten fixtures on Core, through the pinned contract inventory in
`scripts/rust-method-parity.json` and `scripts/rust-scenario-parity.json`.

## Semantics in Lean

Memory arrays are builtins, as the twelve integer types are. They take upstream's typing and std's
checks. The source semantics holds arrays as objects in its heap, and an array value is a reference
to one. The lowering gives each array a Core cell. Lean ports what its native pipeline can express:
memory arrays inside functions ([decision 4](#4-what-row-4s-lean-side-covers)). Storage arrays,
calldata arrays, the ABI and raw memory wait for the native pipeline's contracts and ABI.

Core needs nothing for row 4: it already has the cells, cell references and data types that the
lowering uses, so no Core primitive, host function or typing rule is added. The Hull importer
needs nothing either.

### Syntax

- `TypeExprValue` has the array form: `T[]` suffixes on any type, folded left to right. A size is
  rejected with upstream's message.
- `ExprValue` has `new T[](n)` and the four slice forms. `new` allocates only before an array
  type and a parenthesized length. Otherwise it stays an identifier, as upstream's contextual
  keyword does, except that after `new T[](` the length and the `)` are required (difference 12).
  `a[]` is rejected.
- `e.length` and `e.length()` parse as a field and a call of a field.
- The grammar and the parser's correctness proofs cover the new forms. In inference, `new T[](n)`
  and the slices each have their own arm of `inferExprFuel`.

### Typing

- **Types.** `BuiltinType` has the memory array `T[]`, the slice `arraySlice<B>` and the memref
  `memref<T>`, std's checked reference to one element of a memory array. `arraySlice<B>` and
  `memref<T>` resolve once aliases are expanded, as intrinsics that a user type of the same name
  hides, as `integer` is (`resolveBuiltinFallback`), with one argument (`typeArityMismatch`
  otherwise).
- **Formation.** `T[]` is well formed when `T` is `word`, one of the twelve types or a memory
  array: the types with `Typedef<word>` upstream that Lean has. `Ty.arraysWellFormed` admits
  `arraySlice<B>` when `B` is a memory array or a slice (`Ty.arraySliceBaseAllowed`), and
  `memref<T>` when a memory array holds `T` (`Ty.arrayElementAllowed`). `Ty.containsArray` counts
  all three, so a mapping that holds one is rejected with `unsupportedArrayType`.
  `Ty.arrayElementAllowed` admits no slice and no memref, so no array holds one (differences 17
  and 21). Elaboration and the strict catalog reject slice and memref types, and the compatible
  catalog projects them ([lowering](#lowering)).
- **`new T[](n)`** has the type `T[]`. Its length has the type `uint256`, and an open literal
  length defaults to it.
- **Literals.** The elements take one type `T`, and the literal has the type `T[]`. Inference infers
  the elements with no expected type, as a tuple's, and unifies their types with one fresh element
  type, as upstream's `infer_array_expr` does. So `[]` takes its element type from the expected type
  or from the elements beside it, as in `[[a], []]`. Finalization defaults an open literal element
  to `uint256` (`operatorMentions`) and rejects an element type a memory array cannot hold with
  `operatorNotSupported "Typedef"` (`validateArrayLiteral`), as upstream's `bool: Typedef<word>`
  fails. An unannotated `let m = [];` is rejected, used or not (difference 8).
- **Reads and writes.** Inference decides `a[i]` on its base's resolved type.
  - A read: on a memory array or a slice, `a[i]` is a read at the element type of the array or of
    the slice's base (`Ty.viewElement?`). On a mapping, or on a base whose type is still open
    there, it keeps the mapping rule (difference 15).
  - A place: on a memory array, `a[i]` is an element place at the element type, so `a[i][j] = v`
    takes two element projections. On any other base, a slice included, the place keeps the mapping
    rule, so a write through a slice is rejected, as upstream's slices have no assignable index.
  - The index is inferred on its own. Finalization defaults an open literal index to `uint256` and
    rejects an index type other than `word` and the twelve with `operatorNotSupported "Typedef"`,
    for reads (`validateArrayIndex`) and writes (`validatePlaceElements`) alike, as upstream's
    `bool: Typedef<word>` fails. The element place's static rule takes no index kind: its run
    faults on an index that is not a word.
  - Plain writes, compound assignments, their unchecked forms and in-place `~` take the element
    type, with row 1's rules for each type. So `rows[0] += xs` or `rows[0] ~=;` on a row is
    rejected by unifying the row with `word`, as a compound assignment or an in-place `~` on any
    array is.
  - A write's base is a place rooted at a local (difference 16).
- **Slices** take `uint256` bounds and a base whose resolved type is a memory array or a slice
  there, and have the type `arraySlice<B>` (`ExpressionForm.arraySlice`). Another base is rejected
  with `unsupportedExpression "slice"` (difference 18). The bounds' types unify with `uint256`, so
  an open literal bound takes `uint256` and a bound of another type is rejected.
- **Lengths.** `a.length`, `a.length()` and `Length.length(a)` on an array or a slice have the type
  `uint256`. They are recorded as the length's own typed form, whose evaluation reads the array's
  cell, rather than as a builtin function, whose evaluation reads no heap
  (`Dynamic.BuiltinApplies`). `Length.length` is a builtin qualified call when no namespace or local
  is named `Length`, as `Typedef.abs` is (`typedefCall?`). `a.length` is a field that names no
  constructor, and `a.length()` a call of it with no arguments, recorded as a group over that
  field. Other names after a dot still give `unsupportedExpression "field"`. The base must be an
  array or a slice there: `arrayLengthOf` reads `Ty.viewElement?` (difference 14).
- **Rejected.** `Typedef` at an array type, `==` on arrays, `push` and `pop`, and assignment to a
  length. A mapping key or value of an array type is rejected too: upstream's meaning there is a
  storage array. A contract field of an array type parses and, like every contract member, is not
  typed.

**Compiler calls.** `toArray(s)`, `lidx(a, i)`, `CanStore.load(r)` and `CanStore.store(r, v)` are
each recorded as their own typed form, and only a call names them (differences 20 and 22 to 24).
Each rejects its slice, array or memref when that operand's type is still open there (differences
19 and 22 to 24).

| Call | Found when | Its operands, once inferred | Typed form, at |
| --- | --- | --- | --- |
| `toArray(s)` | no source function, local or compiler function has the name | a slice, whose base's view gives the copy's element | `ExpressionForm.toArray`, an array of that element |
| `lidx(a, i)` | the same holds for `lidx` | a memory array, and an index that waits for finalization as a read's, an open literal taking `uint256` | `ExpressionForm.elementRef`, the memref of the array's element |
| `CanStore.load(r)` | no namespace or local is named `CanStore` | a memref | `ExpressionForm.memrefLoad`, the memref's element |
| `CanStore.store(r, v)` | the same holds | a memref, and a value whose type unifies with the memref's element | `ExpressionForm.memrefStore`, `()` |

So `toArray(m[1:3])` has the type `uint256[]` where `m` has, `lidx(m, 1)`'s index has the type
`uint256` (difference 25), and `CanStore.store(r, 7)` stores a `uint8` where `r` has the type
`memref<uint8>`.

### Source semantics

- **Values.** `Dynamic.Value` has four forms for arrays:
  - an array reference, which carries its element type and the location of its object, as Core's
    `cellRef` does;
  - an array object, which holds the elements and lives only in its heap cell;
  - a slice (`Dynamic.Value.arraySlice`), which holds its base value, its start and its length;
  - a memref (`Dynamic.Value.memref`), which holds its array's element type, the location of its
    cell and its position.
- **Heap.** An array object is a heap cell, whose type is `arrayObject T`, a builtin type that no
  source type names. An allocation appends a cell, so `Dynamic.Heap`, `Dynamic.Heap.Allocates` and
  `Dynamic.Heap.AllocatesCopy` keep their text. Objects never move, grow or shrink, so a reference
  and a memref stay valid.
- **Rules.** Each rule comes with its fault rules and its sized copies, as row 1's rules do. Every
  form faults with its operands' faults. A read, a slice, `lidx(a, i)` and `new T[](n)` also fault
  on an index, a bound or a length that is not a word. The staged traces that the source-to-Core
  theorems are stated over (`Staging.Recursive.Expression`) mirror them: `arrayResult` evaluates
  the children and then `ArrayOutcome`, which mirrors each rule after them, and `arrayFault`
  takes the children's first fault.

| Form | Typed form | Evaluation | Panics |
| --- | --- | --- | --- |
| `new T[](n)` | its own | allocates an object of `n` zero elements; for an array element type, `n` references to one fresh empty array, as std's `0x60` is | `0x41` when `n ≥ 2^251 − 1` |
| `[e₀, …, eₙ₋₁]` | `ExpressionForm.arrayLiteral` | evaluates the elements from left to right, then allocates the cell holding them | none |
| `a[i]` | `ExpressionForm.arrayIndex` | takes the index as a word at `word` or one of the twelve types (`ArrayIndexType`), then the element through `ViewReads`, which checks a slice's length and reads its base at the slice's start plus the position, down to the array's cell | `0x32` outside a view's bounds, the slice's or its base's (`arrayIndexOutOfBounds`, `ViewOutOfBounds`) |
| lengths | its own | reads `ViewLength`: an array cell's element count, or a slice's own length | none |
| `a[s:e]`, `a[s:]`, `a[:e]`, `a[:]` | `ExpressionForm.arraySlice` | evaluates the base, then its present bounds from left to right, each a `uint256` word; fills an absent start with 0 and an absent stop with the base's length (`SliceBounds`), as std's `sliceFrom`, `sliceTo` and `sliceAll` do; holds the base from `s` on for `e − s` elements | `0x32` unless `s ≤ e ≤ length` (`arraySliceOutOfBounds`) |
| `toArray(s)` | `ExpressionForm.toArray` | evaluates the slice, reads its elements in order (`ViewCopies`), then allocates a fresh array's cell holding them | none: a slice's positions lie within its base's bounds once it is made |
| `lidx(a, i)` | `ExpressionForm.elementRef` | takes its index as a read does, evaluates the array, then the index, and below the array's length (`ViewLength`) gives a memref to the element at the index | `0x32` from the length on (`elementRefOutOfBounds`), as std's `LValueIdxAccess` does |
| `CanStore.load(r)` | `ExpressionForm.memrefLoad` | evaluates the memref and reads the element at its position in its array's cell (`ViewReads`) | none: a memref's position lies within its array's bounds once it is made |
| `CanStore.store(r, v)` | `ExpressionForm.memrefStore` | evaluates the memref, then the value; the element at the memref's position takes the value (`ValuesReplaceAt`), as a plain element write's place does; its value is `()` | none, as for the load |

- A literal and `toArray(s)` allocate after their elements. No element can observe the fresh cell,
  so where the allocation falls changes no result. Unlike `new`'s, a literal's static rule checks
  no element type; inference's finalization does.
- The read's and the length's static rules take a base whose type is a memory array or a slice,
  with its element type (`ViewElement`). `toArray(s)`'s result is an array of the slice's element
  type (`ViewElement`).
- **Element places.** An element place `a[i]` is a place whose last projection is an element
  (`PlaceProjection.element`). Its leading place resolves first, to an array reference, then the
  index, and the place resolves to the array object's own cell with the element's position as its
  one evaluated projection (`SourcePlaceResolves.element`). So the place is evaluated once and
  checked before the right side, as `lidx(a, i)` does.
  - A write replaces the element through `ProjectionsUpdate`'s element case, and
    `ResolvedPlaceWrites` keeps its text. The compound rules take any place, so a compound
    assignment to an element evaluates its place once
    ([decision 3](#3-compound-assignment-to-an-element)).
  - Before the right side, the place faults with its leading place's fault, the index's, an index
    that is not a word, `0x32` from the length on, or `uninitializedLocation` when its leading is a
    local not yet initialized, as reading that local does.
  - The staged traces stage an element place with `Staging.Recursive.ElementTarget`: the root
    local, then each element, with the place's faults. `StatementsIn` and `ForItems` write
    through it (`assignElement`, `bitNotElement`, `elementAssignment`, `elementBitNot`).
- **Preservation.**
  - A reference has the type `T[]` when the cell it names has the type `arrayObject T`, as Core's
    runtime typing reads a `cellRef`'s cell in its world, and an object's elements each have its
    element type. A later heap keeps every cell's type, so a reference keeps its type, and
    `Dynamic.HeapWellTyped` keeps its text.
  - A slice has the type `arraySlice<B>` when its base has the type `B`, a memory array or a slice
    (`ValueHasType.arraySlice`). Its typing reads no bound: a slice is made only once its bounds are
    checked, and a read through it checks them again, so a later heap keeps its type too.
  - A memref has the type `memref<T>` when the cell it names has the type `arrayObject T`, as a
    reference does (`ValueHasType.memref`), so `lidx(a, i)`'s memref has its array's element type
    (`ValueHasType.memref_of_arrayRef`). A load has its memref's element type, read through the
    array's reference (`ValueHasType.arrayRef_of_memref`). A store keeps the heap well typed: the
    cell's object keeps its type (`ValueHasType.arrayElementWrite`).
- **Panics** reuse `SemanticFault.panic`.

### Lowering

The public compiler lowers through the compatible profile. Its catalog
(`SourceCoreCompatibleCatalog`) gives each type its Core form and registers what it holds: `T[]`'s
element mapping as `mapping(word => T)`, a slice's base `B` and a memref's `T[]` mapping. Its data
lowering (`SourceCoreCompatibleDataExpressions`) lowers the forms. The projection tests an
application's runtime head, so that a type and its runtime type project alike. The strict
representation's catalog and direct linking reject `T[]`. Core does not change.

| Type | Core form |
| --- | --- |
| `T[]` | a cell of a word, the element's Core type and the element mapping: the length, the default element and the present elements in an `OrderedMapping` from index to element; the source value is the cell's `cellRef` |
| `arraySlice<B>` | the product of `B`'s Core type and two words: the base, the start and the length |
| `memref<T>` | the product of `T[]`'s Core type and a word: the array and the position |

- **Arrays.** Nested arrays hold `cellRef`s. The default element is zero, or for an array element
  type the shared empty array, one fresh per `new`. `new` allocates the cell with no entries, so an
  absent element reads as the default.
- **Reads** (`SourceCoreDataExpressions.arrayIndex`) evaluate the array, then the index, panic with
  `0x32` from the cell's length on, and otherwise look the index up in the cell's mapping, an absent
  element reading as the cell's default element. The index's Core value is its word, so a negative
  signed index panics, as upstream's `Typedef.rep(j)` gives it a word from 2^255 on.
- **Literals** (`SourceCoreDataExpressions.arrayLiteral`) evaluate the elements from left to right,
  packed as a call's arguments are, and then allocate the cell of the length `n`, the default
  element and the element at each index below `n`, as the source semantics evaluates the elements
  before it allocates.
- **Element writes.** The place lowering, `SourceCoreCompatibleDataPlaces.lower`, sends every write
  to an element, plain, compound, unchecked or an in-place `~`, to
  `SourceCoreCompatibleDataPlaces.lowerElements` (`takesElement`), and every other place keeps its
  route (`lowerRoute`).
  - The place is a root local followed by elements. The lowering reads the root's array, failing
    with the place's reason when the root is not yet initialized, then each index, panicking with
    `0x32` from its array's length on, and for an inner index the next array, as a read does. Only
    then does it evaluate the right side. That is the source semantics' order and upstream's
    `lidx(a[i], j)`. The route's `execute` evaluates every key first, so it could not be reused.
  - A plain write evaluates the right side, and the last array's cell takes the value at its index
    (`arrayElementWrite`).
  - A compound assignment or an in-place `~` reads the element present at the index or the array's
    default element, as a read does, then evaluates the right side. The last array's cell takes
    `modified`'s leaf after `guard`'s check (`elementStore`), with the route's modifier, wrap and
    checks (`placeModifier`, `placeWrap`), as its `execute` gives a local or a mapping. So the
    place is evaluated once, its element is read before the right side, and `Panic(0x11)` and
    `Panic(0x12)` come after it, as in the source semantics.
  - The compatible fault-site pass reserves the write's place reason, as a projected route's
    (`SourceCoreCompatibleDataPlaceFaultSites.prepare`).
  - The place lowering's receipt (`CompatiblePlaceCompilerCertificates.generated_of_lower`) takes
    the place's element-freeness (`takesElement_of_free`). The statement recognizers'
    value-assignment cases and the heads that reach the receipt take it as a field or a
    hypothesis. So do the projected in-place `~` receipts, heads and certificates and the
    recognizers' projected in-place `~` cases, from their mapping route (`Route.elementFree`).
- **Slices.** The data lowering reads a view's shape from its Core type
  (`SourceCoreDataExpressions.viewShape?`): a memory array's cell inside some slices.
  - A slice evaluates its base, then its present bounds from left to right, fills an absent start
    with 0 and an absent stop with the base's length, and panics with `0x32` unless
    `s ≤ e ≤ length`. Otherwise it holds the base, `s` and `e − s` (`arraySlice`). A slice's length
    is its own (`sliceLength`).
  - A read through a slice panics with `0x32` from the slice's length on, then reads the base at the
    slice's start plus the index, down to the array's cell (`viewIndex`, `viewRead`), as the source
    semantics' `ViewReads` does.
  - `toArray(s)` evaluates the slice and reads its elements from position 0 on with a recursive Core
    helper, a self closure in a cell, as `OrderedMapping`'s lookup is (`sliceCopyBody`). It then
    allocates the cell of the slice's length, the default element of the array under it and those
    elements (`sliceCopy`), as the source semantics' `ViewCopies` and its allocation do.
- **Memrefs.**
  - `lidx(a, i)` evaluates the array, then the index, panics with `0x32` from the array's length
    on, and otherwise holds the array and the index (`SourceCoreDataExpressions.elementRef`), as
    std's `LValueIdxAccess` does.
  - `CanStore.load(r)` evaluates the memref and reads the element at its position as a read does
    (`memrefLoad`). A memref's position is below its array's length, which no write changes, so the
    load's check passes.
  - `CanStore.store(r, v)` evaluates the memref, then the value, and the array's cell takes the
    value at the memref's position, keeping its length and default element, as an element write's
    last array does (`memrefStore`).
- **The proofs.** Arrays stay outside `StaticProfile` and the proved subset, as row 1's conversions
  did. The meaning proofs and their statements do not change.

### Tests

A root whose signature mentions an array or a slice is rejected
([decision 5](#5-arrays-at-the-public-api)), so tests reach arrays through functions over words,
as row 1's fixture ports do.

- `runUpstreamArrayFixtures` runs the functions in the fixture table above, in one workspace, as
  upstream wrote them. It runs every case the four fixtures give, with their values and panic
  codes, then the values that earlier tests checked on the same functions. mem-array's `bump(r)`
  and `bumpElement(v)` run with the contract's method as a function, so `bumpElement(7) -> 8` is
  checked through `bump`, which loads and stores through `lidx`'s memref.
- memory-array-abi's `ret`, `sum`, `echo`, `grid` and `slices` run behind word wrappers, since a
  root's signature takes no array. A wrapper changes only how an array arrives, a literal of word
  arguments instead of the ABI's decoding, and how one leaves, read back by index or length instead
  of ABI-encoded. So `ret(3) -> [0,2,4]` is checked as 0, 2 and 4 at indexes 0 to 2 and length 3,
  and `slices([10,20,30,40]) -> [20,30]` as 20 at index 0, 30 at 1 and `0x32` at 2.
- `runArrayElementCases` holds Lean's own array cases. Among them, `compoundTwice()` gives 105,
  where upstream gives 205 (difference 1), and `plainOnce()` gives 107, as upstream does.
- `runLiteralElementRefs` runs `lidx` at a literal index through a `let`, a call, `CanStore.store`
  and `CanStore.load`, and past the array's end with `0x32`.

## Decisions

Each decision gives its options, the one taken, upstream's code and the statements each option
changes. The statements are README and its Proof status, the names the guides cite, and
core-lowering's [build-on table](../guide/core-lowering.md#definitions-and-theorems-you-build-on).
Decisions 1, 2, 4, 5 and 6 were made under the delegation, each as recommended. Decision 3, which
changes what programs that upstream accepts compute, was made by the user, as recommended.
Decision 2 changes a result only for lengths just below 2^251 − 1 (difference 2).

### 1. How the source semantics holds arrays

- **Decided: objects in the heap.** Array objects live in `Dynamic.Heap` as cells beside the
  locals' cells. An array value is a reference that carries its element type, and
  `Dynamic.HeapWellTyped` covers the objects.
- **Other option: byte memory.** The source state would hold std's layout, and an array value
  would be its address.
- **Upstream.** `std.sol:1229-1244`, `:1371-1382`, `:3100-3119`.
- **Statements under the decision.**
  - Only `Dynamic.Value` and `Dynamic.ValueHasType` gain forms. `Dynamic.Heap`,
    `Dynamic.HeapWellTyped`, `Dynamic.Heap.Allocates` and `Dynamic.Heap.AllocatesCopy` keep their
    text ([source-semantics.md](../guide/source-semantics.md#dynamic-semantics) names them).
  - The whole-language theorems `Dynamic.WholeLanguagePreservation` and
    `ProgramWellFormed.wholeLanguagePreservation` keep their text and cover arrays. The staged ones
    reach the array forms and element writes: `Staging.Recursive.FaultPreservation.expression`
    keeps its text, and `Staging.Recursive.SelectedPreservation.expression` gains one clause,
    that a run which does not fault keeps every array object's length (`KeepsLengths`).
  - README's Proof status sentence on the source semantics' type preservation stays true, and
    nothing in the build-on table changes.
- **Statements under byte memory.** `Dynamic.ValueHasType` and `Dynamic.HeapWellTyped` would take
  the memory, so every cited statement that uses them would change its text, and preservation
  would need typed regions of memory.

### 2. How the lowering stores arrays, and when `new` panics with `0x41`

- **Decided: one Core cell per array.** The cell holds the length, the default element and an
  `OrderedMapping` of elements, and is referenced by `cellRef`. `0x41` comes exactly when
  `n ≥ 2^251 − 1`. There is no free pointer.
- **Other options.**
  - std's layout: all arrays share one Core memory cell of `memoryType`, the cell holding a
    `WordMapping` that is the Hull importer's and the generators' byte memory, with a free pointer
    that starts at `0x80`. Both of std's checks apply, so `0x41` matches Yul exactly.
  - Cells and a counter: one cell per array, plus a free-pointer counter in the source state and
    in Core, for both checks without the layout.
- **Upstream.** `std.sol:1331-1340` and `:1400-1441`. In the probe, the free pointer at entry is 896
  on O0, 352 on O2 and 128 on Yul.
- **Statements under the decision.** None of the cited ones: the cells are the ones Core already
  allocates.
- **Statements under the other options.** Every function that allocates would need a memory or
  counter cell, as an administrative binder or a global. `DataHeap.EnvRepresents` and the slot
  arithmetic behind `CellAwareInvocationAcceptedFlow.body_preserves` read those binders. If the
  cell were threaded through every function, those build-on statements could change.

### 3. Compound assignment to an element

- **Decided by the user: one evaluation of the place**, as row 1's compound assignments do. The
  user's answer was "一回だけ評価する。" ("evaluate it once").
- **Other option: upstream's rewrite** to `a[i] = a[i] op v`.
- **What differs.** Under either answer, the place is resolved and its current value read before the
  right side, then the write, as Lean's places do. Under one evaluation, only upstream's second
  evaluation of the base and the index differs: difference 1.
- **Upstream.** `crates/parser/src/parse/stmt.rs:49-80`, whose comment says the rewrite is
  deliberate, and the probe's 205 against 107. `questions.md` records the double evaluation as the
  upstream bug candidate Q015, with this decision.
- **Statements under the decision.** None beyond the place rules.
- **Statements under upstream's rewrite.** The compound rules of every place would change, locals
  and mappings too, to stay consistent. That reaches the cited `Dynamic.CompoundAssignmentApplies`,
  `CompatibleBareAssignment.of_lower` and `inferAssignedValueFuel_success_sound`, and reverses row
  1's decision.

### 4. What row 4's Lean side covers

- **Decided: memory arrays in functions.** The types, `new`, literals, reads, writes, the lengths,
  slices of arrays and slices, `toArray` and `memref`.
- **Other options.**
  - Without `memref`: bump(r) and bumpElement(v) would not be ported.
  - With storage arrays, calldata arrays and `T[]` in the ABI. These need the native pipeline's
    contract storage and calldata ABI, which are units of their own, come before any array work,
    and are not scheduled.
- **Statements.** None. The options differ in size only.

### 5. Arrays at the public API

- **Decided:** a root whose signature mentions an array or a slice is rejected.
- **Not enforced yet.** Such a root still compiles. The check is being added.
- **Other option: a new public value form**, a list of elements, for array arguments and results.
- **Upstream.** [The ABI of `T[]`](#abi).
- **Statements under the decision.** None.
- **Statements under the other option.** The public values of `SourceCoreExecution`, described in
  README's [Using the frontend](../../README.md#using-the-frontend) and in the
  [runtime API overview](core-runtime-unification.md#public-runtime-api).

### 6. Meaning proofs

- **Decided: compiled, outside the meaning proofs in row 4**, as row 1's conversions were. The
  proofs for arrays become a later unit, which relates array objects to their Core cells.
- **That unit is under way.** The staged traces have the array forms and the element writes, the
  selected preservation keeps every array object's length, and the whole-cell relation holds
  array objects through `CellModel.Array`.
  The unit takes a memref only as the operand of a load or a store, and `toArray` only of
  slices made where it is called: the Source has no rule for a load, a store or a copy out of
  bounds, and the bound of a stored memref or slice would be an invariant over the heap. The
  relation that gains the array objects is the whole-cell `GenericHeap.CellHeapRepresents`;
  `HeapRepresents`, `ordinaryHeap_iff` and `finiteHeap_iff` keep their text.
- **Other option: prove the lowering of arrays in row 4.**
- **Statements under the decision.** Nothing in README, its Proof status or the build-on table
  changes. [What remains](../guide/core-lowering.md#what-remains) in core-lowering.md has arrays.
- **Statements under the other option**, which bringing arrays into the meaning proofs would
  change. These are build-on table changes:
  - `GenericHeap.HeapRepresents` gains the array objects;
  - the premises of `CellAwareInvocationAcceptedFlow.body_preserves` and `body_reflects`
    (`Covered`, `Expressions`) gain the array forms.

## Differences from upstream that Lean would keep

1. **One evaluation of an element place in a compound assignment**
   ([decision 3](#3-compound-assignment-to-an-element)). `m[next(c)] += 5` runs `next` once, so the
   probe's 205 is 105 in Lean. This is row 1's rule for compound assignments
   ([row 1's compound assignments](integer-types-unchecked-shifts.md#row-1s-compound-assignments-checked-at-the-guard)).
2. **`0x41` only from the length check**
   ([decision 2](#2-how-the-lowering-stores-arrays-and-when-new-panics-with-0x41)).
   - For lengths just below 2^251 − 1, the pinned backends disagree with each other. Each panics
     where its own free pointer makes the end wrap, and halts otherwise. Lean allocates. The
     generators draw no length in that window: their `allocationLimit` is 2^251 − 1, and a drawn
     length is at most 7 or at least 2^255.
   - Lengths that exhaust EVM memory run out of gas there and allocate in Lean, whose Core does not
     meter gas.
3. **No addresses.** `Typedef.rep` and `Typedef.abs` at an array type, `memory<…>` and
   `DynArray<…>`, and std's allocation functions are rejected. So is an array used as an index,
   with `operatorNotSupported "Typedef"`. The pinned driver compiles `a[b]` with `b` an array and
   takes `b`'s address as the index, since its read takes any `i: Typedef<word>` (`std.sol:3115`),
   which `memory<t>` has (`std.sol:1229-1244`).
4. **`arraySlice<B>` is a type only.** A program cannot build or match a slice by hand, while
   upstream exports the constructor.
5. **`T[]` only where the native pipeline has a meaning for it.** Storage and calldata arrays,
   mappings of arrays and `T[]` in public signatures are rejected.
6. **Element types are checked where the type is formed.** `bool[]` is rejected even where upstream
   accepts it, which is until an operation requires `Typedef<word>`. Generic `t[]` is rejected,
   since Lean cannot write `where t: Typedef<word>`: row 1's gap for generic code over std's
   instances.
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
    statement fails. Where the same statement fails later, they differ: `return a[] + ;` gets
    upstream's error over the `[]`, and in Lean the `;` and then the `]`, as `return a[1] + ;`
    does, since Lean's recovery of a failed statement does not keep the `[]`'s error.
14. **A length needs its array known where the length is.** `Length.length(a)`, `a.length` and
    `a.length()` are rejected with `operatorNotSupported "Length"` when `a`'s type is still open
    there, as an open `Typedef` call is
    ([row 1's conversions](integer-types-unchecked-shifts.md#row-1s-conversions-a-word-becomes-a-value-only-when-canonical)).
    Only the array must be known, not its element: `arrayLengthOf` reads the resolved type's view
    (`Ty.viewElement?`). Upstream's `Length` constraint waits for later uses to fix the type.
15. **A read needs its array known where the read is.** `a[i]` on a base whose type is still open
    there takes the mapping rule, so a base that later turns out to be a memory array is rejected
    with a type mismatch. Upstream's `RValueIdxAccess` constraint waits for later uses to fix the
    type.
16. **An element write's base is a local, or an element of one.** Lean's assignment target is a
    place rooted at a local: an identifier, a group, or an index of a place. So `same(m)[1] = v`,
    whose base is a call's result, is rejected with `invalidAssignmentTarget`, while the pinned
    driver accepts it, as it accepts a struct field's element `s.xs[1] = v`; Lean has no `struct`.
    Binding the array to a local first, `let r = same(m); r[1] = v;`, writes the same object, since
    an array is a reference. No element place has a member or a mapping index before its elements,
    since inference's places hold no member and a mapping of arrays is rejected (difference 5), so
    the lowering takes a local followed by elements only.
17. **A slice views a memory array or a slice, and no array or mapping holds a slice.**
    `arraySlice<uint256>` is rejected with `unsupportedArrayType`. The pinned driver forms it: its
    `arraySlice<coll>` is an enum over any `coll`, whose values over other bases only its
    constructor makes (difference 4). An array of slices is rejected where the type is formed, as
    `bool[]` is (difference 6); the pinned driver accepts the annotation `arraySlice<uint256[]>[]`
    and fails `new arraySlice<uint256[]>[](2)` with SC0207, since a slice has no `Typedef<word>`. A
    mapping that holds a slice is rejected as one that holds an array is (difference 5), while the
    pinned driver accepts a contract field of that type.
18. **A slice needs its base's type known where the slice is.** The four slice forms on a base whose
    type is not a memory array or a slice there are rejected with `unsupportedExpression "slice"`,
    as a read on such a base takes the mapping rule (difference 15). Upstream's `Length` constraint
    waits for later uses to fix the type.
19. **A copy needs its slice known where the copy is.** `toArray(s)` is rejected with
    `operatorNotSupported "toArray"` when `s`'s type is not a slice there, as a length is on an
    array still open (difference 14). The pinned driver compiles `lam(s) { return toArray(s); }`
    applied to `m[0:2]`, since its constraints wait for later uses to fix the type. Only the slice
    must be known, not its element.
20. **`toArray` and `Length.length` are only called.** Lean has them as compiler forms that a call
    names, as row 1 has `Typedef.abs`, so `let copy = toArray;` is rejected with
    `unknownVariable "toArray"`, and `let size = Length.length;` with `unknownVariable "Length"`.
    The pinned driver compiles both, since std's `toArray` and `Length.length` are functions there.
21. **A memref refers to an element a memory array holds, and no array or mapping holds a memref.**
    `memref<bool>`, a memref of a slice and a memref of a memref are rejected where the type is
    formed, as `bool[]` is (difference 6), and generic `memref<t>` as generic `t[]` is. The pinned
    driver accepts the annotation `memref<bool>`, and generic `memref<t>` with
    `where t: Typedef<word>`. An array of memrefs is rejected where it is formed; the pinned driver
    accepts the annotation `memref<uint256>[]` and fails `new memref<uint256>[](2)` with SC0207,
    since a memref has no `Typedef<word>`. A mapping that holds a memref is rejected as one that
    holds an array is (difference 5), while the pinned driver accepts a contract field of that
    type.
22. **`lidx` needs its array known where the call is, and is only called.** `lidx(a, i)` is
    rejected with `operatorNotSupported "lidx"` when `a`'s type is not a memory array there, and
    `let at = lidx;` with `unknownVariable "lidx"`, as `toArray` is (difference 20). The pinned
    driver compiles `lam(a) { return lidx(a, uint256(1)); }` applied to `m`, and `let at = lidx;`
    applied to `m` and `uint256(1)`, since std's `lidx` is a function there whose constraints wait
    for later uses. Only the array must be known, not its element.
23. **`CanStore.load` needs its memref known where the call is, and is only called.**
    `CanStore.load(r)` is rejected with `operatorNotSupported "CanStore"` when `r`'s type is not a
    memref there, and `let get = CanStore.load;` with `unsupportedExpression "field"`, as
    `Length.length` is only called (difference 20). The pinned driver compiles
    `lam(r) { return CanStore.load(r); }` applied to `lidx(m, uint256(1))`, and
    `let get = CanStore.load;` applied to the same memref, since std's `CanStore` instance resolves
    once later uses fix the type. Only the memref must be known, not its element.
24. **`CanStore.store` needs its memref known where the call is, and is only called.**
    `CanStore.store(r, v)` is rejected with `operatorNotSupported "CanStore"` when `r`'s type is not
    a memref there, and `let put = CanStore.store;` with `unsupportedExpression "field"`. The pinned
    driver compiles `lam(r) { CanStore.store(r, uint256(5)); }` applied to `lidx(m, uint256(1))`,
    and `let put = CanStore.store;` applied to the same memref and `uint256(5)`. The value's type,
    unlike the memref's, may still be open: it unifies with the element. Both drivers reject a value
    of another type, the pinned driver with SC0207.
25. **A literal `lidx` index takes `uint256`, under `CanStore` too.** As a read's index does, it
    takes `uint256` wherever the call is: in `let r = lidx(m, 1);`, `bump(lidx(m, 1))`,
    `CanStore.store(lidx(m, 1), v)` and `CanStore.load(lidx(m, 1))`. The pinned driver gives the
    literal `uint256` in the first two, as it does a literal in a generic call's bound. It rejects
    the last two with SC0299, since the memref's type is still open there. Lean's memref takes its
    type from the array alone, so both are typed where the call is.

Differences 9 to 13 change only a diagnostic or the room of a resource limit, 8 and 14 to 24 only
reject some programs that upstream accepts, and 25 only accepts two forms that upstream rejects.
None of them changes what an accepted program means. Difference 1 does, by the user's decision 3.
Deferring the choice to finalization could lift differences 14, 15, 18 and 19 and the first
rejection in 22 to 24, as it could the open `Typedef` call. Nothing schedules it.

## What remains

- **Storage arrays, calldata arrays and `T[]` in the ABI**, so no `0x31` yet. They need the native
  pipeline's contract storage and calldata ABI first
  ([decision 4](#4-what-row-4s-lean-side-covers)). Contract declarations are catalogued, but their
  members are not typed (`ProgramContractSignature`). Persistent storage and external calls are not
  connected, and the ABI wrapper takes static words only ([README](../../README.md#proof-status)).
- **The meaning proofs for arrays** ([decision 6](#6-meaning-proofs)). The unit that relates array
  objects to their Core cells is under way, and changes the build-on statements that decision 6
  lists. The staged traces have the array forms and the element writes, and the whole-cell heap
  relation has the array objects; the payload cases, the compiler receipts and the heads follow.
  Arrays stay outside `StaticProfile`.
- **User collections indexed through `RValueIdxAccess`.** They need std's traits, and `Typedef` at
  a type parameter, which is row 1's open gap. Generic code over std's `Length` (`where c: Length`)
  waits for the same: Lean declares neither trait, so both are rejected with `unknownTrait`.
- **Raw memory:** `get_free_memory()`, `allocate_memory(size)`, `mload`, `mstore` and
  `abi_encode(v)`.
- **Deferred type resolution at finalization**, which could lift differences 14, 15, 18, 19 and the
  first rejection in 22 to 24. It is not scheduled.
