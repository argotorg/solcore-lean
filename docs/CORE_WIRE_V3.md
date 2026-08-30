# Semantic Core Wire v3

This page is the closed JSON catalog for `solcore-semantic-core/v3`. It is a
syntax-independent representation of the current Semantic Core, intended for
checking generated Core and for building checked contract packages. It is not
Solcore source syntax.

Every object is exact: fields not listed here are rejected, and every listed
field is required unless explicitly marked optional. Arrays retain their stated
order. Natural fields use nonnegative mathematical integers. Words use `0x`
followed by exactly 64 lowercase hexadecimal digits.

## Program

| Field | Value |
| --- | --- |
| `schema` | exact string `solcore-semantic-core/v3` |
| `resultType` | Type |
| `dataDefinitions` | array of DataDefinition |
| `body` | Expression |

A DataDefinition is the exact object
`{"constructorPayloadTypes": [Type, ...]}`. A data-type identity is a natural
index into `dataDefinitions`. A constructor identity is
`{"owner": <data-type index>, "index": <constructor index>}`.

## Types

The three scalar types are JSON strings: `"unit"`, `"bool"`, and `"word"`.
Composite types are exact tagged objects.

| Tag | Additional fields |
| --- | --- |
| `product` | `left`, `right` Types |
| `function` | `parameter`, `result` Types |
| `sum` | `left`, `right` Types |
| `cell` | `elementType` Type |
| `namedData` | `dataType` natural index |

## Expressions

Every expression is an object with a required `tag` and exactly the additional
fields below.

| Tag | Additional fields |
| --- | --- |
| `unit` | none |
| `bool` | `value` Boolean |
| `word` | `value` Word |
| `var` | `index` natural de Bruijn index |
| `pair` | `left`, `right` Expressions |
| `first` | `operand` Expression |
| `second` | `operand` Expression |
| `lambda` | `parameterType`, `resultType` Types; `body` Expression |
| `apply` | `function`, `argument` Expressions |
| `inLeft` | `rightType` Type; `payload` Expression |
| `inRight` | `leftType` Type; `payload` Expression |
| `case` | `scrutinee`, `leftBranch`, `rightBranch` Expressions |
| `newCell` | `elementType` Type; `initializer` Expression |
| `loadCell` | `reference` Expression |
| `storeCell` | `reference`, `value` Expressions |
| `construct` | `constructor` ConstructorId; `payload` Expression |
| `matchData` | `dataType` natural; `resultType` Type; `scrutinee` Expression; `branches` Expression array |
| `unary` | `op` UnaryOp; `operand` Expression |
| `binary` | `op` BinaryOp; `left`, `right` Expressions |
| `ternary` | `op` TernaryOp; `first`, `second`, `third` Expressions |
| `let` | `initializer`, `body` Expressions |
| `if` | `condition`, `thenBranch`, `elseBranch` Expressions |

De Bruijn binders prepend locals to the checking context. `lambda` and `let`
bind one local in `body`; each `case` branch binds its payload; each `matchData`
branch binds the corresponding constructor payload. No name or host-function
expression is serialized.

## Operators

Operators are encoded as the exact strings below.

| Family | Values |
| --- | --- |
| UnaryOp | `boolNot`, `wordNot`, `wordClz` |
| BinaryOp | `wordAdd`, `wordSub`, `wordMul`, `wordDiv`, `wordMod`, `wordEq`, `wordGt`, `wordSgt`, `wordAnd`, `wordOr`, `wordXor`, `wordShl`, `wordShr`, `wordByte`, `wordSar`, `wordPow`, `wordSignExtend`, `wordSdiv`, `wordSmod` |
| TernaryOp | `wordAddMod`, `wordMulMod` |

## Frozen host context

At the program root, free variables 0 through 13 have the following frozen
meaning. `product(a,b)`, `sum(a,b)`, and `function(a,b)` below abbreviate the
corresponding Type objects; they do not introduce alternate JSON spellings.

| Index | Public name | Parameter | Result | Internal host value |
| ---: | --- | --- | --- | --- |
| 0 | `storageRead` | word | word | `storageRead` |
| 1 | `storageWrite` | product(word, word) | unit | `storageWrite` |
| 2 | `storageAddress` | unit | word | `storageAddress` |
| 3 | `codeAddress` | unit | word | `codeAddress` |
| 4 | `callValue` | unit | word | `callValue` |
| 5 | `callerAddress` | unit | word | `callerAddress` |
| 6 | `inputDataByte` | word | sum(unit, word) | `inputDataByte?` |
| 7 | `inputDataSize` | unit | word | `inputDataSize` |
| 8 | `inputDataWordBE` | word | sum(unit, word) | `inputDataWordBE?` |
| 9 | `currentAddress` | unit | word | `currentAddress` |
| 10 | `callContractWord` | product(word, word) | sum(word, sum(word, sum(word, word))) | `callContractWord` |
| 11 | `callContractWordWithValue` | product(word, product(word, word)) | sum(word, sum(word, sum(word, word))) | `callContractWordWithValue` |
| 12 | `createContractWord` | product(word, product(word, word)) | sum(word, sum(word, sum(word, word))) | `createContractWord` |
| 13 | `emitLogWord` | product(word, word) | unit | `emitLogWord` |

The checker uses this table even if a later internal release appends another
host capability. Under `n` local binders, the same host entries appear at
indices `n` through `n + 13`; the first unbound free index is `n + 14`.

## Closed-boundary rules

- Wire-to-Core conversion is total for every value in this catalog.
- Core-to-wire projection is partial and rejects any later Core form not listed.
- Semantic Core Wire v1 and v2 remain separate closed types and reject v3-only
  forms.
- Wire v3 contains no runtime Value, closure environment, local Store, CEK
  state, proof witness, generated ABI cache, WorldState, or execution result.
- Static Word ABI metadata contains only a method name and a Wire v3
  implementation. Its `uint256` input/output shape, signature, and selector are
  derived during admission.
