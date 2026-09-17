import VersoManual

open Verso.Genre Manual

#doc (Manual) "The model in one picture" =>
%%%
tag := "orientation"
file := "orientation"
%%%

Solcore is a language for describing computations and contracts. This
repository gives those computations a precise meaning in Lean, an executable
reference implementation, and proofs connecting parts of the implementation
to that meaning. It is useful both for understanding the language and for
asking whether another implementation behaves the same way.

A compiler may accept source text and emit bytecode. The model separates that
journey into smaller boundaries:

```
source text
    | parsing: words, structure, locations, diagnostics
    v
source syntax
    | resolution and checking: which name? which type?
    v
resolved / typed input
    | lowering: express the supported computation in Core
    v
Semantic Core
    | evaluate expressions and issue typed host requests
    v
contract execution in an explicit world
    | select committed state and observable effects
    v
observations: outcome, data, state, logs, created addresses
```

Each arrow needs its own justification. The existence of all these layers does
not imply a theorem about every source program passing through all of them.
The public Oracle starts at Core; the source frontend has a broader parser and
more restricted executable and proven semantic paths.

# A running question

Imagine a contract that reads a storage slot, adds one, writes it back, and
then returns. To explain it we need several rules:

* Words have 256 bits, so arithmetic can wrap.
* Expression evaluation has an order, so reads and writes cannot be freely
  exchanged.
* The storage operation refers to a particular account and slot.
* Return selects the working state for commitment.
* A revert selects the checkpoint instead, even if the write already happened.

A typing theorem answers whether the pieces fit together. A storage theorem
answers which read changes after a write. A rollback theorem answers which
world is selected. None of those alone proves that incrementing this slot is
what the contract's author intended.

# What defines the language?

The [specification charter](https://github.com/Y-Nak/solcore-lean/blob/main/docs/SPEC_CHARTER.md)
puts versioned declarative Lean rules first, followed by accepted decisions and
designated formats, corresponding executors, tests, and explanatory material.
Rust and Haskell implementations provide comparison evidence. Their behavior
does not silently replace the selected semantics.

There are also several meanings of “supported”:

: Representable

  A datatype can describe the construct.

: Executable

  A function can check or run it in a stated profile.

: Proven

  A theorem establishes a particular property under explicit assumptions.

: Published

  A versioned interface admits it with a fixed meaning.

These are separate questions. An internal extension may be executable and
proven while remaining unavailable in an older wire format.

# How to use this guide

Read the prose and small examples first. Declaration names link to formal
statements or provide signature hovers. The
{ref "reading-theorems"}[next chapter] explains how to read those statements.
The proof scripts are optional background.

Use the [current status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md)
for the detailed revision-local implementation boundary, and the
[feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md)
to locate an individual feature. Historical decisions explain why a rule was
chosen; their old progress reports do not override later implementations.
