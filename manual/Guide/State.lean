import VersoManual
import Solcore.Core.Safety
import Solcore.Semantics.WorldStateStorageReadWriteProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Three different kinds of state" =>
%%%
tag := "state"
file := "state"
%%%

The word “state” can hide important distinctions. Core has lexical bindings
and a local cell store. Contracts additionally have an account world. Execution
keeps checkpoint and working versions of that world so failure has a precise
meaning.

# An environment is a list of bindings

An environment gives values to positional variables. Extending it with a new
binding does not overwrite an older binding. A closure saves its lexical
environment so a function can continue to refer to the values visible where it
was created. A saved cell reference still points into the shared local store.

# A local cell store carries mutation

This expression allocates a Boolean cell, writes `false`, then reads it:

```lean
open Solcore.Core

def changeCell : Expr :=
  .letE (.newCell .bool (.bool true))
    (.letE (.storeCell (.var 0) (.bool false))
      (.loadCell (.var 1)))

example : run 30 (State.initial changeCell) =
    .done (.bool false) := by
  rfl
```

Why `var 1` in the last line? The inner let binds the write's unit result at
position zero. The cell reference moves to position one. Changing the cell
contents does not change which lexical position holds the reference.

{includeDocstring Solcore.Core.StoreHasTypes}

{name Solcore.Core.evaluation_preserves_type}`evaluation_preserves_type`

{includeDocstring Solcore.Core.evaluation_preserves_type}

{includeDocstring Solcore.Core.CellPayload}

# Persistent storage belongs to an account

{includeDocstring Solcore.Semantics.WorldState}

```lean
open Solcore.Semantics

example (slot value : Word) :
    (Account.empty.storageWrite slot value).storageRead slot
      = value := by
  exact Account.storageRead_storageWrite_same _ _ _
```

{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_same}`WorldState.readStorage?_writeStorage?_same`

{includeDocstring Solcore.Semantics.WorldState.readStorage?_writeStorage?_same}

{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_slot}`WorldState.readStorage?_writeStorage?_other_slot`

{includeDocstring Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_slot}

{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_address}`WorldState.readStorage?_writeStorage?_other_address`

{includeDocstring Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_address}

# A checkpoint determines what survives

During contract execution, the working world accumulates effects. The
checkpoint records the world to restore when the selected outcome requires
rollback. The same distinction applies to rollback-scoped journals, including
logs and created-address observations.

For a slot that starts at 7, is written to 8, and then reaches a terminal
outcome, the root policy is:

:::table +header
*
  * Outcome
  * Checkpoint slot
  * Working slot
  * Committed slot
*
  * Return
  * 7
  * 8
  * 8
*
  * Revert
  * 7
  * 8
  * 7
*
  * Trap
  * 7
  * 8
  * 7
:::

The return/revert distinction can also be checked directly on the generic
state-selection helper. The {ref "contracts"}[next chapter] shows that law
and explains why the helper deliberately leaves trap policy to its caller.

This table describes root state selection, not a claim that the write was
never evaluated. Speculative work and committed observations answer different
questions. A run that exhausts fuel has no terminal committed result yet.

These stores also differ from physical EVM byte-addressed memory. A theorem
about typed local cells or sparse account storage does not establish an EVM
memory layout, spill discipline, gas cost, or bytecode refinement.
