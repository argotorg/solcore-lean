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

The store has a typing that records each allocated location's element type.
{name Solcore.Core.StoreHasTypes}`StoreHasTypes` connects those types to actual
contents. Allocation extends this typing; writes preserve the allocated
locations and their types.
{name Solcore.Core.evaluation_preserves_type}`evaluation_preserves_type`
tracks the final store as well as the result value.

{name Solcore.Core.CellPayload}`CellPayload` admits unit, Boolean, Word, and
products and sums recursively built from those types. Functions, cells, and
named data are not admitted cell payloads in this profile. The model makes
this restriction explicit rather than treating every Core type as storable.

# Persistent storage belongs to an account

{name Solcore.Semantics.WorldState}`WorldState` maps addresses to accounts.
Accounts contain balance, nonce, optional checked code, and sparse Word storage.
A storage key and value are both Words. This is distinct from a local cell's
location and type.

For a present account, reading an unwritten slot returns zero. Writing zero
removes the sparse entry without changing the value a later read observes.
An absent account is a different case: world-level reads and writes retain
presence information through optional results.

```lean
open Solcore.Semantics

example (slot value : Word) :
    (Account.empty.storageWrite slot value).storageRead slot
      = value := by
  exact Account.storageRead_storageWrite_same _ _ _
```

{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_same}`WorldState.readStorage?_writeStorage?_same`
expresses read-after-write at the world boundary, including the condition that
the account exists. The companion theorems
{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_slot}`WorldState.readStorage?_writeStorage?_other_slot`
and
{name Solcore.Semantics.WorldState.readStorage?_writeStorage?_other_address}`WorldState.readStorage?_writeStorage?_other_address`
show that a write preserves reads at a different slot or address. Their
inequality premises identify exactly which observations are unaffected.

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
