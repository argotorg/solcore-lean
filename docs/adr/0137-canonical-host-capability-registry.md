# ADR-0137: Canonical host capability registry

- Status: Accepted
- Decision date: 2026-08-29
- Scope: one canonical ordering for the existing internal Core host capabilities
- Implementation: In progress

## Context

Core currently has nine host functions. Their parameter and result types and
their stable numeric indexes are defined on `HostFunction`, while
`hostContext` and `hostEnvironment` repeat the same order as two independent
list literals. The runtime-environment typing proof then repeats that order a
third time as nine nested constructors.

All three copies are correct today:

| Index | Capability |
| ---: | --- |
| 0 | `storageRead` |
| 1 | `storageWrite` |
| 2 | `storageAddress` |
| 3 | `codeAddress` |
| 4 | `callValue` |
| 5 | `callerAddress` |
| 6 | `inputDataByte?` |
| 7 | `inputDataSize` |
| 8 | `inputDataWordBE?` |

The duplication makes a future append unnecessarily risky. A capability can
be added to one table but omitted from another, or the type and value tables
can be reordered independently. Individual lookup and length regressions
would eventually expose the mistake, but only after several definitions have
already diverged.

This normalization adds no capability or behavioral change.

## Decision

Add one explicit registry in the `HostFunction` namespace:

```lean
def HostFunction.all : List HostFunction :=
  [.storageRead, .storageWrite, .storageAddress, .codeAddress,
    .callValue, .callerAddress, .inputDataByte?, .inputDataSize,
    .inputDataWordBE?]
```

`HostFunction.all` is the sole source of table order. The order above is
unchanged and append-only. A future capability may be added only at the end;
existing entries may not move, disappear, or be reused.

Keep `HostFunction.index` as an explicit pattern match with the existing
values 0 through 8. It is the numeric ABI declaration, not a computation of a
list position. Its constructor cases remain exactly the index table above.

The registry and explicit index have different responsibilities; general laws make drift a proof failure instead of a silent ABI change.

Do not implement `HostFunction.index` by searching through `all`.

## Registry laws

Prove the complete finite-registry contract:

- `HostFunction.all.length = 9`;
- `HostFunction.all.Nodup`;
- every `HostFunction` is a member of `HostFunction.all`;
- `HostFunction.all[function.index]? = some function` for every function;
- mapping `HostFunction.index` over `all` produces
  `List.range HostFunction.all.length` exactly;
- `HostFunction.index` is injective;
- an index is represented by a host function exactly when it is below
  `HostFunction.all.length`; and
- lookup in `all` is exact: `all[index]? = some function` holds exactly for
  the function whose explicit index is `index`.

Representative theorem shapes are:

```lean
theorem HostFunction.mem_all (function : HostFunction) :
    function ∈ HostFunction.all

theorem HostFunction.getElem?_all_index (function : HostFunction) :
    HostFunction.all[function.index]? = some function

theorem HostFunction.getElem?_all_iff {index : Nat} {function : HostFunction} :
  HostFunction.all[index]? = some function ↔ function.index = index

theorem HostFunction.exists_index_iff (index : Nat) :
    (∃ function, function.index = index) ↔
      index < HostFunction.all.length
```

Names may be adjusted to the repository's conventions, but the facts may not
be weakened into nine unrelated constructor calculations. The existing
constructor-specific `index_*` simp theorems remain available and keep their
current statements.

## Derived host tables

Define both fixed host tables only by mapping the registry:

```lean
def hostContext : Context :=
  HostFunction.all.map HostFunction.functionType

def hostEnvironment : Environment :=
  HostFunction.all.map Value.hostFunction
```

No second literal list, private duplicate registry, or separately maintained
ordering is permitted. This is the central normalization provided by the ADR.

Prove generic lookup laws for any capability:

```lean
theorem hostContext_lookup (function : HostFunction) :
    hostContext[function.index]? = some function.functionType

theorem hostEnvironment_lookup (function : HostFunction) :
    hostEnvironment[function.index]? = some (.hostFunction function)
```

Also expose generic structural laws:

- both table lengths equal `HostFunction.all.length`;
- therefore both table lengths equal 9;
- lookup in either table is present if and only if its position is below the
  registry length; and
- index 9, equivalently `HostFunction.all.length`, is the first unbound
  position in both tables.

The existing `hostContext_storageRead` through
`hostContext_inputDataWordBE?` and matching `hostEnvironment_*` theorems must
remain under their current names and with their current statements. They
become compatibility aliases proved from the generic lookup laws. Their
existing `@[simp]` attributes must also remain. Existing consumers should not
have to unfold the registry or change proofs merely because the tables now
have one source.

Likewise, keep `hostContext_length`, `hostEnvironment_length`, and the current
numeric index simp theorems as compatibility facts, including their existing
`@[simp]` attributes.

## Runtime typing

Replace the nine-level hand-written `hostEnvironment_hasTypes` proof with one
theorem for an arbitrary list of capabilities:

```lean
theorem hostFunctions_haveTypes
    (world : StoreTyping)
    (functions : List HostFunction)
    (definitions : DataEnvironment := []) :
  HostRuntimeEnvironmentHasTypes world
    (functions.map Value.hostFunction)
    (functions.map HostFunction.functionType)
    definitions
```

Prove it by induction on `functions`. The empty list uses `.nil`; the
nonempty case uses `.cons .hostFunction` and the induction hypothesis.

The existing `@[simp]` theorem `hostEnvironment_hasTypes` remains the public
proof surface for the fixed runtime environment. Derive it by specializing
the general theorem to `HostFunction.all` and simplifying only the two mapped
table definitions. This ensures that a future append automatically extends the
runtime typing proof without another manually nested constructor.

## Compatibility and ABI boundary

This change is definitionally intended to preserve the current lists, but
callers rely on named theorems as well as computed values. Preserve all of the
following:

- the nine constructor indexes 0 through 8;
- the exact table order shown above;
- both table lengths at 9 for this nine-entry migration;
- index 9 as the first unbound position for this nine-entry migration;
- all existing capability-specific lookup theorem names and statements;
- all existing `@[simp]` attributes on compatibility theorems;
- `hostEnvironment_hasTypes` with its existing arguments and conclusion; and
- host checker and runner behavior for every existing Core program.

The current numeric length and first-unbound facts intentionally change when a
future capability is appended; the old indexes never do. The explicit numeric
regressions in `CoreHostMachine` remain in place. Add
generic compile-time and executable checks for registry length, membership,
index coverage, exact table derivation, and the first-unbound boundary. Do not
replace the numeric 0-through-8 assertions solely with abstract registry
facts: the concrete values are the ABI regression.

## Migration sequence

Keep each implementation commit at or below 300 changed lines:

1. add `HostFunction.all` and prove its length, membership, no-duplicate,
   lookup, index-range, injectivity, and exact-range laws;
2. redefine `hostContext` and `hostEnvironment` as maps over `all`, then prove
   generic lookup, length, bounds, and first-unbound laws;
3. re-prove every existing individual lookup and length fact as a
   compatibility alias without changing its statement;
4. add the arbitrary-list runtime typing induction and specialize the current
   fixed-environment theorem;
5. add focused generic and numeric regressions without changing runtime test
   fixtures; and
6. run full validation and synchronize internal implementation documents.

Compile direct dependants at each stage. Remove temporary duplicate tables and
proof helpers before acceptance.

## Validation

Acceptance requires:

- focused builds of the registry, host table, host safety, checked-program,
  driver, and Core host-machine test roots;
- the full build and executable test suite;
- zero-placeholder and warning-as-error checks on every changed Lean root;
- an axiom audit of the registry, generic lookup, exact-range, and generic
  runtime-typing theorems;
- metadata, kernel, and whitespace/diff checks;
- compile-time confirmation that all old lookup and length theorem statements
  still typecheck unchanged and retain their simplification behavior;
- executable confirmation of indexes 0 through 8, table length 9, and first
  unbound index 9; and
- an independent review for table duplication, accidental index computation,
  theorem weakening, and scope expansion.

No trust increase, placeholder proof, or new noncomputable dependency is
accepted merely to prove the finite registry facts.

## Risks and mitigations

**The list and explicit index can disagree.** This duplication is intentional:
one declares table order and the other declares numeric ABI. Exact lookup,
mapped-range, injectivity, and exact-range theorems make disagreement fail the
build.

**Changing definitions can disturb simplification.** Existing named lookup,
length, and index theorems remain compatibility aliases. Consumers should use
those facts or the new generic facts rather than depend on list reduction.

**A future constructor can be omitted.** `mem_all` and exact index-range proofs
must cover every constructor, so omission leaves proof obligations open.

**A future entry can be inserted in the middle.** The retained numeric tests
and `all[index]?` law fail unless old positions remain fixed. The documented
append-only rule makes the required repair unambiguous.

## Rejected alternatives

**Compute `index` with `idxOf` over `all`.** Rejected because a list reorder
would then silently redefine every numeric index. The stable ABI must remain
an explicit constructor pattern match.

**Keep three hand-maintained copies and add more constructor tests.** Rejected
because tests detect drift but do not remove its cause. The two runtime tables
and their typing proof should be structurally derived from one order.

**Derive the registry from an implicit enumeration or constructor order.**
Rejected because constructor enumeration makes ordering less visible and can
turn a source refactor into an ABI change. The canonical list is intentionally
written out.

**Replace `HostFunction` with a descriptor record.** Rejected because it would
expand the change into request dispatch, equality, serialization-adjacent
code, and runtime behavior. A finite list is sufficient for this normalization.

**Delete individual lookup theorems after adding generic ones.** Rejected
because those names are an established proof interface and provide readable
capability-specific regressions.

## Non-goals

This ADR does not:

- add, remove, rename, reorder, or change the type of a host capability;
- refactor exhaustive case analysis over `HostRequest`, the Core machine,
  suspension, transition, handler, or driver;
- change request responses, runtime execution, fuel, faults, or Store effects;
- change storage semantics, checkpoints, lifecycle, gas, scheduling, or
  resumption;
- publish a capability registry or alter any public ABI;
- change Wire, Oracle, Surface, parser, source syntax, metadata schema, or
  external format; or
- resume parser or syntax proofs paused by the current semantics-first plan.

The root README does not change.

## Consequences

Core host capability order becomes visible in exactly one canonical list.
Host types, runtime values, and their safety proof are derived from that list,
while explicit numeric indexes remain independently fixed and formally tied
to it. Future append-only capabilities therefore have one ordering edit and a
small set of proof obligations that immediately expose omissions, reorders,
duplicates, or ABI drift.

Runtime meaning and every existing public boundary remain unchanged.
