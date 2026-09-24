# ADR-0175: Value-free restricted runtime function compilation

- Status: Accepted
- Decision date: 2026-09-08
- Scope: explicit canonical entries compiled in their parameter typing context

## Decision

Compile the existing restricted function-entry profile without asking for
runtime argument values. A `CompiledRuntimeFunction` stores the type-only
parameter inputs, actual elaborated Core expression, and declared return type.
The independent `RuntimeFunctionCompiles` relation requires the existing
restricted header meaning, independent parameter declaration, and exact
return-body elaboration at that declared type. The relation must not mention
the executable compiler or contain a runtime-value-existence premise.

The executable `compileRuntimeFunction?` composes existing header interpretation,
type-only parameter declaration, and singleton return-body elaboration, then
checks the inferred body type against the declared return type. Retain the
exact Core returned by elaboration. Prove independent success and failure
characterization, exact result uniqueness, and Core typing in the declared
parameter context. A manually constructed compiled record alone carries none
of these guarantees.

## Runtime preparation factorization

Erase prepared runtime inputs to static inputs while leaving actual Core and
return type unchanged. A compiled record corresponds to an existing independent
runtime preparation exactly when it has independent compilation evidence and
the supplied structurally typed arguments have the expected source-order types.
The expected type list is the reverse of the static context's values.

Prove executable equality, including rejection:

```lean
(prepareRuntimeFunction? types owner declaration arguments).map
    PreparedRuntimeFunction.toCompiled =
  do
    let compiled ← compileRuntimeFunction? types owner declaration
    if arguments.map (·.type) = compiled.inputs.context.values.reverse then
      some compiled
    else
      none
```

The type guard preserves argument count and order. Forward correspondence uses
runtime parameter erasure and exact row layout; reverse correspondence uses
only the actual supplied values and their typing proofs. No dummy values or
inhabitation assumption may enter static compilation or reconstruction.

## Boundary

The output Core is open in the parameter context. It is not a function value,
source-call implementation, global declaration collector, whole-program
compiler, runtime argument decoder, or evaluator change. Existing restrictions
on header modifiers, generics, where clauses, explicit annotations, return
lists, and singleton return bodies remain unchanged. Arbitrary explicit type
aliases retain caller-defined meanings, including nominal data types for which
the default runtime typing environment supplies no argument inhabitant.

Compilation success does not guarantee that arguments exist, that a provided
argument list matches, or that execution completes at a chosen fuel. Existing
checked runtime execution and exact-cost theorems continue to apply only after
their stated preparation and argument conditions are met.

## Validation

Use independent compilation evidence for bare return, annotated parameter
return, and conditional bodies; preserve actual Core rather than an arbitrary
equally typed replacement. Include statically accepted nominal types without
runtime inhabitants, argument arity/type/order rejection, invalid whole headers
and bodies, and matching actual arguments whose values or costs differ while
their compiled projection stays fixed. Completely parse full declarations and
test value-free checking followed by unchanged checked execution. Audit all
public declarations, focused and aggregate builds, full tests, kernel checks,
forbidden proof tokens, and whitespace. Keep new proof files
below 300 lines and leave diagnostic proofs untouched.
