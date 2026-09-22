# ADR-0367: Lexical closures and function values

## Status

Accepted for the structural source runtime.  Runtime lambdas capture their
lexical environment, named source functions are first-class global values, and
application accepts direct globals, local closures, selected global values, or
compatible Core closures.  This supplies the higher-order value layer required
by roadmap phase 6.

## Context

A named table alone removes cyclic inlining for syntactically direct calls, but
it does not execute the function forms already retained by source inference.
The typed IR records source lambdas, function types, declaration references
used as values, and indirect-call metadata.  The earlier linker rejected these
forms because `Resolved.Expr` deliberately remains a narrow first-order
language.

Function types also erase source arity behind one bundled parameter type.  Zero,
one, and multiple source arguments must agree with that convention while each
selected runtime definition still retains the ordered parameter list needed to
bind stable source locals.  In particular, one product parameter and several
parameters can have the same structural function type.

## Decision

### Distinguish callable shape while checking

The runtime checker uses an internal callable static shape containing the
ordered parameter types and result type.  Erasing that shape yields the
ordinary Core function type whose parameter is the source argument bundle:
Unit for zero parameters, the parameter itself for one, and a right-associated
product for multiple parameters.

Named globals and freshly evaluated lambdas retain their ordered callable
shape, but application compares structural argument bundles rather than source
arity.  A function value that has passed through a structural context may keep
only its erased Core function type and uses the same comparison.  This allows a
conditional to select between compatible named functions without inventing a
new runtime closure or losing type checking.  Zero parameters and one Unit
parameter likewise share the Unit bundle and are normalized only after the
selected callee is known.

### Capture lexical environments at lambda evaluation

Evaluating a lambda produces a closure containing its ordered parameters,
declared result type, body, and the current local environment.  Applying that
closure evaluates the callee and arguments left to right, packs the supplied
values to Unit, a singleton value, or a right-associated product, checks the
exact bundle type, and unpacks that value according to the selected closure's
parameter list before prepending stable-ID bindings.  Thus a one-product-
parameter function and a multi-parameter function may flow through the same
structural function value and each receives its own normalized parameter view.
Inner binders may not duplicate a parameter or an already visible local
identity.

A named global evaluates to a compact key value rather than copying its body.
Application looks the key up in the same checked finite program and evaluates
the definition with an empty captured environment.  Global function values can
therefore be stored in locals, passed to another function, or selected by a
conditional, while direct and mutual recursion continue to share one table.

Runtime values also preserve incoming Core closures.  When such a closure is
applied, source arguments are packed by the same Unit/single/product convention
and execution delegates to the Core machine under the remaining fuel.  This is
a compatibility case, not a general equivalence theorem between the two
machines.

### Keep function-valued public results internal

Unit, Bool, Word, structural pairs, and existing Core values can project back
to the public Core value carrier.  A source lexical closure or named global
cannot: Core has no value containing a reference to this frontend runtime
table.  `Value.toCore?` therefore returns no projection for those two forms,
and the graph linker rejects a function-valued public result rather than
returning a dangling key or erasing a captured environment.

## Phase boundary

This ADR provides:

- lexical capture for source lambdas;
- first-class named source-function references;
- higher-order passing and internal returns through local variables, function
  parameters, and helper results;
- zero-, one-, and multiple-argument application under the source bundle
  convention; and
- conditional selection between compatible global function values.

It does not provide function equality, serialization, storage, function-valued
public results, recursive lexical `let`, closure conversion into ordinary Core,
or nominal closure environments.  The graph path also does not yet execute
indirect argument or result coercions, evidence-bearing function bodies, or
marked/comptime functions.  Host-function and effectful interoperation is not
claimed by the source regressions.

The proof boundary remains focused: executable checks cover one captured value,
but there is no broad lexical-scoping, closure-typing, substitution, or machine
correspondence development yet.

## Verification target

One checked runtime definition creates a lambda that ignores its own argument
and returns a captured entry parameter.  End-to-end source regressions pass a
capturing closure through another function, return a capturing closure from a
helper and invoke it inside the graph, invoke a two-argument lambda, select
between two named global functions before indirect application, and select
between one-product-parameter and two-parameter functions with the same erased
bundle type.  Zero-parameter and one-Unit-parameter functions are exercised
with both empty and Unit-valued call syntax.  Each case returns the expected
Word value.
