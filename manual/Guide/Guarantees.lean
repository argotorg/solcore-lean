import VersoManual

open Verso.Genre Manual

#doc (Manual) "A map of the proven guarantees" =>
%%%
tag := "guarantees"
file := "guarantees"
%%%

Choose the question you want answered. The linked chapters combine worked
examples with the documentation from the declarations themselves. Their theorem
explanations have one source, beside the Lean definitions and proofs.

:::table +header
*
  * Question
  * Read
*
  * Does the checker recognize the typing rules?
  * {ref "checking-guarantee"}[Checking and its specification]
*
  * Does the machine implement evaluation, and what does typing add?
  * {ref "execution"}[Evaluation, safety, and fuel]
*
  * What does pausing and resuming preserve?
  * {ref "execution"}[Fuel and checkpoints]
*
  * What do the values and expression forms mean?
  * {ref "core-language"}[The Core language]
*
  * What changes after a local or persistent write?
  * {ref "state"}[State and storage]
*
  * What survives failure, and what can the host do?
  * {ref "contracts"}[Contracts and rollback]
*
  * What does parsing establish, and how do names become positions?
  * {ref "frontend"}[Source and local lowering]
*
  * What is executable in the source type system?
  * {ref "source-types"}[Types and specialization]
*
  * What is proven directly about source evaluation?
  * {ref "source-semantics"}[Independent source fragments]
*
  * Which inputs and observations make an experiment reproducible?
  * {ref "oracle"}[The Oracle and checked synthesis]
:::

The [current status](https://github.com/Y-Nak/solcore-lean/blob/main/docs/CURRENT_STATUS.md)
and [feature matrix](https://github.com/Y-Nak/solcore-lean/blob/main/docs/FEATURE_MATRIX.md)
locate the detailed revision-local boundaries. They are the reference for
whether a wider feature is implemented, published, or still deferred.

# Reading the boundary

A theorem applies only under its stated assumptions. The
{ref "reading-theorems"}[reading guide] explains how to distinguish a typing
property, a correspondence, an existence result, and an exact resource law.
A result about one stage does not automatically compose with every other stage.

The [specification charter](https://github.com/Y-Nak/solcore-lean/blob/main/docs/SPEC_CHARTER.md)
defines authority and trust. The
[compatibility evidence](https://github.com/Y-Nak/solcore-lean/blob/main/docs/COMPATIBILITY_MATRIX.md)
records the external comparisons that exist. These are the places to check
before turning a local guarantee into a claim about a complete compiler.
