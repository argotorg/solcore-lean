import VersoManual
import Guide.Orientation
import Guide.Theorems
import Guide.Language
import Guide.Checking
import Guide.Execution
import Guide.State
import Guide.Contracts
import Guide.SourceTypes
import Guide.SourceSemantics
import Guide.Frontend
import Guide.Oracle
import Guide.Guarantees
import Guide.Maintenance

open Verso.Genre Manual

#doc (Manual) "Solcore: semantics and proven guarantees" =>
%%%
tag := "solcore-guide"
shortTitle := "Solcore"
%%%

What does a Solcore program mean? What can its checker promise? Which changes
survive a failed contract call? This guide explains the model through examples
and the theorems that justify its behavior. You do not need to read Lean proofs
to follow it.

Start with {ref "orientation"}[the model in one picture], then follow an
expression from {ref "core-language"}[values and bindings] through
{ref "checking-a-program"}[checking] to {ref "execution"}[execution]. For
contracts, continue with {ref "state"}[state] and
{ref "contracts"}[return, revert, and calls]. The
{ref "guarantees"}[guarantee map] is a reference for returning readers.

The examples are checked against this checkout. The guide distinguishes
universal theorems, executable examples, and features whose wider correctness
remains open. Exact protocol fields and the revision-local feature inventory
remain in their linked reference documents.

{include 0 Guide.Orientation}

{include 0 Guide.Theorems}

{include 0 Guide.Language}

{include 0 Guide.Checking}

{include 0 Guide.Execution}

{include 0 Guide.State}

{include 0 Guide.Contracts}

{include 0 Guide.Frontend}

{include 0 Guide.SourceTypes}

{include 0 Guide.SourceSemantics}

{include 0 Guide.Oracle}

{include 0 Guide.Guarantees}

{include 0 Guide.Maintenance}
