# Frontend freeze and resumption plan

Frontend work is paused while the concrete Solcore syntax is expected to
change. This document records what is preserved, what is stopped, and the
conditions for resuming.

## Preserved public boundary

Surface v1 and Oracle v4 remain supported exactly as published. They provide a
restricted single-file parse result with stable spans, diagnostics, schemas,
limits, and golden cases.

They do not resolve imports or names, type-check source, elaborate to Core, or
execute contracts.

## Preserved internal reference

The internal Multi frontend for its frozen grammar includes:

- pure workspace identity and validation;
- source-owned UTF-8 spans, tokens, comments, and a source-preserving AST;
- a total lexer;
- an unconditional chart parser;
- a complete structural validator;
- parser-wide source-location evidence;
- exact retained-token correspondence;
- a proof-carrying one-file frontend; and
- finite fast-parser schedule accounting plus a terminal-only execution base.

This is valuable historical and regression evidence. It is not assumed to be
the AST or grammar of the next Solcore syntax.

## Paused work

The following work is not active:

- the remaining fast-parser executor;
- operational equality with the chart parser;
- new grammar-specific rank, token, span, and diagnostic proofs;
- canonical standard-file parser certification;
- structural syntax identity over the frozen AST;
- module and lexical resolution over that AST;
- source checking and elaboration from that AST; and
- a public Multi workspace protocol.

ADR-0016 remains an Accepted design record. ADR-0017 remains Proposed. Their
implementation priority is suspended by ADR-0018 rather than erased.

## Working-tree experiment

An uncommitted synthetic comma-separator scan was started after the stable
parser commit 0209a37. It is incomplete and not part of the frozen guarantee.
It must not be included in semantic commits accidentally.

## Resume conditions

Parser and Surface-dependent work resumes only when:

1. a new concrete syntax version is named;
2. its lexical rules, grammar, AST, recovery policy, and diagnostic boundary
   are deliberately frozen;
3. the change from the retained Surface versions is documented;
4. the resolved semantic input expected by Core is stable enough to define the
   adapter target;
5. the proof and performance budget for grammar-specific regeneration is
   accepted; and
6. publication, if any, is assigned a new additive protocol boundary.

## Resumption order

After those gates:

1. define the new Surface algebra and parser judgment;
2. implement and prove lexer/parser correspondence;
3. restore structural, location, and token guarantees where they remain
   useful;
4. define structured identities and resolution;
5. implement Surface-to-Resolved and Resolved-to-Core elaboration;
6. prove identity, typing, effect, and stage preservation;
7. publish only after schemas, limits, capabilities, and golden cases close.

Semantic Core work can proceed without waiting for any of these steps.
