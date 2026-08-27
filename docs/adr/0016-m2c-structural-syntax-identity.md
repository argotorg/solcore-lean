# ADR-0016: M2c structural syntax identity

- Status: Accepted
- Decision date: 2026-08-18
- Scope: M2c parsed-syntax identity and address certification

## Reader summary / Current implementation

- **Decision:** Assign every Multi Surface syntax site one role-tagged,
  module-rooted structural address; derive certified module-reference sites,
  virtual scope identities, canonical indices, selection, and finite measures
  without using spans or compiler allocation identity.
- **Current implementation:** The ADR is Accepted, so implementation is
  authorized against the frozen ADR-0015 boundary. No Structural identity
  modules are currently present in Solcore; implementation has not started
  and is paused by ADR-0018.
- **Not yet implemented:** `prepareGraphModule`, structural selection and
  inventories, `CertifiedModuleIndex`, identity lifting, scope/owner tables,
  primary-span proofs, and the required traversal and injectivity audits.
  ADR-0015 now produces CertifiedParsedModule; the remaining blocker is the
  deliberate semantics-first development freeze.
- **Suggested reading:** Read “Dependency and frozen boundaries”, “One absolute
  address scheme”, and “Exact direct-child inventory” first; then read
  “Virtual lexical scopes”, “Construction boundary and diagnostics”, and
  “Required proof boundary”. The long role tables are reference material.

The remainder of this ADR is a technical reference. For the current
development priority and pause condition, read the frontend freeze plan.

## Context

ADR-0014 fixes source and module identity without interpreting source syntax.
ADR-0015 fixes the closed Multi Surface AST, parser judgments, structural
acceptance, and `Multi.CertifiedParsedModule`. Graph construction, interface
saturation, lexical resolution, and diagnostics additionally need stable
identities for syntax inside each parsed module.

A source span is not an identity. Nested nodes may share a span, and identical
text can occur at many sites. A plain sequence of list indices is also
ambiguous: top item zero, contract member zero, constructor zero, parameter
zero, statement zero, and argument zero must not collide. Compiler pointers,
hash-table positions, generated names, source text, and resolver insertion
order are not portable structural evidence.

An earlier combined resolver proposal mixed module-root and owner-relative
paths, treated every lexical scope as an AST node, and allowed graph code to
construct keys before a later address-validation phase. That creates a cycle:
the graph consumes identities whose validity is not yet established. It also
invites a source diagnostic for a defect in the identity implementation.

This decision gives every syntax site one role-tagged address from its module
root. Immediately after ADR-0015 parses a file, a total preparation function
constructs every certified module-reference site that a later graph may
consume. Any finite collection of distinct prepared modules can then form a
policy-free canonical index, and module-local identities lift injectively into
identities indexed by that exact collection. Root selection, edge resolution,
reachability, and pattern classification remain outside this ADR.

## Decision

### Dependency and frozen boundaries

The prerequisite parser boundary is exactly:

```text
Multi.SourceSpan
Multi.Located alpha
Multi.ParsedModuleV1
Multi.CertifiedParsedModule
Multi.parseModule :
  WorkspaceFile ->
  Except (NonemptyList Multi.SurfaceDiagnostic)
    Multi.CertifiedParsedModule
```

The syntax algebra is the one in ADR-0015 under "Closed source-preserving
AST". In particular:

- `ParsedModuleV1` itself is located;
- every semantic syntax node, identifier, path component, selector marker,
  module-root marker, fallback marker, contract-constructor marker, modifier,
  operator, and assembly slice is located;
- import mode is the one unlocated subordinate sum retained inside a located
  import declaration;
- sum constructors carry their displayed direct named fields and do not add a
  variant-payload wrapper;
- any mechanical `Box` inserted for Lean positivity is transparent and does
  not add an address step;
- absent constructs are `none` and do not acquire a structural node;
- ordinary punctuation and `SourceSpan` metadata retained in `BodyOrigin` or a
  statement terminator are not syntax nodes;
- a call has an arbitrary expression callee;
- a statement return value and statement else body are optional;
- a function type has one domain and one codomain;
- a class declaration name is one `IdentifierOccurrence`, while an instance's
  referenced class remains a `QualifiedName`; and
- explicit type, expression, and pattern groups remain distinct nodes.

Whitespace, comments, and the retained token stream remain parser evidence.
They do not receive resolver identities. This ADR neither changes parser
spans nor inserts normalized syntax.

Surface v1, parse-result v1, Oracle v1 through v4, draft.1 through draft.4,
all existing profiles, feature statuses, Semantic Core versions, schemas,
capability bytes, and golden streams remain unchanged. These identities are
internal and have no wire encoding.

The cross-ADR freeze assumes the reviewed ADR-0015 names
`Multi.ModuleReferenceShape` and `Multi.CertifiedParsedModule`,
`ClassDeclPayload.className : IdentifierOccurrence`, a `Marker` in the pattern
wildcard case, and `ClassMethodDecl` as its own located wrapper. Any change to
these facts reopens the inventory and identity review; it is not an
implementation shortcut.

### Module-local preparation and policy-free index

```text
GraphReadyModule = {
  parsed           : Multi.CertifiedParsedModule,
  moduleReferences : List (Structural.ModuleReferenceSite parsed),
  ...proof that the list is complete, duplicate-free, and in source order...
}

prepareGraphModule : Multi.CertifiedParsedModule -> GraphReadyModule

parseGraphModule file = Multi.parseModule file |>.map prepareGraphModule
```

`prepareGraphModule` is total and has no diagnostic result. Its keys carry
selection proofs against `parsed.module`. Graph code accepts only
`GraphReadyModule`; it cannot accept a raw address or fabricate an edge site.
Preparation preserves the parser certificate definitionally and only adds the
derived reference-site enumeration and its proofs.
The graph-phase parser entry is `parseGraphModule`, not `Multi.parseModule`
alone: preparation therefore finishes before discovery can inspect the first
outgoing reference.

This ADR also defines a collection certificate with no graph policy:

```text
moduleId (module : GraphReadyModule) =
  module.parsed.file.id.toModuleId

CertifiedModuleIndex = {
  modules : List GraphReadyModule,
  sorted  : PairwiseStrictAscending modules by moduleId
}

CertifiedModuleIndex.ofUnique
  : (modules : List GraphReadyModule)
    -> PairwiseDistinct (modules.map moduleId)
    -> CertifiedModuleIndex
```

`ofUnique` sorts by ADR-0014 `ModuleId` order and preserves membership exactly;
it does not select, discard, or discover a module. Strict ordering entails
unique `ModuleId` and `SourceId` values. An empty index and a singleton index
are valid. There is no root, source edge, reachability witness, entry marker,
standard-library requirement, or resolver diagnostic in this type.

A later ADR may wrap one `CertifiedModuleIndex` with roots, graph closure, and
other resolver evidence. That wrapper does not change the structural index
parameter of an identity and cannot admit a module absent from the index.

### One absolute address scheme

All syntax and virtual-scope identities use one address from a located parsed
module root.

```text
StructuralAddress = List ChildStep

ChildStep =
  | locatedPayload
  | singular DirectRole
  | indexed ListRole Nat
  | virtualScope ScopeRole
```

The empty address selects the located `ParsedModuleV1` root. A
`locatedPayload` step selects the payload of the currently selected
`Multi.Located` value. A `singular` step selects one present direct child. An
`indexed` step selects the written zero-based element of a list or nonempty
list. A `virtualScope` step selects a derived lexical scope and must be the
last step.

There are no owner-relative suffixes, parent escapes, untagged indices,
field-number aliases, parser-recovery steps, or addresses through span
metadata. An absent optional field has no child, so its direct role does not
select. The address retains every located wrapper: reaching a located child
and then its payload always requires two distinct selections.

Selection uses this closed node-kind vocabulary:

```text
SyntaxSort =
  parsedModule | topItem | qualifiedName |
  identifier | pathComponent | externalLibraryName |
  syntaxMarker | unitMarker |
  moduleReference |
  importSelectorEntry | importSelection | hidingClause |
  importMode | importDecl |
  constructorSelection | exportItem | exportEntry | localExportList |
  remoteExportEntry | remoteExportSelection | exportMode |
  forallBinder | forallClause | predicate | genericPrefix | parameter |
  functionSignature | classMethodDecl | functionDecl | fallbackDecl |
  contractConstructorDecl | dataConstructor | dataDecl | typeAliasDecl |
  classDecl | instanceDecl | pragmaKind | pragmaDecl |
  fieldDecl | contractMember | contractDecl |
  literal | typeExpr | prefixOperator | infixOperator |
  assignmentOperator | expression | pattern | body | letBinding |
  forInitItem | forPostItem | matchArm | statement | assemblySlice

SelectedKind =
  | located SyntaxSort
  | payload SyntaxSort
  | virtualScope ScopeRole
```

`located importMode` is uninhabited because ADR-0015 stores that one
subordinate sum without a location wrapper. Every other `located` case is
inhabited exactly when ADR-0015 defines the corresponding `Located` alias or
field. `unitMarker` is the payload of a located `Unit` used for leading-dot and
proxy punctuation that is not a `SyntaxMarker`; external `@` is the
`externalSigil` syntax marker. The vocabulary has no generic extension case.

`DirectRole` is the following closed sum. Its constructor order is exactly the
displayed order:

```text
topImport, topExport, topPragma, topData, topTypeAlias,
topClass, topInstance, topContract, topFunction,

moduleLibraryMarker, moduleStandardMarker,
moduleExternalSigil, moduleExternalLibrary,

importModuleReference, importMode,
importModuleAlias, importItemSelection, importHidingClause,
importWildcardMarker, importNamedSource, importNamedAlias,

constructorAllMarker,
exportItemName, exportItemConstructors,
exportWildcardMarker, exportEntryItem,
exportAllFromModuleReference, exportAllFromMarker,
remoteWildcardMarker, remoteExportItem, remoteDotWildcardMarker,
exportLocalSelection, exportModuleReference, exportModuleAlias,
exportFromModuleReference, exportFromSelection,

forallBareBinder, forallBoundedBinder, forallBoundClass,
parameterComptimeMarker, parameterName, parameterType,
predicateMain, predicateClass,
genericPrefixForall, functionGenericPrefix,
functionPublicMarker, functionPayableMarker, functionName,
functionReturnType, classMethodSignature, functionSignature, functionBody,
fallbackGenericPrefix, fallbackPublicMarker, fallbackPayableMarker,
fallbackMarker, fallbackReturnType, fallbackBody,
constructorPublicMarker, constructorPayableMarker, constructorMarker,
constructorBody,

dataConstructorName, dataName,
typeAliasName, typeAliasBody,
classGenericPrefix, classMain, className,
instanceGenericPrefix, instanceDefaultMarker, instanceMain, instanceClass,
pragmaKind,
fieldName, fieldType, fieldInitializer,
contractMemberData, contractMemberTypeAlias, contractMemberField,
contractMemberFunction, contractMemberFallback, contractMemberConstructor,
contractName,

typeNamedName, typeProxyMarker, typeProxyInner,
typeFunctionDomain, typeFunctionCodomain,
typeGroupInner, typeComptimeMarker, typeComptimeInner,

expressionName, expressionCallCallee,
expressionSelectReceiver, expressionSelectField,
expressionDotMarker, expressionDotName,
expressionProxyMarker, expressionProxyType, expressionLiteral,
expressionLambdaReturnType, expressionLambdaBody,
expressionAnnotationValue, expressionAnnotationType,
expressionKeywordCondition, expressionKeywordThen, expressionKeywordElse,
expressionTernaryCondition, expressionTernaryThen, expressionTernaryElse,
expressionIndexReceiver, expressionIndexValue,
expressionPrefixOperator, expressionPrefixOperand,
expressionInfixLeft, expressionInfixOperator, expressionInfixRight,
expressionGroupInner,

patternNamedName, patternDotMarker, patternDotName,
patternWildcardMarker, patternLiteral,
patternComptimeMarker, patternComptimeExpression, patternGroupInner,

letName, letComptimeMarker, letType, letInitializer,
forInitLetBinding, forInitAssignmentLeft,
forInitAssignmentOperator, forInitAssignmentRight, forInitExpression,
forPostAssignmentLeft, forPostAssignmentOperator,
forPostAssignmentRight, forPostExpression,
matchArmBody,
statementAssignmentLeft, statementAssignmentOperator,
statementAssignmentRight, statementLetBinding, statementBlockBody,
statementExpression, statementReturnValue, statementAssemblySlice,
statementIfCondition, statementIfThenBody, statementIfElseBody,
statementForCondition, statementForBody
```

`ListRole` is this closed sum, in this order:

```text
moduleItems,
moduleRelativeComponents, moduleLibraryTail,
moduleStandardTail, moduleExternalTail,
qualifiedNameComponents,
importSelectionEntries, hidingNames,
constructorNames, localExportEntries, remoteExportEntries,
forallBoundArguments, forallClauseBinders, genericContext,
functionParameters, fallbackParameters, constructorParameters,
predicateParameters,
dataConstructorFields, dataParameters, dataConstructors,
typeAliasParameters,
classParameters, classMethods,
instanceParameters, instanceMethods,
pragmaTargets, contractParameters, contractMembers,
typeNamedArguments, typeTupleElements,
expressionCallArguments, expressionDotArguments,
expressionLambdaParameters, expressionTupleElements,
patternNamedArguments, patternDotArguments, patternTupleElements,
bodyStatements,
statementMatchScrutinees, statementMatchArms,
statementForInitializers, statementForPostItems,
matchArmPatterns
```

`ScopeRole` is this closed sum, in this order:

```text
module,
dataParameters, typeAliasParameters, contractParameters,
topFunctionGeneric, classGeneric, classMethodGeneric,
instanceGeneric, instanceMethodGeneric,
contractFunctionGeneric, fallbackGeneric,
topFunctionParameters, classMethodParameters,
instanceMethodParameters, contractFunctionParameters,
fallbackParameters, contractConstructorParameters,
lambdaParameters,
bodyEntry, matchArmBindings, loopHeader,
sequentialContinuation
```

### Exact direct-child inventory

The following tables are normative. They list every recursive AST child and no
other child. `one r : X` means `singular r` selects one `X`; `maybe` means it
selects only when the option is present; `many r : X` means `indexed r i`
selects the `i`th written `X`. `L X` is a located `X`. The rows for each parent
are in lexical source order and therefore define `childOrdinal` for that
parent. A variant not shown has no recursive child.

Every located carrier has the first transition, without exception:

```text
L X
  one locatedPayload : payload X
```

Module, top-item, and name inventory:

```text
ParsedModuleV1Payload
  many moduleItems : TopItem

TopItemPayload.importDecl
  one topImport : ImportDecl
TopItemPayload.exportDecl
  one topExport : ExportDecl
TopItemPayload.pragmaDecl
  one topPragma : PragmaDecl
TopItemPayload.dataDecl
  one topData : DataDecl
TopItemPayload.typeAliasDecl
  one topTypeAlias : TypeAliasDecl
TopItemPayload.classDecl
  one topClass : ClassDecl
TopItemPayload.instanceDecl
  one topInstance : InstanceDecl
TopItemPayload.contractDecl
  one topContract : ContractDecl
TopItemPayload.functionDecl
  one topFunction : FunctionDecl

QualifiedNamePayload
  many qualifiedNameComponents : IdentifierOccurrence
```

Module-reference inventory:

```text
ModuleReferencePayload.relative
  many moduleRelativeComponents : PathComponent
ModuleReferencePayload.libraryRoot
  one  moduleLibraryMarker : Marker
  many moduleLibraryTail   : PathComponent
ModuleReferencePayload.standard
  one  moduleStandardMarker : Marker
  many moduleStandardTail   : PathComponent
ModuleReferencePayload.external
  one  moduleExternalSigil   : Marker
  one  moduleExternalLibrary : L ExternalLibraryName
  many moduleExternalTail    : PathComponent
```

The standard tail can be empty. Thus `std` and `std.std` have different trees
and keys. Relative, library-root, and external component lists are nonempty as
fixed by ADR-0015.

Import inventory:

```text
ImportDeclPayload
  one importModuleReference : ModuleReference
  one importMode            : ImportMode

ImportMode.module
  maybe importModuleAlias : IdentifierOccurrence
ImportMode.items
  one   importItemSelection : ImportSelection
  maybe importHidingClause  : HidingClause

ImportSelectionPayload
  many importSelectionEntries : ImportSelectorEntry
HidingClausePayload
  many hidingNames : IdentifierOccurrence

ImportSelectorEntryPayload.wildcard
  one importWildcardMarker : Marker
ImportSelectorEntryPayload.named
  one   importNamedSource : IdentifierOccurrence
  maybe importNamedAlias  : IdentifierOccurrence
```

Export inventory:

```text
ConstructorSelectionPayload.all
  one constructorAllMarker : Marker
ConstructorSelectionPayload.named
  many constructorNames : IdentifierOccurrence

ExportItemPayload
  one   exportItemName         : IdentifierOccurrence
  maybe exportItemConstructors : ConstructorSelection

ExportEntryPayload.wildcard
  one exportWildcardMarker : Marker
ExportEntryPayload.item
  one exportEntryItem : ExportItem
ExportEntryPayload.allFrom
  one exportAllFromModuleReference : ModuleReference
  one exportAllFromMarker          : Marker

LocalExportListPayload
  many localExportEntries : ExportEntry

RemoteExportEntryPayload.wildcard
  one remoteWildcardMarker : Marker
RemoteExportEntryPayload.item
  one remoteExportItem : ExportItem

RemoteExportSelectionPayload.dotWildcard
  one remoteDotWildcardMarker : Marker
RemoteExportSelectionPayload.braced
  many remoteExportEntries : RemoteExportEntry

ExportMode.local
  one exportLocalSelection : LocalExportList
ExportMode.module
  one   exportModuleReference : ModuleReference
  maybe exportModuleAlias     : IdentifierOccurrence
ExportMode.from
  one exportFromModuleReference : ModuleReference
  one exportFromSelection       : RemoteExportSelection
```

Generic, callable, and predicate inventory:

```text
ForallBinderPayload.bare
  one forallBareBinder : IdentifierOccurrence
ForallBinderPayload.bounded
  one  forallBoundedBinder : IdentifierOccurrence
  one  forallBoundClass    : QualifiedName
  many forallBoundArguments : TypeExpr

ForallClausePayload
  many forallClauseBinders : ForallBinder

PredicatePayload
  one  predicateMain  : TypeExpr
  one  predicateClass : QualifiedName
  many predicateParameters : TypeExpr

GenericPrefixPayload
  one  genericPrefixForall : ForallClause
  many genericContext      : Predicate

ParameterPayload
  maybe parameterComptimeMarker : Marker
  one   parameterName           : IdentifierOccurrence
  maybe parameterType           : TypeExpr

FunctionSignaturePayload
  maybe functionGenericPrefix : GenericPrefix
  maybe functionPublicMarker  : Marker
  maybe functionPayableMarker : Marker
  one   functionName          : IdentifierOccurrence
  many  functionParameters    : Parameter
  maybe functionReturnType    : TypeExpr

ClassMethodDeclPayload
  one classMethodSignature : FunctionSignature

FunctionDeclPayload
  one functionSignature : FunctionSignature
  one functionBody      : Body

FallbackDeclPayload
  maybe fallbackGenericPrefix : GenericPrefix
  maybe fallbackPublicMarker  : Marker
  maybe fallbackPayableMarker : Marker
  one   fallbackMarker        : Marker
  many  fallbackParameters    : Parameter
  maybe fallbackReturnType    : TypeExpr
  one   fallbackBody          : Body

ContractConstructorDeclPayload
  maybe constructorPublicMarker  : Marker
  maybe constructorPayableMarker : Marker
  one   constructorMarker        : Marker
  many  constructorParameters    : Parameter
  one   constructorBody          : Body
```

ADR-0015 structurally rejects the currently disallowed fallback and constructor
modifiers, but their raw AST fields remain in this complete inventory because
the certified parser proves their accepted absence.

Declaration inventory:

```text
DataConstructorPayload
  one  dataConstructorName : IdentifierOccurrence
  many dataConstructorFields : TypeExpr

DataDeclPayload
  one  dataName         : IdentifierOccurrence
  many dataParameters   : IdentifierOccurrence
  many dataConstructors : DataConstructor

TypeAliasDeclPayload
  one  typeAliasName       : IdentifierOccurrence
  many typeAliasParameters : IdentifierOccurrence
  one  typeAliasBody       : TypeExpr

ClassDeclPayload
  maybe classGenericPrefix : GenericPrefix
  one   classMain          : TypeExpr
  one   className          : IdentifierOccurrence
  many  classParameters    : TypeExpr
  many  classMethods       : ClassMethodDecl

InstanceDeclPayload
  maybe instanceGenericPrefix : GenericPrefix
  maybe instanceDefaultMarker : Marker
  one   instanceMain          : TypeExpr
  one   instanceClass         : QualifiedName
  many  instanceParameters    : TypeExpr
  many  instanceMethods       : FunctionDecl

PragmaDeclPayload
  one  pragmaKind    : L PragmaKind
  many pragmaTargets : IdentifierOccurrence

FieldDeclPayload
  one   fieldName        : IdentifierOccurrence
  one   fieldType        : TypeExpr
  maybe fieldInitializer : Expression

ContractMemberPayload.dataDecl
  one contractMemberData : DataDecl
ContractMemberPayload.typeAlias
  one contractMemberTypeAlias : TypeAliasDecl
ContractMemberPayload.field
  one contractMemberField : FieldDecl
ContractMemberPayload.function
  one contractMemberFunction : FunctionDecl
ContractMemberPayload.fallback
  one contractMemberFallback : FallbackDecl
ContractMemberPayload.constructor
  one contractMemberConstructor : ContractConstructorDecl

ContractDeclPayload
  one  contractName       : IdentifierOccurrence
  many contractParameters : IdentifierOccurrence
  many contractMembers    : ContractMember
```

Type inventory:

```text
TypeExprPayload.named
  one  typeNamedName      : QualifiedName
  many typeNamedArguments : TypeExpr
TypeExprPayload.proxy
  one typeProxyMarker : L Unit
  one typeProxyInner  : TypeExpr
TypeExprPayload.function
  one typeFunctionDomain   : TypeExpr
  one typeFunctionCodomain : TypeExpr
TypeExprPayload.tuple
  many typeTupleElements : TypeExpr
TypeExprPayload.group
  one typeGroupInner : TypeExpr
TypeExprPayload.comptime
  one typeComptimeMarker : Marker
  one typeComptimeInner  : TypeExpr
```

Literal spelling, decoded string content, syntax markers, pragma kinds,
operators, identifiers, path segments, external-library names, and the three
spans inside `AssemblySlice` are leaf payload data. They have no direct syntax
child beyond the universal located-payload transition.

Expression inventory:

```text
ExpressionPayload.name
  one expressionName : IdentifierOccurrence
ExpressionPayload.call
  one  expressionCallCallee    : Expression
  many expressionCallArguments : Expression
ExpressionPayload.select
  one expressionSelectReceiver : Expression
  one expressionSelectField    : IdentifierOccurrence
ExpressionPayload.dotConstructor
  one  expressionDotMarker    : L Unit
  one  expressionDotName      : IdentifierOccurrence
  many expressionDotArguments : Expression
ExpressionPayload.proxy
  one expressionProxyMarker : L Unit
  one expressionProxyType   : TypeExpr
ExpressionPayload.literal
  one expressionLiteral : Literal
ExpressionPayload.lambda
  many  expressionLambdaParameters : Parameter
  maybe expressionLambdaReturnType : TypeExpr
  one   expressionLambdaBody       : Body
ExpressionPayload.annotation
  one expressionAnnotationValue : Expression
  one expressionAnnotationType  : TypeExpr
ExpressionPayload.keywordConditional
  one expressionKeywordCondition : Expression
  one expressionKeywordThen      : Expression
  one expressionKeywordElse      : Expression
ExpressionPayload.ternaryConditional
  one expressionTernaryCondition : Expression
  one expressionTernaryThen      : Expression
  one expressionTernaryElse      : Expression
ExpressionPayload.index
  one expressionIndexReceiver : Expression
  one expressionIndexValue    : Expression
ExpressionPayload.prefix
  one expressionPrefixOperator : L PrefixOperator
  one expressionPrefixOperand  : Expression
ExpressionPayload.infix
  one expressionInfixLeft     : Expression
  one expressionInfixOperator : L InfixOperator
  one expressionInfixRight    : Expression
ExpressionPayload.tuple
  many expressionTupleElements : Expression
ExpressionPayload.group
  one expressionGroupInner : Expression
```

Call and select structure is retained exactly. Recognizing a dotted prefix as
a module, type, class, or contract qualifier is a later resolver judgment and
does not rewrite this tree.

Pattern inventory:

```text
PatternPayload.named
  one  patternNamedName      : QualifiedName
  many patternNamedArguments : Pattern
PatternPayload.dotConstructor
  one  patternDotMarker    : L Unit
  one  patternDotName      : IdentifierOccurrence
  many patternDotArguments : Pattern
PatternPayload.wildcard
  one patternWildcardMarker : Marker
PatternPayload.literal
  one patternLiteral : Literal
PatternPayload.comptime
  one patternComptimeMarker     : Marker
  one patternComptimeExpression : Expression
PatternPayload.tuple
  many patternTupleElements : Pattern
PatternPayload.group
  one patternGroupInner : Pattern
```

Whether a one-component named pattern is a binder or a visible same-name
constructor is not encoded by a different address. The later classification
refines the same site.

Body, loop, match, and statement inventory:

```text
BodyPayload
  many bodyStatements : Statement

LetBindingPayload
  one   letName           : IdentifierOccurrence
  maybe letComptimeMarker : Marker
  maybe letType           : TypeExpr
  maybe letInitializer    : Expression

ForInitItemPayload.letBinding
  one forInitLetBinding : LetBinding
ForInitItemPayload.assignment
  one forInitAssignmentLeft     : Expression
  one forInitAssignmentOperator : L AssignmentOperator
  one forInitAssignmentRight    : Expression
ForInitItemPayload.expression
  one forInitExpression : Expression

ForPostItemPayload.assignment
  one forPostAssignmentLeft     : Expression
  one forPostAssignmentOperator : L AssignmentOperator
  one forPostAssignmentRight    : Expression
ForPostItemPayload.expression
  one forPostExpression : Expression

MatchArmPayload
  many matchArmPatterns : Pattern
  one  matchArmBody     : Body

StatementPayload.assignment
  one statementAssignmentLeft     : Expression
  one statementAssignmentOperator : L AssignmentOperator
  one statementAssignmentRight    : Expression
StatementPayload.letBinding
  one statementLetBinding : LetBinding
StatementPayload.block
  one statementBlockBody : Body
StatementPayload.expression
  one statementExpression : Expression
StatementPayload.return
  maybe statementReturnValue : Expression
StatementPayload.match
  many statementMatchScrutinees : Expression
  many statementMatchArms       : MatchArm
StatementPayload.assembly
  one statementAssemblySlice : AssemblySlice
StatementPayload.ifThenElse
  one   statementIfCondition : Expression
  one   statementIfThenBody  : Body
  maybe statementIfElseBody  : Body
StatementPayload.forLoop
  many statementForInitializers : ForInitItem
  one  statementForCondition    : Expression
  many statementForPostItems    : ForPostItem
  one  statementForBody         : Body
```

The `LetBindingPayload` rows deliberately follow written source order: name,
then the optional `comptime` marker inside the type annotation, then the type,
then the initializer. The record-field display order in ADR-0015 does not
override this lexical order.

The `terminator` and `BodyOrigin` fields are retained `SourceSpan` metadata,
not located syntax nodes. Break and continue have only that metadata and no
recursive syntax child. No transition may be added for either field.

### Role ordering and source order

Raw addresses have structural equality but no context-free source-order
comparison: a singular field and a list element can occur in either lexical
order under different parent types. For a selected parent, `childOrdinal` is
the zero-based row position in its applicable inventory entry. An optional
absent child contributes no row instance; later children retain the ordinal of
their role, not a compacted runtime position. A list role contributes one row,
with its elements ordered by natural-number index.

Two valid addresses in one module are compared by walking their common path.
At the first different step, both steps have the same selected parent, so they
are ordered by `childOrdinal` and then list index. A proper prefix sorts first.
A virtual scope sorts after all concrete children at its site. Index-scoped
IDs first compare ADR-0014 `ModuleId`, then this valid-address order, then
their closed identity role. This comparator is defined only within one fixed
`IdentityKind`; this ADR exports no heterogeneous cross-family comparator.

The required theorem is:

```text
sourceOrder_compare_iff
  : compareValidAddress module left right = LT
    iff the first differing concrete sibling is earlier in the inventory,
        or the common list role has a smaller source index,
        or left is a proper prefix of right
```

Spans, payload text, map iteration, and proof terms do not break ties.

### Executable selection

The independent judgment and pure executor are:

```text
SelectsModule
  : Multi.CertifiedParsedModule -> StructuralAddress -> SelectedSite -> Prop

select?
  : Multi.CertifiedParsedModule -> StructuralAddress -> Option SelectedSite
```

`SelectedSite` is a closed syntax zipper containing the owning module,
selected AST sort, exact subtree view, primary located ancestor, and an
inductive chain of parent-field or list-membership evidence. It does not store
the input address as a second unchecked field. `siteAddress` derives an address
from that zipper. Distinct list memberships distinguish equal payload values at
different sites. The executor starts at `certified.module`, applies only the
inventory transitions, checks option presence and list bounds, and rejects any
step following a virtual scope. It does not dispatch through host runtime type
names.

The correspondence boundary is:

```text
select_sound
select_complete
selects_functional
selects_address_injective
child_inventory_complete
child_inventory_disjoint
role_inventory_exact
```

`selects_address_injective` states that selecting the same zipper site from two
addresses makes those addresses equal. It does not compare subtree values. Two
located wrappers can carry equal spans and equal payloads and still be
different sites. Inventory completeness is proved by induction over the
ADR-0015 AST types, not by checking an executor-generated list against itself.
`role_inventory_exact` states that every `DirectRole` and `ListRole`
constructor occurs in exactly one inventory entry and every concrete recursive
field has exactly one role.

### Virtual lexical scopes

A lexical scope need not be an AST node. It is a terminal virtual child of an
exact syntax site.

```text
ScopeAt
  : Multi.CertifiedParsedModule -> StructuralAddress -> ScopeRole -> Prop
```

The closed role-to-anchor categories are:

| Scope role | Exact anchor |
| --- | --- |
| `module` | empty address selecting the located parsed module |
| `dataParameters` | located `DataDecl` |
| `typeAliasParameters` | located `TypeAliasDecl` |
| `contractParameters` | located `ContractDecl` |
| `topFunctionGeneric` | `GenericPrefix` below a top function |
| `classGeneric` | `GenericPrefix` below a class |
| `classMethodGeneric` | `GenericPrefix` below a class method signature |
| `instanceGeneric` | `GenericPrefix` below an instance |
| `instanceMethodGeneric` | `GenericPrefix` below an instance method |
| `contractFunctionGeneric` | `GenericPrefix` below a contract function |
| `fallbackGeneric` | `GenericPrefix` below a fallback |
| `topFunctionParameters` | top-level `FunctionSignature` |
| `classMethodParameters` | class method `FunctionSignature` |
| `instanceMethodParameters` | instance method `FunctionSignature` |
| `contractFunctionParameters` | contract function `FunctionSignature` |
| `fallbackParameters` | located `FallbackDecl` |
| `contractConstructorParameters` | located `ContractConstructorDecl` |
| `lambdaParameters` | located lambda expression |
| `bodyEntry` | every located `Body` |
| `matchArmBindings` | every located `MatchArm` |
| `loopHeader` | the located `Statement` whose payload is `forLoop` |
| `sequentialContinuation` | a located let `Statement`, or the `LetBinding` below a located for-init let item |

The exact address and ancestry constructor schemas later in "Scope sites"
expand this table and add no role or anchor category. Those ancestry
requirements are part of `ScopeAt`; they are not resolver-supplied tags. A
nested data or type alias uses its ordinary parameter scope under the absolute
contract-member path. Class and instance outer generic scopes remain
structurally distinct from each method's generic and parameter scopes.

This ADR identifies sites, not lexical visibility. ADR-0017 must define scope
parentage using these sites. It cannot append anonymous integers or reuse a
body ID for every scope. Each let has its own continuation scope, so a later
let can shadow an earlier let while its initializer remains associated with
the preceding scope.

The two `sequentialContinuation` cases deliberately have different anchors.
An ordinary let uses its entire located `Statement`; a for-initializer let uses
the nested located `LetBinding`. `loopHeader` uses the entire located for-loop
`Statement`. These anchors are structural facts and are not replaced by the
let name, statement payload, or a synthesized zero-width position.

`ScopeAt` is sound and complete for a closed executable enumeration,
functional in its address and role, and has no children after its virtual
step.

### Module-local and index-scoped identities

The erased structural key is:

```text
SyntaxNodeKey = {
  module  : ModuleId,
  address : StructuralAddress
}
```

`IdentityKind` is `declaration`, `member`, `body`, `scope`, `localSite`, or
`occurrence`. Its role family is the following closed mapping:

```text
IdentityKind = declaration | member | body | scope | localSite | occurrence

IdentityRole declaration = DeclarationRole
IdentityRole member      = MemberRole
IdentityRole body        = BodyRole
IdentityRole scope       = ScopeRole
IdentityRole localSite   = LocalRole
IdentityRole occurrence  = OccurrenceRole

DeclarationRole =
  data | typeAlias | class | instance | contract | function

MemberRole =
  topDataConstructor | nestedData | nestedTypeAlias |
  nestedDataConstructor | contractField | classMethod |
  instanceMethod | contractFunction | contractFallback |
  contractConstructor

BodyRole =
  topFunction | instanceMethod | contractFunction | contractFallback |
  contractConstructor | lambda | block | conditionalThen |
  conditionalElse | loop | matchArm

LocalRole =
  dataParameter | typeAliasParameter | contractParameter |
  forallBinder | functionParameter | lambdaParameter |
  letBinder | forLetBinder | patternCandidate

OccurrenceRole =
  moduleReference | moduleRootMarker | modulePathComponent |
  externalLibraryComponent |
  importSourceName | importAliasSite | hiddenName |
  exportSourceName | exportConstructorName | exportAliasSite |
  pragmaTarget | boundedClassComponent | predicateClassComponent |
  instanceClassComponent | typeNameComponent |
  expressionName | selectField | dotConstructorName |
  patternNameComponent | patternDotConstructorName |
  prefixOperator | infixOperator | assignmentOperator | indexExpression
```

The module-local declarative family, whose constructors are enumerated below,
has the signature:

```text
SelectsIdentity
  : (M : Multi.CertifiedParsedModule)
    -> (K : IdentityKind)
    -> StructuralAddress
    -> IdentityRole K
    -> Prop
```

Module-local identities are indexed by the exact parser certificate:

```text
LocalSyntaxId (M : Multi.CertifiedParsedModule) (K : IdentityKind) = {
  address : StructuralAddress,
  role    : IdentityRole K,
  selects : SelectsIdentity M K address role
}

localKey : LocalSyntaxId M K -> SyntaxNodeKey
localKey id = {
  module  := M.file.id.toModuleId,
  address := id.address
}
```

Index selection is the unique module-local lift relation:

```text
SelectsIndexIdentity I K key role iff
  exists G,
    G member of I.modules and
    key.module = moduleId G and
    SelectsIdentity G.parsed K key.address role
```

Collection-scoped identities are indexed only by the policy-free module
index:

```text
SyntaxId (I : CertifiedModuleIndex) (K : IdentityKind) = {
  key     : SyntaxNodeKey,
  role    : IdentityRole K,
  selects : SelectsIndexIdentity I K key role
}

DeclarationId I = SyntaxId I declaration
MemberId      I = SyntaxId I member
BodyId        I = SyntaxId I body
ScopeId       I = SyntaxId I scope
LocalSiteId   I = SyntaxId I localSite
OccurrenceId  I = SyntaxId I occurrence
```

This index relation is not a second identity judgment. Strict module ordering
makes `G` unique, and the relation cannot select through a prepared module
absent from `I`.

```text
owningModule
  : SyntaxId I K -> { G : GraphReadyModule // G member of I.modules }
```

`owningModule` is the unique witness selected by the identity's module key;
its subtype proof is erased by proof irrelevance. There is no constructor from
`SyntaxNodeKey` alone.

### Exact identity-selection rules

The following address combinators are notation, not additional address
constructors:

```text
payloadOf(a)       = a ++ [locatedPayload]
fieldOf(a, role)   = a ++ [singular role]
elementOf(a,r,i)   = a ++ [indexed r i]
scopeOf(a, role)   = a ++ [virtualScope role]

topAt(i, role) =
  fieldOf(payloadOf(elementOf(payloadOf([]), moduleItems, i)), role)

contractMemberAt(contract, i, role) =
  fieldOf(payloadOf(elementOf(payloadOf(contract), contractMembers, i)), role)

dataConstructorAt(data, i) =
  elementOf(payloadOf(data), dataConstructors, i)

qualifiedComponentAt(name, i) =
  elementOf(payloadOf(name), qualifiedNameComponents, i)

functionSignatureAt(function) =
  fieldOf(payloadOf(function), functionSignature)

classMethodAt(classNode, i) =
  elementOf(payloadOf(classNode), classMethods, i)

classMethodSignatureAt(classNode, i) =
  fieldOf(payloadOf(classMethodAt(classNode, i)), classMethodSignature)

instanceMethodAt(instance, i) =
  elementOf(payloadOf(instance), instanceMethods, i)

contractFunctionAt(contract, i) =
  contractMemberAt(contract, i, contractMemberFunction)
```

Each notation denotes an address only when all option, constructor, and bounds
conditions in the child inventory hold. `SelectsIdentity` has exactly the
constructor schemas in the tables below. Each row requires
`SelectsModule M address site` for the displayed located node or virtual scope
and the displayed zipper ancestry. No general "the selected node has this
type" rule exists, and there are no constructors besides these rows.

#### Declaration sites

Each row below is one constructor schema of
`SelectsIdentity M declaration address role`; the displayed address is the
selected declaration wrapper.

| Role | Exact selected located node and ancestry |
| --- | --- |
| `data` | `topAt(i, topData)`, a `DataDecl` |
| `typeAlias` | `topAt(i, topTypeAlias)`, a `TypeAliasDecl` |
| `class` | `topAt(i, topClass)`, a `ClassDecl` |
| `instance` | `topAt(i, topInstance)`, an `InstanceDecl` |
| `contract` | `topAt(i, topContract)`, a `ContractDecl` |
| `function` | `topAt(i, topFunction)`, a `FunctionDecl` |

Imports, exports, and pragmas have structural addresses but no
`DeclarationRole`.

#### Member sites

Let `D = topAt(i, topData)`, `C = topAt(i, topClass)`,
`N = topAt(i, topInstance)`, and `K = topAt(i, topContract)`.
Each row is one constructor schema of
`SelectsIdentity M member address role`.

| Role | Exact selected located node and ancestry |
| --- | --- |
| `topDataConstructor` | `dataConstructorAt(D, j)`, a `DataConstructor` |
| `nestedData` | `contractMemberAt(K, j, contractMemberData)`, a `DataDecl` |
| `nestedTypeAlias` | `contractMemberAt(K, j, contractMemberTypeAlias)`, a `TypeAliasDecl` |
| `nestedDataConstructor` | `dataConstructorAt(contractMemberAt(K,j,contractMemberData), k)`, a `DataConstructor` |
| `contractField` | `contractMemberAt(K, j, contractMemberField)`, a `FieldDecl` |
| `classMethod` | `elementOf(payloadOf(C), classMethods, j)`, a `ClassMethodDecl` |
| `instanceMethod` | `elementOf(payloadOf(N), instanceMethods, j)`, a `FunctionDecl` |
| `contractFunction` | `contractMemberAt(K, j, contractMemberFunction)`, a `FunctionDecl` |
| `contractFallback` | `contractMemberAt(K, j, contractMemberFallback)`, a `FallbackDecl` |
| `contractConstructor` | `contractMemberAt(K, j, contractMemberConstructor)`, a `ContractConstructorDecl` |

#### Body sites

For a located `FunctionDecl` at `F`, define
`functionBodyAt(F) = fieldOf(payloadOf(F), functionBody)`. The exact body rules
are the constructor schemas of `SelectsIdentity M body address role`:

| Role | Exact selected located `Body` and ancestry |
| --- | --- |
| `topFunction` | `functionBodyAt(topAt(i, topFunction))` |
| `instanceMethod` | `functionBodyAt(instanceMethodAt(topAt(i, topInstance), j))` |
| `contractFunction` | `functionBodyAt(contractFunctionAt(topAt(i, topContract), j))` |
| `contractFallback` | `fieldOf(payloadOf(contractMemberAt(topAt(i,topContract),j,contractMemberFallback)), fallbackBody)` |
| `contractConstructor` | `fieldOf(payloadOf(contractMemberAt(topAt(i,topContract),j,contractMemberConstructor)), constructorBody)` |
| `lambda` | `fieldOf(payloadOf(E), expressionLambdaBody)` where `E` selects a located `ExpressionPayload.lambda` |
| `block` | `fieldOf(payloadOf(S), statementBlockBody)` where `S` selects a located `StatementPayload.block` |
| `conditionalThen` | `fieldOf(payloadOf(S), statementIfThenBody)` where `S` selects a located `StatementPayload.ifThenElse` |
| `conditionalElse` | the present `fieldOf(payloadOf(S), statementIfElseBody)` for that same statement constructor |
| `loop` | `fieldOf(payloadOf(S), statementForBody)` where `S` selects a located `StatementPayload.forLoop` |
| `matchArm` | `fieldOf(payloadOf(A), matchArmBody)` where `A` selects a located `MatchArm` |

#### Scope sites

`SelectsIdentity M scope address role` holds exactly when
`address = scopeOf(anchor, role)` and `ScopeAt M anchor role`. The following
schemas are the complete definition of `ScopeAt`; `present` includes the
option-presence proof required by the child inventory.

| Scope role | Exact located anchor schema |
| --- | --- |
| `module` | `[]`, the located `ParsedModuleV1` root |
| `dataParameters` | `D`, where `D = topAt(i, topData)` or `D = contractMemberAt(topAt(i, topContract), j, contractMemberData)` |
| `typeAliasParameters` | `T`, where `T = topAt(i, topTypeAlias)` or `T = contractMemberAt(topAt(i, topContract), j, contractMemberTypeAlias)` |
| `contractParameters` | `topAt(i, topContract)` |
| `topFunctionGeneric` | the present `functionGenericPrefix` below `functionSignatureAt(topAt(i, topFunction))` |
| `classGeneric` | the present `classGenericPrefix` below `topAt(i, topClass)` |
| `classMethodGeneric` | the present `functionGenericPrefix` below `classMethodSignatureAt(topAt(i, topClass), j)` |
| `instanceGeneric` | the present `instanceGenericPrefix` below `topAt(i, topInstance)` |
| `instanceMethodGeneric` | the present `functionGenericPrefix` below `functionSignatureAt(instanceMethodAt(topAt(i, topInstance), j))` |
| `contractFunctionGeneric` | the present `functionGenericPrefix` below `functionSignatureAt(contractFunctionAt(topAt(i, topContract), j))` |
| `fallbackGeneric` | the present `fallbackGenericPrefix` below `contractMemberAt(topAt(i, topContract), j, contractMemberFallback)` |
| `topFunctionParameters` | `functionSignatureAt(topAt(i, topFunction))` |
| `classMethodParameters` | `classMethodSignatureAt(topAt(i, topClass), j)` |
| `instanceMethodParameters` | `functionSignatureAt(instanceMethodAt(topAt(i, topInstance), j))` |
| `contractFunctionParameters` | `functionSignatureAt(contractFunctionAt(topAt(i, topContract), j))` |
| `fallbackParameters` | `contractMemberAt(topAt(i, topContract), j, contractMemberFallback)` |
| `contractConstructorParameters` | `contractMemberAt(topAt(i, topContract), j, contractMemberConstructor)` |
| `lambdaParameters` | any structurally selected located `Expression` whose payload is `lambda` |
| `bodyEntry` | any structurally selected located `Body` |
| `matchArmBindings` | any structurally selected located `MatchArm` below `statementMatchArms` of a match statement |
| `loopHeader` | any structurally selected located `Statement` whose payload is `forLoop` |
| `sequentialContinuation` | any structurally selected located let `Statement`, or the `LetBinding` below `forInitLetBinding` of a for-loop initializer |

"Structurally selected" in these recursive schemas means a
`SelectsModule` derivation from the module root with the stated payload
constructor and parent roles in its zipper; it does not quantify over a
detached AST value. A scope identity always selects the terminal
`virtualScope role` child. It never selects the anchor wrapper as a substitute.

#### Local-site ancestry and owners

The local-site rows below are exactly the constructor schemas of
`SelectsIdentity M localSite address role`; the owner column simultaneously
defines `HasLocalOwner` after lifting both sites to one index.

The generic-prefix contexts are exactly:

| Generic-prefix anchor `G` | Scope role at `G` |
| --- | --- |
| `functionGenericPrefix` below the signature of a top function | `topFunctionGeneric` |
| `classGenericPrefix` below a top class | `classGeneric` |
| `functionGenericPrefix` below a class-method signature | `classMethodGeneric` |
| `instanceGenericPrefix` below a top instance | `instanceGeneric` |
| `functionGenericPrefix` below an instance-method signature | `instanceMethodGeneric` |
| `functionGenericPrefix` below a contract-function signature | `contractFunctionGeneric` |
| `fallbackGenericPrefix` below a contract fallback | `fallbackGeneric` |

`genericRole(G)` is the partial function whose graph is exactly this table; it
is undefined for a `GenericPrefix` at any other ancestry. For any such `G`,
define:

```text
forallClauseAt(G) = fieldOf(payloadOf(G), genericPrefixForall)
forallAt(G, i) =
  elementOf(payloadOf(forallClauseAt(G)), forallClauseBinders, i)
```

The local-site and owner rules are exactly:

| Local role | Exact selected `IdentifierOccurrence` | Exact owner scope |
| --- | --- | --- |
| `dataParameter` | `elementOf(payloadOf(D), dataParameters, i)` for any top or nested `DataDecl` `D` | `scopeOf(D, dataParameters)` |
| `typeAliasParameter` | `elementOf(payloadOf(T), typeAliasParameters, i)` for any top or nested `TypeAliasDecl` `T` | `scopeOf(T, typeAliasParameters)` |
| `contractParameter` | `elementOf(payloadOf(K), contractParameters, i)` for a top contract `K` | `scopeOf(K, contractParameters)` |
| `forallBinder` | `fieldOf(payloadOf(forallAt(G,i)), forallBareBinder)` when bare, or `fieldOf(payloadOf(forallAt(G,i)), forallBoundedBinder)` when bounded | `scopeOf(G, genericRole(G))` from the context table |
| `functionParameter` | `fieldOf(payloadOf(P), parameterName)` for `P = elementOf(payloadOf(Q), functionParameters, i)` | `scopeOf(Q, parameterRole(Q))` from the callable table below |
| `functionParameter` | `fieldOf(payloadOf(P), parameterName)` for `P = elementOf(payloadOf(F), fallbackParameters, i)` | `scopeOf(F, fallbackParameters)` |
| `functionParameter` | `fieldOf(payloadOf(P), parameterName)` for `P = elementOf(payloadOf(C), constructorParameters, i)` | `scopeOf(C, contractConstructorParameters)` |
| `lambdaParameter` | `fieldOf(payloadOf(P), parameterName)` for `P = elementOf(payloadOf(E), expressionLambdaParameters, i)` and a lambda expression `E` | `scopeOf(E, lambdaParameters)` |
| `letBinder` | `fieldOf(payloadOf(B), letName)` for `B = fieldOf(payloadOf(S), statementLetBinding)` and a located let statement `S` | `scopeOf(S, sequentialContinuation)` |
| `forLetBinder` | `fieldOf(payloadOf(B), letName)` for `B = fieldOf(payloadOf(J), forInitLetBinding)` and a located for-init let item `J` | `scopeOf(B, sequentialContinuation)` |
| `patternCandidate` | `qualifiedComponentAt(fieldOf(payloadOf(P), patternNamedName), 0)` for a childless one-component named pattern `P` below match arm `A` | `scopeOf(A, matchArmBindings)` |

Here `D`, `T`, and `K` range over exactly the data, type-alias, and contract
anchor schemas in the scope table. A fallback `F` and contract constructor `C`
are exactly the corresponding `contractMemberAt` schemas. `Q` ranges over only
the four callable rows below; `E`, `S`, and a for-init item `J` require their
full `SelectsModule` zipper and displayed payload constructor. `A` is the
unique enclosing match arm witnessed by `patternChild` below.

The callable parameter contexts are exactly:

| Function-signature anchor `Q` | `parameterRole(Q)` |
| --- | --- |
| signature of a top function | `topFunctionParameters` |
| signature inside a `ClassMethodDecl` | `classMethodParameters` |
| signature of an instance method | `instanceMethodParameters` |
| signature of a contract function | `contractFunctionParameters` |

`parameterRole(Q)` is the partial function whose graph is exactly this table;
the fallback, contract-constructor, and lambda rows use their distinct anchors
and never call it.

For `patternCandidate`, "below match arm" is the least relation generated by
these cases and no others:

```text
patternChild(A, P)
  when P is an element of A.patterns

patternChild(A, child)
  when patternChild(A, parent) and child is an element of
  parent.named.arguments, parent.dotConstructor.arguments,
  or parent.tuple.elements

patternChild(A, child)
  when patternChild(A, parent) and child is parent.group.inner
```

The candidate itself must be `PatternPayload.named`, its qualified name must
have exactly one component, and its `arguments` option must be absent. A
written empty argument list is not admitted by ADR-0015 pattern syntax and no
other pattern form is a candidate.

The structural refinements exported by this ADR are exactly:

```text
UnconditionalLocalRole =
  dataParameter | typeAliasParameter | contractParameter |
  forallBinder | functionParameter | lambdaParameter |
  letBinder | forLetBinder

UnconditionalLocalRole.toLocalRole :
  UnconditionalLocalRole -> LocalRole

UnconditionalLocalSite I = {
  site : LocalSiteId I,
  role : UnconditionalLocalRole,
  exactRole : site.role = role.toLocalRole
}

PatternCandidateSite I = {
  site : LocalSiteId I,
  exactRole : site.role = patternCandidate
}
```

The injection `toLocalRole` maps every constructor to the identically named
`LocalRole` and has no `patternCandidate` case. `HasLocalOwner site scope` has
exactly the rows in the local-site table, including its pattern-candidate row.
The executable owner and introduction relation are exactly:

```text
HasLocalOwner : LocalSiteId I -> ScopeId I -> Prop

localOwner : LocalSiteId I -> ScopeId I

localOwner_spec :
  HasLocalOwner site scope iff
  scope = localOwner site

IntroducedAt
  : UnconditionalLocalSite I -> ScopeId I -> Prop

introducedAt_spec :
  IntroducedAt unconditional scope iff
  HasLocalOwner unconditional.site scope
```

`HasLocalOwner` is the independent relation whose constructors are the table
rows; `localOwner` is its executable function. `IntroducedAt` independently
copies exactly the eight non-pattern rows after refinement to
`UnconditionalLocalSite`, and `introducedAt_spec` connects the judgments. It
has no `patternCandidate` constructor. A `PatternCandidateSite` still has the
exact `matchArmBindings` owner from the table, but constructor-versus-binder
classification and any active binding identity belong entirely to ADR-0017.

#### Occurrence sites

The following helper relations are closed address schemas. Each displayed
field must exist under the payload constructor named by its role.

```text
moduleReferenceAt(R) iff exactly one of:
  R = fieldOf(payloadOf(topAt(i, topImport)),
              importModuleReference)
  R = fieldOf(payloadOf(topAt(i, topExport)),
              exportModuleReference)
  R = fieldOf(payloadOf(topAt(i, topExport)),
              exportFromModuleReference)
  R = fieldOf(payloadOf(X), exportAllFromModuleReference), where
      X = elementOf(payloadOf(L), localExportEntries, j) and
      L = fieldOf(payloadOf(topAt(i, topExport)), exportLocalSelection)

importNamedEntryAt(X) iff
  X = elementOf(payloadOf(S), importSelectionEntries, j), where
  S = fieldOf(U, importItemSelection) and
  U = fieldOf(payloadOf(topAt(i, topImport)), importMode)

exportItemAt(E) iff exactly one of:
  E = fieldOf(payloadOf(X), exportEntryItem), where
      X = elementOf(payloadOf(L), localExportEntries, j) and
      L = fieldOf(payloadOf(topAt(i, topExport)), exportLocalSelection)
  E = fieldOf(payloadOf(X), remoteExportItem), where
      X = elementOf(payloadOf(S), remoteExportEntries, j) and
      S = fieldOf(payloadOf(topAt(i, topExport)), exportFromSelection)
```

Occurrence selection has exactly the following constructor schemas of
`SelectsIdentity M occurrence address role`:

| Occurrence role | Exact selected located site and ancestry |
| --- | --- |
| `moduleReference` | `R` with `moduleReferenceAt(R)` |
| `moduleRootMarker` | `fieldOf(payloadOf(R), r)` with `moduleReferenceAt(R)` and `r` exactly `moduleLibraryMarker`, `moduleStandardMarker`, or `moduleExternalSigil` |
| `modulePathComponent` | `elementOf(payloadOf(R), r, j)` with `moduleReferenceAt(R)` and `r` exactly `moduleRelativeComponents`, `moduleLibraryTail`, `moduleStandardTail`, or `moduleExternalTail` |
| `externalLibraryComponent` | `fieldOf(payloadOf(R), moduleExternalLibrary)` with `moduleReferenceAt(R)` and external payload |
| `importSourceName` | `fieldOf(payloadOf(X), importNamedSource)` with `importNamedEntryAt(X)` and named payload |
| `importAliasSite` | present `fieldOf(U, importModuleAlias)` for a top import's module-mode `U`, or present `fieldOf(payloadOf(X), importNamedAlias)` with `importNamedEntryAt(X)` |
| `hiddenName` | `elementOf(payloadOf(H), hidingNames, j)`, where `H = fieldOf(U, importHidingClause)` for a top import's items-mode `U` |
| `exportSourceName` | `fieldOf(payloadOf(E), exportItemName)` with `exportItemAt(E)` |
| `exportConstructorName` | `elementOf(payloadOf(C), constructorNames, j)`, where `C = fieldOf(payloadOf(E), exportItemConstructors)` and `exportItemAt(E)` |
| `exportAliasSite` | present `fieldOf(payloadOf(topAt(i, topExport)), exportModuleAlias)` under module export mode |
| `pragmaTarget` | `elementOf(payloadOf(topAt(i, topPragma)), pragmaTargets, j)` |
| `boundedClassComponent` | `qualifiedComponentAt(Q, j)`, where `Q = fieldOf(payloadOf(B), forallBoundClass)` and `B` is a structurally selected bounded `ForallBinder` |
| `predicateClassComponent` | `qualifiedComponentAt(Q, j)`, where `Q = fieldOf(payloadOf(P), predicateClass)` and `P` is a structurally selected `Predicate` |
| `instanceClassComponent` | `qualifiedComponentAt(Q, j)`, where `Q = fieldOf(payloadOf(topAt(i, topInstance)), instanceClass)` |
| `typeNameComponent` | `qualifiedComponentAt(Q, j)`, where `Q = fieldOf(payloadOf(T), typeNamedName)` and `T` is a structurally selected named `TypeExpr` |
| `expressionName` | `fieldOf(payloadOf(E), expressionName)`, where `E` is a structurally selected name expression |
| `selectField` | `fieldOf(payloadOf(E), expressionSelectField)`, where `E` is a structurally selected select expression |
| `dotConstructorName` | `fieldOf(payloadOf(E), expressionDotName)`, where `E` is a structurally selected dot-constructor expression |
| `patternNameComponent` | `qualifiedComponentAt(Q, j)`, where `Q = fieldOf(payloadOf(P), patternNamedName)` and `P` is a structurally selected named pattern below a match arm |
| `patternDotConstructorName` | `fieldOf(payloadOf(P), patternDotName)`, where `P` is a structurally selected dot-constructor pattern below a match arm |
| `prefixOperator` | `fieldOf(payloadOf(E), expressionPrefixOperator)`, where `E` is a structurally selected prefix expression |
| `infixOperator` | `fieldOf(payloadOf(E), expressionInfixOperator)`, where `E` is a structurally selected infix expression |
| `assignmentOperator` | `fieldOf(payloadOf(F), forInitAssignmentOperator)` for a structurally selected assignment `ForInitItem` `F`; `fieldOf(payloadOf(P), forPostAssignmentOperator)` for an assignment `ForPostItem` `P`; or `fieldOf(payloadOf(S), statementAssignmentOperator)` for an assignment `Statement` `S` |
| `indexExpression` | the address `E` itself, where `E` is a structurally selected located expression with `ExpressionPayload.index` |

Here a top import's `U` is
`fieldOf(payloadOf(topAt(i, topImport)), importMode)`. A structurally selected
recursive node requires its full `SelectsModule` zipper from the parsed-module
root and the stated payload constructor. These clauses therefore include
nested type arguments, expressions, and patterns without admitting a detached
value or an occurrence in a different parent field.

No declaration name, member name, unconditional-local binder, literal,
wildcard, proxy marker, annotation colon, call delimiter, or index operand has
an `OccurrenceRole` merely because it is located.

ADR-0017 deferred sites are thereby closed as follows:

| Deferred form | Permitted occurrence role |
| --- | --- |
| receiver field or receiver method | `selectField` |
| leading-dot constructor | `dotConstructorName` |
| unqualified class-method fallback | `expressionName` |
| prefix operator | `prefixOperator` |
| infix operator | `infixOperator` |
| assignment operator | `assignmentOperator` |
| index operation | `indexExpression` |

A call whose callee is a select retains the select field's occurrence; no
second receiver-call occurrence is created. Later qualification or deferred
classification retains the same `OccurrenceId I` and never replaces its
address.

### Module-reference site and index lift

The graph-consumable site is exactly:

```text
Structural.ModuleReferenceSite (M : Multi.CertifiedParsedModule) =
  { site : LocalSyntaxId M occurrence //
      site.role = OccurrenceRole.moduleReference }
```

This dependent site is distinct from ADR-0015 `Multi.ModuleReferenceShape`,
the span-erased comparison value used only by parser structural diagnostics.
The shape value is never an identity or graph edge site.

`localKey site.site` is the certified absolute module-root key available to
graph discovery before any `CertifiedModuleIndex` exists. Its module component
comes from `M.file.id`; no target module or graph edge is part of the site.
Equality, source order, and `modulePrimarySpan` delegate to `site`; the
`moduleReference` role proof is erased.

`prepareGraphModule` enumerates one such key for every import/export module
reference, including each `allFrom` reference inside a local export list. The
keys are in structural source order. Multiple references inside one export
declaration do not collapse, and `std` differs from `std.std` even if later
rules ever map them to equal targets. A declaration ID is never an edge-site
key.

A later graph may retain the dependent pair
`(G : GraphReadyModule, Structural.ModuleReferenceSite G.parsed)`. Independently
of any graph, membership in a `CertifiedModuleIndex` defines:

```text
lift
  : (G : GraphReadyModule)
    -> G member of I.modules
    -> LocalSyntaxId G.parsed K
    -> SyntaxId I K
```

The required laws are:

```text
lift_key :
  (lift G membership local).key = localKey local

lift_role :
  (lift G membership local).role = local.role

lift_owner :
  owningModule (lift G membership local) = <G, membership>

lift_primarySpan :
  primarySpan (lift G membership local) = modulePrimarySpan local

lift_injective :
  lift G membership left = lift G membership right -> left = right

lift_eq_iff :
  lift G memberG left = lift H memberH right iff
    localKey left = localKey right and left.role = right.role

lift_unique :
  lift G memberProof1 local = lift G memberProof2 local

lift_covers_index_id :
  every SyntaxId I K has exactly one module-local preimage,
  modulo erased membership and selection proofs

indexIdentity_no_fabrication :
  eliminating SyntaxId I K requires that unique preimage
```

`lift_unique` erases the choice of membership proof and the proof component of
the same graph-ready module value.
`lift_covers_index_id` gives one unique module-local preimage for every
index-scoped identity; `indexIdentity_no_fabrication` is its eliminator form.
`lift_owner` returns the supplied graph-ready module, and `lift_eq_iff` reduces
equality of lifted values to equality of their module ID, absolute address, and
role. These laws permit a later graph site to become an index-scoped occurrence
without changing identity.

### Equality and comparison

Proof fields do not participate in equality. The executable erasures are:

```text
eraseLocal : LocalSyntaxId M K -> StructuralAddress * IdentityRole K
eraseIndex : SyntaxId I K -> SyntaxNodeKey * IdentityRole K

compareLocalSyntax : LocalSyntaxId M K -> LocalSyntaxId M K -> Ordering
compareIdentity    : SyntaxId I K -> SyntaxId I K -> Ordering

eraseUnconditional : UnconditionalLocalSite I -> LocalSiteId I
erasePatternCandidate : PatternCandidateSite I -> LocalSiteId I
```

Module-local equality is equality of `eraseLocal`; index-scoped equality is
equality of `eraseIndex`. Their `DecidableEq` instances and comparators inspect
only those erasures. The module-local comparator uses valid-address order and
then the displayed constructor order of `IdentityRole K`. The index comparator
first uses ADR-0014 `ModuleId` order and then the same two components.
The two local-site refinements compare their erased `LocalSiteId`; their role
proofs do not add an equality component.

Proof erasure is justified by proof irrelevance, `selects_functional`, unique
module membership, and the exhaustive functional role tables. Every family
proves:

```text
eraseLocal_injective
eraseIndex_injective
eraseUnconditional_injective
erasePatternCandidate_injective

identity_key_injective
  : left.key = right.key -> left.role = right.role -> left = right

compareLocalSyntax_eq_iff_eq
compareIdentity_eq_iff_eq
compareIdentity_lt_iff_sourceOrder
```

The comparator follows the valid-address order above. No identity is compared
across different module indices. A later wire format may erase the index only
if it also supplies enough certified-module-index evidence to recheck the key.

### Total primary spans

Every identity has one total primary span obtained by structural selection,
never by searching equal text.

```text
modulePrimarySpan : LocalSyntaxId M K -> Multi.SourceSpan
primarySpan       : SyntaxId I K -> Multi.SourceSpan
```

The declaration mapping is exact:

| Declaration role | Primary located value |
| --- | --- |
| `data` | the selected `DataDecl.name` identifier reached by `dataName` |
| `typeAlias` | the selected `TypeAliasDecl.name` identifier reached by `typeAliasName` |
| `class` | the selected `ClassDecl.className` identifier |
| `instance` | the complete selected `InstanceDecl` |
| `contract` | the selected `ContractDecl.name` identifier reached by `contractName` |
| `function` | the selected top function signature's `name` reached by `functionName` |

The member mapping is exact:

| Member role | Primary located value |
| --- | --- |
| `topDataConstructor`, `nestedDataConstructor` | the selected constructor's `name` reached by `dataConstructorName` |
| `nestedData` | the selected nested declaration's `name` reached by `dataName` |
| `nestedTypeAlias` | the selected nested declaration's `name` reached by `typeAliasName` |
| `contractField` | the selected field's `name` reached by `fieldName` |
| `classMethod` | the selected class method signature's `name` reached by `functionName` |
| `instanceMethod`, `contractFunction` | the selected function signature's `name` reached by `functionName` |
| `contractFallback` | the selected fallback's `marker` reached by `fallbackMarker` |
| `contractConstructor` | the selected constructor's `marker` reached by `constructorMarker` |

Every `BodyId` uses the complete selected located `Body`. Every `ScopeId` uses
the complete located anchor in its exact `ScopeAt` derivation. Consequently,
module scope uses the parsed-module span, an ordinary-let
`sequentialContinuation` uses the whole located `Statement`, a for-init-let
`sequentialContinuation` uses its nested located `LetBinding`, and
`loopHeader` uses the whole located for-loop `Statement`.

Every `LocalSiteId` uses its selected binder or candidate
`IdentifierOccurrence`. Every `OccurrenceId` uses its selected located value.
Thus a module-reference occurrence uses the whole `ModuleReference`; markers,
components, names, and aliases use their exact located lexemes; prefix, infix,
and assignment operators use their exact located operator lexemes; and an
`indexExpression` uses the whole located index expression, including receiver,
brackets, and index operand.

The required theorems are:

```text
modulePrimarySpan_source
  : (modulePrimarySpan id).source = M.file.id

primarySpan_source
  : (primarySpan id).source.toModuleId = id.key.module

primarySpan_valid
  : let graphModule := (owningModule id).val
    let file := graphModule.parsed.file
    let span := primarySpan id
    span.source = file.id and
    span.startByte <= span.endByte and
    span.endByte <= file.content.toUTF8.size
```

Together with `lift_primarySpan` above, these make the mapping total both before
and after index formation. Overlapping or equal spans do not make identities
equal.

### Non-dangling and injective laws

Every public identity proves selection in one unique member of its exact
`CertifiedModuleIndex`. Every identity family provides:

```text
identity_nonDangling
identity_module_unique
identity_role_functional
identity_address_injective
identity_primary_functional
```

`identity_nonDangling` exhibits the indexed module and its selection
derivation. `identity_address_injective` states that equal selected sites have
equal absolute addresses. Different identity families require an explicit
proved refinement even when they refer to the same syntax wrapper. No public
constructor accepts an unchecked `SyntaxNodeKey`.

### Exact finite measures

The structural layer defines these executable measures:

```text
nodeMeasure : Multi.CertifiedParsedModule -> Nat
scopeMeasure : Multi.CertifiedParsedModule -> Nat
occurrenceMeasure : Multi.CertifiedParsedModule -> Nat
maxAddressDepth : Multi.CertifiedParsedModule -> Nat

structuralNodeMeasure node =
  1 + sum (structuralNodeMeasure child)
      for every concrete child in inventory order

nodeMeasure module =
  structuralNodeMeasure module.module

scopeMeasure module =
  cardinality of pairs (anchor, role) satisfying ScopeAt module anchor role

occurrenceMeasure module =
  cardinality of pairs (address, role) satisfying
    SelectsIdentity module occurrence address role

maxAddressDepth module =
  maximum length of every address accepted by select? module

indexNodeMeasure I =
  sum (nodeMeasure G.parsed) for G in I.modules

indexScopeMeasure I =
  sum (scopeMeasure G.parsed) for G in I.modules

indexOccurrenceMeasure I =
  sum (occurrenceMeasure G.parsed) for G in I.modules

allNodes : (M : Multi.CertifiedParsedModule) -> List SelectedSite
allScopes : (I : CertifiedModuleIndex) -> List (ScopeId I)
allLocalSites : (I : CertifiedModuleIndex) -> List (LocalSiteId I)
allUnconditionalLocalSites :
  (I : CertifiedModuleIndex) -> List (UnconditionalLocalSite I)
allPatternCandidateSites :
  (I : CertifiedModuleIndex) -> List (PatternCandidateSite I)
allOccurrences : (I : CertifiedModuleIndex) -> List (OccurrenceId I)
```

`structuralNodeMeasure` counts every actual located wrapper, its actual payload,
every unlocated import-mode value, and every retained located leaf. It does not
count `Option`, `List`, or `NonemptyList` containers; primitive leaf fields;
token and trivia evidence; `SourceSpan` metadata; or virtual scopes. It
introduces no constructor-payload tuple absent from ADR-0015. The empty maximum
for an impossible empty selectable set is zero; every certified module has at
least its root, so its `maxAddressDepth` is attained.

`occurrenceMeasure` counts the complete module-reference site and each exact
component, name, operator, and index-expression site selected by
`OccurrenceRole`. A later classification does not add another occurrence.
Index measures use the strict ascending `ModuleId` order stored in `I`.

`allNodes M` enumerates the selectable concrete sites of module `M` in valid
address order. For an index `I`, `allScopes I`, `allLocalSites I`,
`allUnconditionalLocalSites I`, `allPatternCandidateSites I`, and
`allOccurrences I` enumerate their proof-carrying public identity types in
index source order. Every list is sorted and duplicate-free. The two refined
local-site lists form an exact disjoint partition of `allLocalSites I`. The
boundary proves:

```text
length_allNodes_eq_nodeMeasure
length_allScopes_eq_indexScopeMeasure
length_allOccurrences_eq_indexOccurrenceMeasure
address_length_le_maxAddressDepth
enumeration_sound
enumeration_complete
```

These are semantic-demand measures, not wall-clock, heap, compiler, or host-map
claims. A later phase may use them only after all of its input components are
available and its exact recurrence is stated.

### Construction boundary and diagnostics

The permitted construction order is:

1. ADR-0015 returns `Multi.CertifiedParsedModule` for one file chosen by a
   caller.
2. `prepareGraphModule` constructs its complete certified module-reference
   list.
3. `CertifiedModuleIndex.ofUnique` canonically indexes any caller-proved
   distinct collection of prepared modules.
4. Consumers use local identities before index construction and lifted
   index-scoped identities afterward.

This order does not say which files a caller chooses, which module references
resolve, or which modules are reachable. ADR-0017 owns those decisions and may
wrap the resulting index with its graph proofs.

There is no later address-validation phase and no `malformedAddress`,
`illFormedAddress`, or equivalent source diagnostic. A failed internal
identity invariant is an implementation defect, not behavior attributed to
source text.

### Required proof boundary

The implementation must provide independent
judgments and pure executors for selection, scope sites, identity refinements,
enumeration, and lift. At minimum it proves:

```text
prepareGraphModule_exact
prepareGraphModule_parsed
moduleIndex_sorted
moduleIndex_membership_iff
moduleIndex_moduleId_unique
moduleIndex_canonical
select_sound
select_complete
selects_functional
selects_address_injective
child_inventory_complete
child_inventory_disjoint
role_inventory_exact
scopeAt_sound_complete
scopeAt_functional
declarationSelection_iff
memberSelection_iff
bodySelection_iff
scopeSelection_iff
localSiteSelection_iff
occurrenceSelection_iff
hasLocalOwner_iff_table
local_owner_functional
localOwner_spec
introducedAt_spec
localSite_partition
eraseLocal_injective
eraseIndex_injective
eraseUnconditional_injective
erasePatternCandidate_injective
identity_key_injective
identity_nonDangling
identity_module_unique
identity_role_functional
identity_address_injective
identity_primary_functional
compareLocalSyntax_eq_iff_eq
compareIdentity_eq_iff_eq
compareIdentity_lt_iff_sourceOrder
modulePrimarySpan_source
primarySpan_source
primarySpan_valid
sourceOrder_compare_iff
moduleReferences_sound_complete
moduleReferences_nodup
moduleReferences_sourceOrdered
lift_key
lift_role
lift_owner
lift_primarySpan
lift_injective
lift_eq_iff
lift_unique
lift_covers_index_id
indexIdentity_no_fabrication
enumeration_sound
enumeration_complete
length_allNodes_eq_nodeMeasure
length_allScopes_eq_indexScopeMeasure
length_allOccurrences_eq_indexOccurrenceMeasure
address_length_le_maxAddressDepth
```

Executor soundness cannot be defined as the executor returning its own result,
and completeness cannot assume a resolver output. The declarative relations
recurse over the closed ADR-0015 syntax constructors. Public theorem assumption
audits may contain only the standard proof principles already allowed by the
repository policy.

### Implementation slices after acceptance

Acceptance authorizes only these additive internal modules, or an equivalent
acyclic split with the same public boundary:

```text
Solcore/Surface/Multi/Structural/Role.lean
Solcore/Surface/Multi/Structural/Address.lean
Solcore/Surface/Multi/Structural/Judgment.lean
Solcore/Surface/Multi/Structural/Selection.lean
Solcore/Surface/Multi/Structural/Scope.lean
Solcore/Surface/Multi/Structural/ModuleLocal.lean
Solcore/Surface/Multi/Structural/PreparedModule.lean
Solcore/Surface/Multi/Structural/Index.lean
Solcore/Surface/Multi/Structural/Identity.lean
Solcore/Surface/Multi/Structural/Measure.lean
Solcore/Surface/Multi/Structural/Properties.lean
Solcore/Surface/Multi/Structural.lean
```

The dependency direction is ADR-0015 syntax/certification, roles and
addresses, independent judgments, executors and scopes, module-local
identities, prepared modules, the policy-free index, index-scoped identities
and lift, measures, then properties. Resolver graph policy, interface
saturation, lexical visibility, target selection, standard-bundle assembly,
SHA-256, publication, and Core elaboration are outside this authorization.

### Explicit exclusions

This ADR does not decide:

- module-reference target semantics;
- root selection, source edges, graph closure, or reachability;
- import, export, constructor-visibility, or interface fixed-point rules;
- scope-to-scope lexical parentage, visibility, shadowing priority, or
  namespace collisions;
- pattern constructor-versus-binder classification or active binding identity;
- intrinsic targets or standard-library byte verification;
- resolver diagnostics, type checking, or elaboration;
- identity serialization or stable external numbering; or
- publication of any language, profile, schema, capability, or Oracle query.

A later layer may refine a certified identity with semantic target evidence,
but it cannot replace its absolute module-root address.

## Consequences

- Every module-reference site exported from a prepared module is certified.
- Module collection is canonical without choosing roots or reachability.
- Multiple module references inside one declaration remain distinct.
- Structural equality is independent of text, span equality, compiler
  allocation, and map order.
- Virtual scope identities cover generic, callable, body, arm, loop, lambda,
  and sequential-let sites without pretending each scope is an AST node.
- Unconditional local sites and pattern candidates are structurally distinct,
  while active pattern binding remains a resolver refinement.
- Exact primary spans need no text search.
- Audited node, scope, occurrence, and depth measures are available to later
  finite-universe and termination arguments.
- Extending the parser AST requires an explicit update to this closed
  inventory.

## Recorded acceptance gates and ongoing conformance

The Accepted decision records the following review and implementation gates.
Acceptance authorizes work; it does not assert that the absent Structural
implementation already satisfies them:

1. ADR-0015 is Accepted; any implementation must consume the exact AST
   referenced here.
2. The canonical six-file standard parse gate and pinned compatibility fixtures
   required by ADR-0015 must pass before Structural implementation is complete.
3. An independent traversal review must enumerate every recursive ADR-0015 AST
   field and confirm exactly one inventory entry.
4. An independent scope review must cover class and instance outer generics in
   methods, contract parameters in nested members, callable and lambda
   parameters, body and arm sites, loop initializers, and sequential lets.
5. An independent identity review must confirm that
   `Structural.ModuleReferenceSite` is module-local, `CertifiedModuleIndex`
   has no graph policy, and `lift` preserves the reference site without
   declaration-level collapse.
6. A primary-span review must confirm every declaration/member binder or
   marker, every operator lexeme, the whole index-expression span, and the
   exact ordinary-let, for-init-let, and loop-header anchors.
7. Implementation files may now be added because the ADR is Accepted, but only
   against the completed, reviewed ADR-0015 `CertifiedParsedModule` boundary.

After acceptance, each implementation slice must pass the full build and test
suite, metadata validation, repository English-text checks, formatting checks,
semantic-kernel policy checks, and public-theorem assumption audits before its
logical commit is made.
