import Solcore.Surface.Multi.Measure

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- Every source location retained by an AST and every direct containment edge. -/
structure LocationInventory where
  spans : List SourceSpan
  containments : List (SourceSpan × SourceSpan)
  deriving Repr, BEq, DecidableEq

/--
An internal traversal result. `roots` are exactly the locations that an
enclosing located wrapper must contain directly.
-/
private structure LocationFragment where
  roots : List SourceSpan
  inventory : LocationInventory

/-- Exhaustive audit anchor for the 54 location-bearing carrier sorts. -/
private def AstCarrierSort.hasLocatedWrapper : AstCarrierSort → Bool
  | .importMode => false
  | .parsedModule
  | .topItem
  | .qualifiedName
  | .identifier
  | .pathComponent
  | .externalLibraryName
  | .syntaxMarker
  | .unitMarker
  | .moduleReference
  | .importSelectorEntry
  | .importSelection
  | .hidingClause
  | .importDecl
  | .constructorSelection
  | .exportItem
  | .exportEntry
  | .localExportList
  | .remoteExportEntry
  | .remoteExportSelection
  | .exportMode
  | .forallBinder
  | .forallClause
  | .predicate
  | .genericPrefix
  | .parameter
  | .functionSignature
  | .classMethodDecl
  | .functionDecl
  | .fallbackDecl
  | .contractConstructorDecl
  | .dataConstructor
  | .dataDecl
  | .typeAliasDecl
  | .classDecl
  | .instanceDecl
  | .pragmaKind
  | .pragmaDecl
  | .fieldDecl
  | .contractMember
  | .contractDecl
  | .literal
  | .typeExpr
  | .prefixOperator
  | .infixOperator
  | .assignmentOperator
  | .expression
  | .pattern
  | .body
  | .letBinding
  | .forInitItem
  | .forPostItem
  | .matchArm
  | .statement
  | .assemblySlice => true

private def emptyFragment : LocationFragment := {
  roots := []
  inventory := {
    spans := []
    containments := []
  }
}

/-- Merge sibling fragments without introducing a containment edge. -/
private def mergeFragments (fragments : List LocationFragment) :
    LocationFragment := {
  roots := fragments.flatMap (fun fragment => fragment.roots)
  inventory := {
    spans := fragments.flatMap (fun fragment => fragment.inventory.spans)
    containments := fragments.flatMap
      (fun fragment => fragment.inventory.containments)
  }
}

/-- One raw span, exposed as a direct child root of its containing wrapper. -/
private def rawFragment (span : SourceSpan) : LocationFragment := {
  roots := [span]
  inventory := {
    spans := [span]
    containments := []
  }
}

/--
Create one located wrapper and connect it to every root of its child fragments.
-/
private def locatedFragment (span : SourceSpan)
    (children : List LocationFragment) : LocationFragment :=
  let merged := mergeFragments children
  {
    roots := [span]
    inventory := {
      spans := span :: merged.inventory.spans
      containments :=
        merged.roots.map (fun child => (span, child)) ++
          merged.inventory.containments
    }
  }

/--
Create a located wrapper while exposing selected raw locations to its parent.
This is used only for a match-arm body: the arm, rather than the body, directly
contains the written fat arrow.
-/
private def locatedFragmentWithPromotedRoots (span : SourceSpan)
    (promoted : List SourceSpan) (children : List LocationFragment) :
    LocationFragment :=
  let merged := mergeFragments children
  {
    roots := span :: promoted
    inventory := {
      spans := span :: promoted ++ merged.inventory.spans
      containments :=
        merged.roots.map (fun child => (span, child)) ++
          merged.inventory.containments
    }
  }

private def listFragment {alpha : Type}
    (visit : alpha → LocationFragment) (values : List alpha) :
    LocationFragment :=
  mergeFragments (values.map visit)

private def optionFragment {alpha : Type}
    (visit : alpha → LocationFragment) : Option alpha → LocationFragment
  | none => emptyFragment
  | some value => visit value

private def nonemptyFragment {alpha : Type}
    (visit : alpha → LocationFragment) (values : NonemptyList alpha) :
    LocationFragment :=
  mergeFragments [visit values.head, listFragment visit values.tail]

private def rawOptionFragment : Option SourceSpan → LocationFragment
  | none => emptyFragment
  | some span => rawFragment span

private def identifierFragment (identifier : IdentifierOccurrence) :
    LocationFragment :=
  locatedFragment identifier.span []

private def pathComponentFragment (component : PathComponent) :
    LocationFragment :=
  locatedFragment component.span []

private def externalLibraryNameFragment
    (name : Located ExternalLibraryName) : LocationFragment :=
  locatedFragment name.span []

private def markerFragment (marker : Marker) : LocationFragment :=
  locatedFragment marker.span []

private def unitMarkerFragment (marker : Located Unit) : LocationFragment :=
  locatedFragment marker.span []

private def pragmaKindFragment (kind : Located PragmaKind) : LocationFragment :=
  locatedFragment kind.span []

private def prefixOperatorFragment (operator : Located PrefixOperator) :
    LocationFragment :=
  locatedFragment operator.span []

private def infixOperatorFragment (operator : Located InfixOperator) :
    LocationFragment :=
  locatedFragment operator.span []

private def assignmentOperatorFragment
    (operator : Located AssignmentOperator) : LocationFragment :=
  locatedFragment operator.span []

private def qualifiedNameFragment (name : QualifiedName) : LocationFragment :=
  locatedFragment name.span [
    nonemptyFragment identifierFragment name.payload.components
  ]

private def moduleReferenceFragment (reference : ModuleReference) :
    LocationFragment :=
  let children :=
    match reference.payload with
    | .relative components =>
        [nonemptyFragment pathComponentFragment components]
    | .libraryRoot marker tail =>
        [markerFragment marker,
          nonemptyFragment pathComponentFragment tail]
    | .standard marker tail =>
        [markerFragment marker, listFragment pathComponentFragment tail]
    | .external atMarker library tail =>
        [markerFragment atMarker, externalLibraryNameFragment library,
          nonemptyFragment pathComponentFragment tail]
  locatedFragment reference.span children

private def importSelectorEntryFragment (entry : ImportSelectorEntry) :
    LocationFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => [markerFragment marker]
    | .named source alias =>
        [identifierFragment source, optionFragment identifierFragment alias]
  locatedFragment entry.span children

private def importSelectionFragment (selection : ImportSelection) :
    LocationFragment :=
  locatedFragment selection.span [
    listFragment importSelectorEntryFragment selection.payload.entries
  ]

private def hidingClauseFragment (clause : HidingClause) : LocationFragment :=
  locatedFragment clause.span [
    listFragment identifierFragment clause.payload.names
  ]

/-- `ImportMode` has no wrapper; its located children remain direct roots. -/
private def importModeFragment : ImportMode → LocationFragment
  | .module alias => optionFragment identifierFragment alias
  | .items selection hidingClause =>
      mergeFragments [
        importSelectionFragment selection,
        optionFragment hidingClauseFragment hidingClause
      ]

private def importDeclFragment (declaration : ImportDecl) : LocationFragment :=
  locatedFragment declaration.span [
    moduleReferenceFragment declaration.payload.moduleRef,
    importModeFragment declaration.payload.mode
  ]

private def constructorSelectionFragment
    (selection : ConstructorSelection) : LocationFragment :=
  let children :=
    match selection.payload with
    | .all marker => [markerFragment marker]
    | .named constructors =>
        [nonemptyFragment identifierFragment constructors]
  locatedFragment selection.span children

private def exportItemFragment (item : ExportItem) : LocationFragment :=
  locatedFragment item.span [
    identifierFragment item.payload.name,
    optionFragment constructorSelectionFragment item.payload.constructors
  ]

private def exportEntryFragment (entry : ExportEntry) : LocationFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => [markerFragment marker]
    | .item item => [exportItemFragment item]
    | .allFrom moduleRef marker =>
        [moduleReferenceFragment moduleRef, markerFragment marker]
  locatedFragment entry.span children

private def localExportListFragment (selection : LocalExportList) :
    LocationFragment :=
  locatedFragment selection.span [
    listFragment exportEntryFragment selection.payload.entries
  ]

private def remoteExportEntryFragment (entry : RemoteExportEntry) :
    LocationFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => [markerFragment marker]
    | .item item => [exportItemFragment item]
  locatedFragment entry.span children

private def remoteExportSelectionFragment
    (selection : RemoteExportSelection) : LocationFragment :=
  let children :=
    match selection.payload with
    | .dotWildcard marker => [markerFragment marker]
    | .braced entries => [listFragment remoteExportEntryFragment entries]
  locatedFragment selection.span children

private def exportDeclFragment (declaration : ExportDecl) : LocationFragment :=
  let children :=
    match declaration.payload with
    | .local selection => [localExportListFragment selection]
    | .module moduleRef alias =>
        [moduleReferenceFragment moduleRef,
          optionFragment identifierFragment alias]
    | .from moduleRef selection =>
        [moduleReferenceFragment moduleRef,
          remoteExportSelectionFragment selection]
  locatedFragment declaration.span children

private def literalFragment (literal : Literal) : LocationFragment :=
  locatedFragment literal.span []

mutual

private def typeExprFragment (typeExpression : TypeExpr) : LocationFragment :=
  match typeExpression with
  | ⟨span, payload⟩ =>
      let children :=
        match payload with
        | .named name arguments =>
            [qualifiedNameFragment name, typeExprArgumentsFragment arguments]
        | .proxy marker inner =>
            [unitMarkerFragment marker, typeExprFragment inner]
        | .function domain codomain =>
            [typeExprFragment domain, typeExprFragment codomain]
        | .tuple elements => [typeExprListFragment elements]
        | .group inner => [typeExprFragment inner]
        | .comptime marker inner =>
            [markerFragment marker, typeExprFragment inner]
      locatedFragment span children

private def typeExprArgumentsFragment :
    Option (NonemptyList TypeExpr) → LocationFragment
  | none => emptyFragment
  | some arguments => typeExprNonemptyFragment arguments

private def typeExprNonemptyFragment :
    NonemptyList TypeExpr → LocationFragment
  | ⟨head, tail⟩ =>
      mergeFragments [typeExprFragment head, typeExprListFragment tail]

private def typeExprListFragment : List TypeExpr → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [typeExprFragment head, typeExprListFragment tail]

end

private def forallBinderFragment (binder : ForallBinder) : LocationFragment :=
  let children :=
    match binder.payload with
    | .bare name => [identifierFragment name]
    | .bounded name className arguments =>
        [identifierFragment name, qualifiedNameFragment className,
          optionFragment
            (nonemptyFragment typeExprFragment)
            arguments]
  locatedFragment binder.span children

private def forallClauseFragment (clause : ForallClause) : LocationFragment :=
  locatedFragment clause.span [
    nonemptyFragment forallBinderFragment clause.payload.binders
  ]

private def predicateFragment (predicate : Predicate) : LocationFragment :=
  locatedFragment predicate.span [
    typeExprFragment predicate.payload.main,
    qualifiedNameFragment predicate.payload.className,
    optionFragment
      (nonemptyFragment typeExprFragment)
      predicate.payload.parameters
  ]

private def genericPrefixFragment (genericPrefix : GenericPrefix) :
    LocationFragment :=
  locatedFragment genericPrefix.span [
    forallClauseFragment genericPrefix.payload.forallClause,
    optionFragment
      (nonemptyFragment predicateFragment)
      genericPrefix.payload.context
  ]

private def parameterFragment (parameter : Parameter) : LocationFragment :=
  locatedFragment parameter.span [
    optionFragment markerFragment parameter.payload.comptime,
    identifierFragment parameter.payload.name,
    optionFragment typeExprFragment parameter.payload.type
  ]

private def functionSignatureFragment (signature : FunctionSignature) :
    LocationFragment :=
  locatedFragment signature.span [
    optionFragment genericPrefixFragment signature.payload.genericPrefix,
    optionFragment markerFragment signature.payload.public,
    optionFragment markerFragment signature.payload.payable,
    identifierFragment signature.payload.name,
    listFragment parameterFragment signature.payload.parameters,
    optionFragment typeExprFragment signature.payload.returnType
  ]

private def assemblySliceFragment (slice : AssemblySlice) : LocationFragment :=
  locatedFragment slice.span [
    rawFragment slice.payload.openBrace,
    rawFragment slice.payload.contents,
    rawFragment slice.payload.closeBrace
  ]

private structure BodyFragmentParts where
  promoted : List SourceSpan
  children : LocationFragment

mutual

private def expressionPayloadFragment : ExpressionPayload → LocationFragment
  | .name name => identifierFragment name
  | .call callee arguments =>
      mergeFragments [expressionFragment callee,
        expressionListFragment arguments]
  | .select receiver field =>
      mergeFragments [expressionFragment receiver, identifierFragment field]
  | .dotConstructor marker name arguments =>
      mergeFragments [unitMarkerFragment marker, identifierFragment name,
        expressionListOptionFragment arguments]
  | .proxy marker typeExpression =>
      mergeFragments [unitMarkerFragment marker,
        typeExprFragment typeExpression]
  | .literal literal => literalFragment literal
  | .lambda parameters returnType body =>
      mergeFragments [listFragment parameterFragment parameters,
        optionFragment typeExprFragment returnType, bodyFragment body]
  | .annotation inner typeExpression =>
      mergeFragments [expressionFragment inner,
        typeExprFragment typeExpression]
  | .keywordConditional condition thenBranch elseBranch =>
      mergeFragments [expressionFragment condition,
        expressionFragment thenBranch, expressionFragment elseBranch]
  | .ternaryConditional condition thenBranch elseBranch =>
      mergeFragments [expressionFragment condition,
        expressionFragment thenBranch, expressionFragment elseBranch]
  | .index receiver index =>
      mergeFragments [expressionFragment receiver, expressionFragment index]
  | .prefix operator operand =>
      mergeFragments [prefixOperatorFragment operator,
        expressionFragment operand]
  | .infix operator left right =>
      mergeFragments [infixOperatorFragment operator,
        expressionFragment left, expressionFragment right]
  | .tuple elements => expressionListFragment elements
  | .group inner => expressionFragment inner

private def patternPayloadFragment : PatternPayload → LocationFragment
  | .named name arguments =>
      mergeFragments [qualifiedNameFragment name,
        patternArgumentsFragment arguments]
  | .dotConstructor marker name arguments =>
      mergeFragments [unitMarkerFragment marker, identifierFragment name,
        patternArgumentsFragment arguments]
  | .wildcard marker => markerFragment marker
  | .literal literal => literalFragment literal
  | .comptime marker expression =>
      mergeFragments [markerFragment marker, expressionFragment expression]
  | .tuple elements => patternListFragment elements
  | .group inner => patternFragment inner

private def bodyPayloadFragment : BodyPayload → BodyFragmentParts
  | ⟨origin, statements⟩ =>
      match origin with
      | .braced openBrace closeBrace => {
          promoted := []
          children := mergeFragments [
            rawFragment openBrace,
            rawFragment closeBrace,
            statementListFragment statements
          ]
        }
      | .matchArm fatArrow => {
          promoted := [fatArrow]
          children := statementListFragment statements
        }

private def letBindingPayloadFragment :
    LetBindingPayload → LocationFragment
  | ⟨comptime, name, typeExpression, initializer⟩ =>
      mergeFragments [optionFragment markerFragment comptime,
        identifierFragment name, optionFragment typeExprFragment typeExpression,
        expressionOptionFragment initializer]

private def forInitItemPayloadFragment :
    ForInitItemPayload → LocationFragment
  | .letBinding binding => letBindingFragment binding
  | .assignment operator left right =>
      mergeFragments [assignmentOperatorFragment operator,
        expressionFragment left, expressionFragment right]
  | .expression expression => expressionFragment expression

private def forPostItemPayloadFragment :
    ForPostItemPayload → LocationFragment
  | .assignment operator left right =>
      mergeFragments [assignmentOperatorFragment operator,
        expressionFragment left, expressionFragment right]
  | .expression expression => expressionFragment expression

private def matchArmPayloadFragment : MatchArmPayload → LocationFragment
  | ⟨patterns, body⟩ =>
      mergeFragments [patternNonemptyFragment patterns, bodyFragment body]

private def statementPayloadFragment : StatementPayload → LocationFragment
  | .assignment operator left right =>
      mergeFragments [assignmentOperatorFragment operator,
        expressionFragment left, expressionFragment right]
  | .letBinding binding => letBindingFragment binding
  | .block body => bodyFragment body
  | .expression expression terminator =>
      mergeFragments [expressionFragment expression,
        rawOptionFragment terminator]
  | .return value terminator =>
      mergeFragments [expressionOptionFragment value, rawFragment terminator]
  | .match scrutinees arms terminator =>
      mergeFragments [expressionNonemptyFragment scrutinees,
        matchArmNonemptyFragment arms, rawOptionFragment terminator]
  | .assembly slice => assemblySliceFragment slice
  | .ifThenElse condition thenBody elseBody =>
      mergeFragments [expressionFragment condition, bodyFragment thenBody,
        bodyOptionFragment elseBody]
  | .forLoop initializers condition post body =>
      mergeFragments [forInitItemListFragment initializers,
        expressionFragment condition, forPostItemListFragment post,
        bodyFragment body]
  | .break terminator => rawFragment terminator
  | .continue terminator => rawFragment terminator

private def expressionFragment : Expression → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [expressionPayloadFragment payload]

private def expressionListFragment : List Expression → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [expressionFragment head, expressionListFragment tail]

private def expressionListOptionFragment :
    Option (List Expression) → LocationFragment
  | none => emptyFragment
  | some expressions => expressionListFragment expressions

private def bodyFragment : Body → LocationFragment
  | ⟨span, payload⟩ =>
      let parts := bodyPayloadFragment payload
      locatedFragmentWithPromotedRoots span parts.promoted [parts.children]

private def patternArgumentsFragment :
    Option (NonemptyList Pattern) → LocationFragment
  | none => emptyFragment
  | some patterns => patternNonemptyFragment patterns

private def patternListFragment : List Pattern → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [patternFragment head, patternListFragment tail]

private def patternFragment : Pattern → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [patternPayloadFragment payload]

private def statementListFragment : List Statement → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [statementFragment head, statementListFragment tail]

private def expressionOptionFragment : Option Expression → LocationFragment
  | none => emptyFragment
  | some expression => expressionFragment expression

private def letBindingFragment : LetBinding → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [letBindingPayloadFragment payload]

private def patternNonemptyFragment :
    NonemptyList Pattern → LocationFragment
  | ⟨head, tail⟩ =>
      mergeFragments [patternFragment head, patternListFragment tail]

private def expressionNonemptyFragment :
    NonemptyList Expression → LocationFragment
  | ⟨head, tail⟩ =>
      mergeFragments [expressionFragment head, expressionListFragment tail]

private def matchArmNonemptyFragment :
    NonemptyList MatchArm → LocationFragment
  | ⟨head, tail⟩ =>
      mergeFragments [matchArmFragment head, matchArmListFragment tail]

private def bodyOptionFragment : Option Body → LocationFragment
  | none => emptyFragment
  | some body => bodyFragment body

private def forInitItemListFragment : List ForInitItem → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [forInitItemFragment head, forInitItemListFragment tail]

private def forPostItemListFragment : List ForPostItem → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [forPostItemFragment head, forPostItemListFragment tail]

private def statementFragment : Statement → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [statementPayloadFragment payload]

private def matchArmFragment : MatchArm → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [matchArmPayloadFragment payload]

private def matchArmListFragment : List MatchArm → LocationFragment
  | [] => emptyFragment
  | head :: tail =>
      mergeFragments [matchArmFragment head, matchArmListFragment tail]

private def forInitItemFragment : ForInitItem → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [forInitItemPayloadFragment payload]

private def forPostItemFragment : ForPostItem → LocationFragment
  | ⟨span, payload⟩ =>
      locatedFragment span [forPostItemPayloadFragment payload]

end

private def classMethodDeclFragment (declaration : ClassMethodDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    functionSignatureFragment declaration.payload.signature,
    rawFragment declaration.payload.terminator
  ]

private def functionDeclFragment (declaration : FunctionDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    functionSignatureFragment declaration.payload.signature,
    bodyFragment declaration.payload.body
  ]

private def fallbackDeclFragment (declaration : FallbackDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    optionFragment genericPrefixFragment declaration.payload.genericPrefix,
    optionFragment markerFragment declaration.payload.public,
    optionFragment markerFragment declaration.payload.payable,
    markerFragment declaration.payload.marker,
    listFragment parameterFragment declaration.payload.parameters,
    optionFragment typeExprFragment declaration.payload.returnType,
    bodyFragment declaration.payload.body
  ]

private def contractConstructorDeclFragment
    (declaration : ContractConstructorDecl) : LocationFragment :=
  locatedFragment declaration.span [
    optionFragment markerFragment declaration.payload.public,
    optionFragment markerFragment declaration.payload.payable,
    markerFragment declaration.payload.marker,
    listFragment parameterFragment declaration.payload.parameters,
    bodyFragment declaration.payload.body
  ]

private def dataConstructorFragment (constructor : DataConstructor) :
    LocationFragment :=
  locatedFragment constructor.span [
    identifierFragment constructor.payload.name,
    optionFragment
      (nonemptyFragment typeExprFragment)
      constructor.payload.fields
  ]

private def dataDeclFragment (declaration : DataDecl) : LocationFragment :=
  locatedFragment declaration.span [
    identifierFragment declaration.payload.name,
    optionFragment
      (nonemptyFragment identifierFragment)
      declaration.payload.parameters,
    optionFragment
      (nonemptyFragment dataConstructorFragment)
      declaration.payload.constructors
  ]

private def typeAliasDeclFragment (declaration : TypeAliasDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    identifierFragment declaration.payload.name,
    optionFragment
      (nonemptyFragment identifierFragment)
      declaration.payload.parameters,
    typeExprFragment declaration.payload.body
  ]

private def classDeclFragment (declaration : ClassDecl) : LocationFragment :=
  locatedFragment declaration.span [
    optionFragment genericPrefixFragment declaration.payload.genericPrefix,
    typeExprFragment declaration.payload.main,
    identifierFragment declaration.payload.className,
    optionFragment
      (nonemptyFragment typeExprFragment)
      declaration.payload.parameters,
    listFragment classMethodDeclFragment declaration.payload.methods
  ]

private def instanceDeclFragment (declaration : InstanceDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    optionFragment genericPrefixFragment declaration.payload.genericPrefix,
    optionFragment markerFragment declaration.payload.default,
    typeExprFragment declaration.payload.main,
    qualifiedNameFragment declaration.payload.className,
    optionFragment
      (nonemptyFragment typeExprFragment)
      declaration.payload.parameters,
    listFragment functionDeclFragment declaration.payload.methods
  ]

private def pragmaDeclFragment (declaration : PragmaDecl) : LocationFragment :=
  locatedFragment declaration.span [
    pragmaKindFragment declaration.payload.kind,
    listFragment identifierFragment declaration.payload.targets
  ]

private def fieldDeclFragment (declaration : FieldDecl) : LocationFragment :=
  locatedFragment declaration.span [
    identifierFragment declaration.payload.name,
    typeExprFragment declaration.payload.type,
    optionFragment expressionFragment declaration.payload.initializer
  ]

private def contractMemberFragment (member : ContractMember) :
    LocationFragment :=
  let children :=
    match member.payload with
    | .dataDecl declaration => [dataDeclFragment declaration]
    | .typeAlias declaration => [typeAliasDeclFragment declaration]
    | .field declaration => [fieldDeclFragment declaration]
    | .function declaration => [functionDeclFragment declaration]
    | .fallback declaration => [fallbackDeclFragment declaration]
    | .constructor declaration =>
        [contractConstructorDeclFragment declaration]
  locatedFragment member.span children

private def contractDeclFragment (declaration : ContractDecl) :
    LocationFragment :=
  locatedFragment declaration.span [
    identifierFragment declaration.payload.name,
    optionFragment
      (nonemptyFragment identifierFragment)
      declaration.payload.parameters,
    listFragment contractMemberFragment declaration.payload.members
  ]

private def topItemFragment (item : TopItem) : LocationFragment :=
  let children :=
    match item.payload with
    | .importDecl declaration => [importDeclFragment declaration]
    | .exportDecl declaration => [exportDeclFragment declaration]
    | .pragmaDecl declaration => [pragmaDeclFragment declaration]
    | .dataDecl declaration => [dataDeclFragment declaration]
    | .typeAliasDecl declaration => [typeAliasDeclFragment declaration]
    | .classDecl declaration => [classDeclFragment declaration]
    | .instanceDecl declaration => [instanceDeclFragment declaration]
    | .contractDecl declaration => [contractDeclFragment declaration]
    | .functionDecl declaration => [functionDeclFragment declaration]
  locatedFragment item.span children

private def parsedModuleFragment (module : ParsedModuleV1) :
    LocationFragment :=
  locatedFragment module.span [
    listFragment topItemFragment module.payload.items
  ]

/-- Traverse one complete parsed module exactly once to collect its locations. -/
def locationInventory (module : ParsedModuleV1) : LocationInventory :=
  (parsedModuleFragment module).inventory

/-- Every located wrapper and retained raw span is valid for the source file. -/
def AllLocationsValid (file : WorkspaceFile) (module : ParsedModuleV1) : Prop :=
  ∀ span ∈ (locationInventory module).spans, span.ValidFor file

/-- Every direct AST parent location contains its retained child location. -/
def AllLocationsNested (module : ParsedModuleV1) : Prop :=
  ∀ containment ∈ (locationInventory module).containments,
    containment.1.Contains containment.2

/-- Complete location validity and direct parent-child nesting for one module. -/
def EveryLocationValid (file : WorkspaceFile) (module : ParsedModuleV1) : Prop :=
  AllLocationsValid file module ∧ AllLocationsNested module

/-- Execute the validity check for every location retained by a module. -/
def locationsValid (file : WorkspaceFile) (module : ParsedModuleV1) : Bool :=
  (locationInventory module).spans.all (fun span => span.isValidFor file)

/-- The executable location-validity check decides its logical predicate. -/
@[simp] theorem locationsValid_eq_true_iff
    (file : WorkspaceFile) (module : ParsedModuleV1) :
    locationsValid file module = true ↔ AllLocationsValid file module := by
  simp [locationsValid, AllLocationsValid, SourceSpan.isValidFor_eq_true_iff]

/-- Execute the direct parent-child containment check for a module. -/
def locationsNested (module : ParsedModuleV1) : Bool :=
  (locationInventory module).containments.all fun containment =>
    containment.1.contains containment.2

/-- The executable nesting check decides its logical predicate. -/
@[simp] theorem locationsNested_eq_true_iff (module : ParsedModuleV1) :
    locationsNested module = true ↔ AllLocationsNested module := by
  simp [locationsNested, AllLocationsNested, SourceSpan.contains_eq_true_iff]

/-- Execute the complete location-validity and nesting check. -/
def everyLocationValid (file : WorkspaceFile) (module : ParsedModuleV1) : Bool :=
  locationsValid file module && locationsNested module

/-- The complete executable check decides `EveryLocationValid`. -/
@[simp] theorem everyLocationValid_eq_true_iff
    (file : WorkspaceFile) (module : ParsedModuleV1) :
    everyLocationValid file module = true ↔ EveryLocationValid file module := by
  simp [everyLocationValid, EveryLocationValid]

end Solcore.Surface.Multi
