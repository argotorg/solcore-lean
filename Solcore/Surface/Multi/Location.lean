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
A proof-facing traversal result. `roots` are exactly the locations that an
enclosing located wrapper must contain directly.
The recursive visitors stay encapsulated behind canonical entry points.
-/
structure LocationFragment where
  roots : List SourceSpan
  inventory : LocationInventory

namespace LocationInventory

/-- Every span in one inventory is valid for the owning source file. -/
def ValidFor (file : WorkspaceFile) (inventory : LocationInventory) : Prop :=
  ∀ span ∈ inventory.spans, span.ValidFor file

/-- Every direct parent-child edge in one inventory is geometrically nested. -/
def Nested (inventory : LocationInventory) : Prop :=
  ∀ containment ∈ inventory.containments,
    containment.1.Contains containment.2

end LocationInventory

namespace LocationFragment

/-- Every retained span in one traversal fragment is source-valid. -/
def ValidFor (file : WorkspaceFile) (fragment : LocationFragment) : Prop :=
  fragment.inventory.ValidFor file

/-- Every direct parent-child edge in one fragment is geometrically nested. -/
def Nested (fragment : LocationFragment) : Prop :=
  fragment.inventory.Nested

/-- Every root exposed by a fragment is contained by an enclosing span. -/
def RootsContainedBy (fragment : LocationFragment)
    (outer : SourceSpan) : Prop :=
  ∀ root ∈ fragment.roots, outer.Contains root

end LocationFragment

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

namespace LocationFragment

/-- The empty traversal fragment. -/
def empty : LocationFragment :=
  emptyFragment

/-- Merge sibling fragments without adding parent-child edges. -/
def merge (fragments : List LocationFragment) : LocationFragment :=
  mergeFragments fragments

/-- Retain one raw span as a root without adding a wrapper. -/
def raw (span : SourceSpan) : LocationFragment :=
  rawFragment span

/-- Retain one located wrapper around canonical child fragments. -/
def located (span : SourceSpan) (children : List LocationFragment) :
    LocationFragment :=
  locatedFragment span children

/-- Retain one located wrapper while exposing selected raw spans to its
parent instead of connecting them to this wrapper. -/
def locatedWithPromotedRoots (span : SourceSpan)
    (promoted : List SourceSpan) (children : List LocationFragment) :
    LocationFragment :=
  locatedFragmentWithPromotedRoots span promoted children

@[simp] theorem empty_roots : empty.roots = [] := by
  rfl

@[simp] theorem empty_spans : empty.inventory.spans = [] := by
  rfl

@[simp] theorem empty_containments : empty.inventory.containments = [] := by
  rfl

@[simp] theorem merge_roots (fragments : List LocationFragment) :
    (merge fragments).roots = fragments.flatMap (fun fragment => fragment.roots) := by
  rfl

@[simp] theorem merge_spans (fragments : List LocationFragment) :
    (merge fragments).inventory.spans =
      fragments.flatMap (fun fragment => fragment.inventory.spans) := by
  rfl

@[simp] theorem merge_containments (fragments : List LocationFragment) :
    (merge fragments).inventory.containments =
      fragments.flatMap (fun fragment => fragment.inventory.containments) := by
  rfl

@[simp] theorem raw_roots (span : SourceSpan) :
    (raw span).roots = [span] := by
  rfl

@[simp] theorem raw_spans (span : SourceSpan) :
    (raw span).inventory.spans = [span] := by
  rfl

@[simp] theorem raw_containments (span : SourceSpan) :
    (raw span).inventory.containments = [] := by
  rfl

@[simp] theorem located_roots (span : SourceSpan)
    (children : List LocationFragment) :
    (located span children).roots = [span] := by
  rfl

@[simp] theorem located_spans (span : SourceSpan)
    (children : List LocationFragment) :
    (located span children).inventory.spans =
      span :: (merge children).inventory.spans := by
  rfl

@[simp] theorem located_containments (span : SourceSpan)
    (children : List LocationFragment) :
    (located span children).inventory.containments =
      (merge children).roots.map (fun child => (span, child)) ++
        (merge children).inventory.containments := by
  rfl

@[simp] theorem locatedWithPromotedRoots_roots (span : SourceSpan)
    (promoted : List SourceSpan) (children : List LocationFragment) :
    (locatedWithPromotedRoots span promoted children).roots =
      span :: promoted := by
  rfl

@[simp] theorem locatedWithPromotedRoots_spans (span : SourceSpan)
    (promoted : List SourceSpan) (children : List LocationFragment) :
    (locatedWithPromotedRoots span promoted children).inventory.spans =
      span :: promoted ++ (merge children).inventory.spans := by
  rfl

@[simp] theorem locatedWithPromotedRoots_containments (span : SourceSpan)
    (promoted : List SourceSpan) (children : List LocationFragment) :
    (locatedWithPromotedRoots span promoted children).inventory.containments =
      (merge children).roots.map (fun child => (span, child)) ++
      (merge children).inventory.containments := by
  rfl

/-- Location fragments are equal when all three observable lists agree. -/
theorem eq_of_fields
    {left right : LocationFragment}
    (roots : left.roots = right.roots)
    (spans : left.inventory.spans = right.inventory.spans)
    (containments : left.inventory.containments =
      right.inventory.containments) :
    left = right := by
  cases left with
  | mk leftRoots leftInventory =>
      cases right with
      | mk rightRoots rightInventory =>
          cases leftInventory
          cases rightInventory
          simp only at roots spans containments
          subst_vars
          rfl

/-- Wrapping a pre-merged child fragment is identical to wrapping its
unmerged sibling list. -/
@[simp] theorem located_merge (span : SourceSpan)
    (children : List LocationFragment) :
    located span [merge children] = located span children := by
  apply eq_of_fields <;> simp

/-- A located leaf and a raw span have the same location fragment. -/
@[simp] theorem leaf_eq_raw (span : SourceSpan) :
    located span [] = raw span := by
  apply eq_of_fields <;> simp

end LocationFragment

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

namespace LocationFragment

/-- Proof-facing traversal of one identifier occurrence. -/
def ofIdentifier (identifier : IdentifierOccurrence) : LocationFragment :=
  identifierFragment identifier

@[simp] theorem ofIdentifier_roots (identifier : IdentifierOccurrence) :
    (ofIdentifier identifier).roots = [identifier.span] := by
  rfl

/-- Proof-facing traversal of one top-level item. -/
def ofTopItem (item : TopItem) : LocationFragment :=
  topItemFragment item

@[simp] theorem ofTopItem_roots (item : TopItem) :
    (ofTopItem item).roots = [item.span] := by
  rfl

/-- Proof-facing traversal of one qualified name. -/
def ofQualifiedName (name : QualifiedName) : LocationFragment :=
  qualifiedNameFragment name

@[simp] theorem ofQualifiedName_roots (name : QualifiedName) :
    (ofQualifiedName name).roots = [name.span] := by
  rfl

/-- Proof-facing traversal of one module reference. -/
def ofModuleReference (reference : ModuleReference) : LocationFragment :=
  moduleReferenceFragment reference

@[simp] theorem ofModuleReference_roots (reference : ModuleReference) :
    (ofModuleReference reference).roots = [reference.span] := by
  rfl

/-- Proof-facing traversal of one import selector entry. -/
def ofImportSelectorEntry (entry : ImportSelectorEntry) : LocationFragment :=
  importSelectorEntryFragment entry

@[simp] theorem ofImportSelectorEntry_roots (entry : ImportSelectorEntry) :
    (ofImportSelectorEntry entry).roots = [entry.span] := by
  rfl

/-- Proof-facing traversal of one hiding clause. -/
def ofHidingClause (clause : HidingClause) : LocationFragment :=
  hidingClauseFragment clause

@[simp] theorem ofHidingClause_roots (clause : HidingClause) :
    (ofHidingClause clause).roots = [clause.span] := by
  rfl

@[simp] theorem ofHidingClause_mk (span : SourceSpan)
    (names : List IdentifierOccurrence) :
    ofHidingClause ⟨span, ⟨names⟩⟩ =
      located span [merge (names.map ofIdentifier)] := by
  rfl

/-- Proof-facing traversal of one import declaration. -/
def ofImportDecl (declaration : ImportDecl) : LocationFragment :=
  importDeclFragment declaration

@[simp] theorem ofImportDecl_roots (declaration : ImportDecl) :
    (ofImportDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one constructor selection. -/
def ofConstructorSelection (selection : ConstructorSelection) :
    LocationFragment :=
  constructorSelectionFragment selection

@[simp] theorem ofConstructorSelection_roots
    (selection : ConstructorSelection) :
    (ofConstructorSelection selection).roots = [selection.span] := by
  rfl

/-- Proof-facing traversal of one exported item. -/
def ofExportItem (item : ExportItem) : LocationFragment :=
  exportItemFragment item

@[simp] theorem ofExportItem_roots (item : ExportItem) :
    (ofExportItem item).roots = [item.span] := by
  rfl

/-- Proof-facing traversal of one local export entry. -/
def ofExportEntry (entry : ExportEntry) : LocationFragment :=
  exportEntryFragment entry

@[simp] theorem ofExportEntry_roots (entry : ExportEntry) :
    (ofExportEntry entry).roots = [entry.span] := by
  rfl

/-- Proof-facing traversal of one remote export entry. -/
def ofRemoteExportEntry (entry : RemoteExportEntry) : LocationFragment :=
  remoteExportEntryFragment entry

@[simp] theorem ofRemoteExportEntry_roots (entry : RemoteExportEntry) :
    (ofRemoteExportEntry entry).roots = [entry.span] := by
  rfl

/-- Proof-facing traversal of one export declaration. -/
def ofExportDecl (declaration : ExportDecl) : LocationFragment :=
  exportDeclFragment declaration

@[simp] theorem ofExportDecl_roots (declaration : ExportDecl) :
    (ofExportDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one forall binder. -/
def ofForallBinder (binder : ForallBinder) : LocationFragment :=
  forallBinderFragment binder

@[simp] theorem ofForallBinder_roots (binder : ForallBinder) :
    (ofForallBinder binder).roots = [binder.span] := by
  rfl

/-- Proof-facing traversal of one forall clause. -/
def ofForallClause (clause : ForallClause) : LocationFragment :=
  forallClauseFragment clause

@[simp] theorem ofForallClause_roots (clause : ForallClause) :
    (ofForallClause clause).roots = [clause.span] := by
  rfl

/-- Proof-facing traversal of one predicate. -/
def ofPredicate (predicate : Predicate) : LocationFragment :=
  predicateFragment predicate

@[simp] theorem ofPredicate_roots (predicate : Predicate) :
    (ofPredicate predicate).roots = [predicate.span] := by
  rfl

/-- Proof-facing traversal of one generic prefix. -/
def ofGenericPrefix (genericPrefix : GenericPrefix) : LocationFragment :=
  genericPrefixFragment genericPrefix

@[simp] theorem ofGenericPrefix_roots (genericPrefix : GenericPrefix) :
    (ofGenericPrefix genericPrefix).roots = [genericPrefix.span] := by
  rfl

/-- Proof-facing traversal of one parameter. -/
def ofParameter (parameter : Parameter) : LocationFragment :=
  parameterFragment parameter

@[simp] theorem ofParameter_roots (parameter : Parameter) :
    (ofParameter parameter).roots = [parameter.span] := by
  rfl

/-- Proof-facing traversal of one function signature. -/
def ofFunctionSignature (signature : FunctionSignature) : LocationFragment :=
  functionSignatureFragment signature

@[simp] theorem ofFunctionSignature_roots (signature : FunctionSignature) :
    (ofFunctionSignature signature).roots = [signature.span] := by
  rfl

/-- Proof-facing traversal of one class method declaration. -/
def ofClassMethodDecl (declaration : ClassMethodDecl) : LocationFragment :=
  classMethodDeclFragment declaration

@[simp] theorem ofClassMethodDecl_roots (declaration : ClassMethodDecl) :
    (ofClassMethodDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one function declaration. -/
def ofFunctionDecl (declaration : FunctionDecl) : LocationFragment :=
  functionDeclFragment declaration

@[simp] theorem ofFunctionDecl_roots (declaration : FunctionDecl) :
    (ofFunctionDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one fallback declaration. -/
def ofFallbackDecl (declaration : FallbackDecl) : LocationFragment :=
  fallbackDeclFragment declaration

@[simp] theorem ofFallbackDecl_roots (declaration : FallbackDecl) :
    (ofFallbackDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one contract constructor declaration. -/
def ofContractConstructorDecl (declaration : ContractConstructorDecl) :
    LocationFragment :=
  contractConstructorDeclFragment declaration

@[simp] theorem ofContractConstructorDecl_roots
    (declaration : ContractConstructorDecl) :
    (ofContractConstructorDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one data constructor. -/
def ofDataConstructor (constructor : DataConstructor) : LocationFragment :=
  dataConstructorFragment constructor

@[simp] theorem ofDataConstructor_roots (constructor : DataConstructor) :
    (ofDataConstructor constructor).roots = [constructor.span] := by
  rfl

/-- Proof-facing traversal of one data declaration. -/
def ofDataDecl (declaration : DataDecl) : LocationFragment :=
  dataDeclFragment declaration

@[simp] theorem ofDataDecl_roots (declaration : DataDecl) :
    (ofDataDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one type-alias declaration. -/
def ofTypeAliasDecl (declaration : TypeAliasDecl) : LocationFragment :=
  typeAliasDeclFragment declaration

@[simp] theorem ofTypeAliasDecl_roots (declaration : TypeAliasDecl) :
    (ofTypeAliasDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one class declaration. -/
def ofClassDecl (declaration : ClassDecl) : LocationFragment :=
  classDeclFragment declaration

@[simp] theorem ofClassDecl_roots (declaration : ClassDecl) :
    (ofClassDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one instance declaration. -/
def ofInstanceDecl (declaration : InstanceDecl) : LocationFragment :=
  instanceDeclFragment declaration

@[simp] theorem ofInstanceDecl_roots (declaration : InstanceDecl) :
    (ofInstanceDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one pragma declaration. -/
def ofPragmaDecl (declaration : PragmaDecl) : LocationFragment :=
  pragmaDeclFragment declaration

@[simp] theorem ofPragmaDecl_roots (declaration : PragmaDecl) :
    (ofPragmaDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one field declaration. -/
def ofFieldDecl (declaration : FieldDecl) : LocationFragment :=
  fieldDeclFragment declaration

@[simp] theorem ofFieldDecl_roots (declaration : FieldDecl) :
    (ofFieldDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one contract member. -/
def ofContractMember (member : ContractMember) : LocationFragment :=
  contractMemberFragment member

@[simp] theorem ofContractMember_roots (member : ContractMember) :
    (ofContractMember member).roots = [member.span] := by
  rfl

/-- Proof-facing traversal of one contract declaration. -/
def ofContractDecl (declaration : ContractDecl) : LocationFragment :=
  contractDeclFragment declaration

@[simp] theorem ofContractDecl_roots (declaration : ContractDecl) :
    (ofContractDecl declaration).roots = [declaration.span] := by
  rfl

/-- Proof-facing traversal of one type expression. -/
def ofTypeExpr (typeExpression : TypeExpr) : LocationFragment :=
  {
    roots := [typeExpression.span]
    inventory := (typeExprFragment typeExpression).inventory
  }

@[simp] theorem ofTypeExpr_roots (typeExpression : TypeExpr) :
    (ofTypeExpr typeExpression).roots = [typeExpression.span] := by
  rfl

@[simp] theorem ofTypeExpr_emptyTuple (span : SourceSpan) :
    ofTypeExpr ⟨span, .tuple []⟩ = located span [empty] := by
  simp [ofTypeExpr, typeExprFragment, typeExprListFragment, located,
    empty, locatedFragment, emptyFragment, mergeFragments]

/-- Proof-facing traversal of one pattern. -/
def ofPattern (pattern : Pattern) : LocationFragment :=
  patternFragment pattern

@[simp] theorem ofPattern_roots (pattern : Pattern) :
    (ofPattern pattern).roots = [pattern.span] := by
  cases pattern
  rfl

@[simp] theorem ofPattern_emptyTuple (span : SourceSpan) :
    ofPattern ⟨span, .tuple []⟩ = located span [empty] := by
  rfl

/-- Proof-facing traversal of one let binding. -/
def ofLetBinding (binding : LetBinding) : LocationFragment :=
  letBindingFragment binding

@[simp] theorem ofLetBinding_roots (binding : LetBinding) :
    (ofLetBinding binding).roots = [binding.span] := by
  cases binding
  rfl

/-- Proof-facing traversal of one for-loop initializer. -/
def ofForInitItem (item : ForInitItem) : LocationFragment :=
  forInitItemFragment item

@[simp] theorem ofForInitItem_roots (item : ForInitItem) :
    (ofForInitItem item).roots = [item.span] := by
  cases item
  rfl

/-- Proof-facing traversal of one for-loop post item. -/
def ofForPostItem (item : ForPostItem) : LocationFragment :=
  forPostItemFragment item

@[simp] theorem ofForPostItem_roots (item : ForPostItem) :
    (ofForPostItem item).roots = [item.span] := by
  cases item
  rfl

/-- Proof-facing traversal of one literal and its retained locations. -/
def ofLiteral (literal : Literal) : LocationFragment :=
  literalFragment literal

@[simp] theorem ofLiteral_roots (literal : Literal) :
    (ofLiteral literal).roots = [literal.span] := by
  rfl

@[simp] theorem ofLiteral_spans (literal : Literal) :
    (ofLiteral literal).inventory.spans = [literal.span] := by
  rfl

@[simp] theorem ofLiteral_containments (literal : Literal) :
    (ofLiteral literal).inventory.containments = [] := by
  rfl

/-- Proof-facing traversal of one assignment operator location. -/
def ofAssignmentOperator (operator : Located AssignmentOperator) :
    LocationFragment :=
  assignmentOperatorFragment operator

@[simp] theorem ofAssignmentOperator_roots
    (operator : Located AssignmentOperator) :
    (ofAssignmentOperator operator).roots = [operator.span] := by
  rfl

@[simp] theorem ofAssignmentOperator_spans
    (operator : Located AssignmentOperator) :
    (ofAssignmentOperator operator).inventory.spans = [operator.span] := by
  rfl

@[simp] theorem ofAssignmentOperator_containments
    (operator : Located AssignmentOperator) :
    (ofAssignmentOperator operator).inventory.containments = [] := by
  rfl

/-- Proof-facing traversal of one expression and all of its descendants. -/
def ofExpression (expression : Expression) : LocationFragment :=
  expressionFragment expression

@[simp] theorem ofExpression_roots (expression : Expression) :
    (ofExpression expression).roots = [expression.span] := by
  cases expression
  rfl

@[simp] theorem ofExpression_emptyTuple (span : SourceSpan) :
    ofExpression ⟨span, .tuple []⟩ = located span [empty] := by
  rfl

/-- Proof-facing traversal of one body and all of its descendants. -/
def ofBody (body : Body) : LocationFragment :=
  bodyFragment body

@[simp] theorem ofBody_roots (body : Body) :
    (ofBody body).roots =
      match body.payload.origin with
      | .braced _ _ => [body.span]
      | .matchArm fatArrow => [body.span, fatArrow] := by
  rcases body with ⟨span, origin, statements⟩
  cases origin <;> rfl

/-- Proof-facing traversal of one match arm and all of its descendants. -/
def ofMatchArm (arm : MatchArm) : LocationFragment :=
  matchArmFragment arm

@[simp] theorem ofMatchArm_roots (arm : MatchArm) :
    (ofMatchArm arm).roots = [arm.span] := by
  cases arm
  rfl

/-- Proof-facing traversal of one statement and all of its descendants. -/
def ofStatement (statement : Statement) : LocationFragment :=
  statementFragment statement

@[simp] theorem ofStatement_roots (statement : Statement) :
    (ofStatement statement).roots = [statement.span] := by
  cases statement
  rfl

/-- Proof-facing traversal of one opaque assembly slice. -/
def ofAssemblySlice (slice : AssemblySlice) : LocationFragment :=
  assemblySliceFragment slice

@[simp] theorem ofAssemblySlice_roots (slice : AssemblySlice) :
    (ofAssemblySlice slice).roots = [slice.span] := by
  rfl

@[simp] theorem ofAssemblySlice_spans (slice : AssemblySlice) :
    (ofAssemblySlice slice).inventory.spans =
      [slice.span, slice.payload.openBrace, slice.payload.contents,
        slice.payload.closeBrace] := by
  rfl

@[simp] theorem ofAssemblySlice_containments (slice : AssemblySlice) :
    (ofAssemblySlice slice).inventory.containments =
      [(slice.span, slice.payload.openBrace),
        (slice.span, slice.payload.contents),
        (slice.span, slice.payload.closeBrace)] := by
  rfl

@[simp] theorem ofStatement_assembly (span : SourceSpan)
    (slice : AssemblySlice) :
    ofStatement ⟨span, .assembly slice⟩ =
      located span [ofAssemblySlice slice] := by
  rfl

/-- Proof-facing location of a leaf carrier. -/
def leaf (span : SourceSpan) : LocationFragment :=
  located span []

/-- Proof-facing locations of an optional carrier. -/
def ofOption {alpha : Type} (visit : alpha → LocationFragment) :
    Option alpha → LocationFragment
  | none => empty
  | some value => visit value

/-- Proof-facing sibling locations of a list carrier. -/
def ofList {alpha : Type} (visit : alpha → LocationFragment)
    (values : List alpha) : LocationFragment :=
  merge (values.map visit)

/-- Proof-facing sibling locations of a nonempty carrier. -/
def ofNonempty {alpha : Type} (visit : alpha → LocationFragment)
    (values : NonemptyList alpha) : LocationFragment :=
  merge [visit values.head, ofList visit values.tail]

/-- Ordered type-expression locations in the recursive visitor shape. -/
private theorem ofTypeExpr_eq_fragment (value : TypeExpr) :
    ofTypeExpr value = typeExprFragment value := by
  rcases value with ⟨span, payload⟩
  apply eq_of_fields
  · unfold ofTypeExpr
    cases payload <;> rw [typeExprFragment] <;> rfl
  · rfl
  · rfl

def ofTypeExprList : List TypeExpr → LocationFragment
  | [] => empty
  | head :: tail => merge [ofTypeExpr head, ofTypeExprList tail]

private theorem ofTypeExprList_eq_fragment (values : List TypeExpr) :
    ofTypeExprList values = typeExprListFragment values := by
  induction values with
  | nil => simp [ofTypeExprList, typeExprListFragment, empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofTypeExprList, typeExprListFragment, merge,
        ofTypeExpr_eq_fragment, inductionHypothesis]

/-- Optional type-expression argument locations in the recursive visitor
shape. -/
def ofTypeExprArguments :
    Option (NonemptyList TypeExpr) → LocationFragment
  | none => empty
  | some values =>
      merge [ofTypeExpr values.head, ofTypeExprList values.tail]

private theorem ofTypeExprArguments_eq_fragment
    (arguments : Option (NonemptyList TypeExpr)) :
    ofTypeExprArguments arguments =
      typeExprArgumentsFragment arguments := by
  cases arguments with
  | none =>
      simp [ofTypeExprArguments, typeExprArgumentsFragment,
        empty, emptyFragment]
  | some values =>
      rcases values with ⟨head, tail⟩
      simp [ofTypeExprArguments, typeExprArgumentsFragment,
        typeExprNonemptyFragment, merge, ofTypeExpr_eq_fragment,
        ofTypeExprList_eq_fragment]

/-- The exact child fragment below one type-expression wrapper. -/
def ofTypeExprPayload : TypeExprPayload → LocationFragment
  | .named name arguments =>
      merge [ofQualifiedName name, ofTypeExprArguments arguments]
  | .proxy marker inner => merge [leaf marker.span, ofTypeExpr inner]
  | .function domain codomain =>
      merge [ofTypeExpr domain, ofTypeExpr codomain]
  | .tuple elements => ofTypeExprList elements
  | .group inner => ofTypeExpr inner
  | .comptime marker inner => merge [leaf marker.span, ofTypeExpr inner]

/-- A type-expression visitor is exactly its outer span around its public
payload fragment. -/
@[simp] theorem ofTypeExpr_mk (span : SourceSpan)
    (payload : TypeExprPayload) :
    ofTypeExpr ⟨span, payload⟩ =
      located span [ofTypeExprPayload payload] := by
  rw [ofTypeExpr_eq_fragment]
  cases payload <;>
    simp [typeExprFragment, ofTypeExprPayload, leaf, located, merge,
      ofTypeExpr_eq_fragment, ofTypeExprList_eq_fragment,
      ofTypeExprArguments_eq_fragment, ofQualifiedName,
      qualifiedNameFragment, unitMarkerFragment, markerFragment]
  all_goals exact (located_merge _ _).symm

/-- Ordered pattern locations in the recursive visitor shape. -/
def ofPatternList : List Pattern → LocationFragment
  | [] => empty
  | head :: tail => merge [ofPattern head, ofPatternList tail]

/-- Optional nonempty pattern argument locations. -/
def ofPatternArguments :
    Option (NonemptyList Pattern) → LocationFragment
  | none => empty
  | some values =>
      merge [ofPattern values.head, ofPatternList values.tail]

/-- The exact child fragment below one pattern wrapper. -/
def ofPatternPayload : PatternPayload → LocationFragment
  | .named name arguments =>
      merge [ofQualifiedName name, ofPatternArguments arguments]
  | .dotConstructor marker name arguments =>
      merge [leaf marker.span, ofIdentifier name,
        ofPatternArguments arguments]
  | .wildcard marker => leaf marker.span
  | .literal literal => ofLiteral literal
  | .comptime marker expression =>
      merge [leaf marker.span, ofExpression expression]
  | .tuple elements => ofPatternList elements
  | .group inner => ofPattern inner

private theorem ofPatternList_eq_fragment (values : List Pattern) :
    ofPatternList values = patternListFragment values := by
  induction values with
  | nil => simp [ofPatternList, patternListFragment, empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofPatternList, patternListFragment, merge, ofPattern,
        inductionHypothesis]

private theorem ofPatternArguments_eq_fragment
    (arguments : Option (NonemptyList Pattern)) :
    ofPatternArguments arguments = patternArgumentsFragment arguments := by
  cases arguments with
  | none =>
      simp [ofPatternArguments, patternArgumentsFragment,
        empty, emptyFragment]
  | some values =>
      rcases values with ⟨head, tail⟩
      simp [ofPatternArguments, patternArgumentsFragment,
        patternNonemptyFragment, merge, ofPattern,
        ofPatternList_eq_fragment]

private theorem ofPatternPayload_eq_fragment (payload : PatternPayload) :
    ofPatternPayload payload = patternPayloadFragment payload := by
  cases payload with
  | named name arguments =>
      simp only [ofPatternPayload, patternPayloadFragment]
      rw [ofPatternArguments_eq_fragment]
      rfl
  | dotConstructor marker name arguments =>
      simp only [ofPatternPayload, patternPayloadFragment]
      rw [ofPatternArguments_eq_fragment]
      rfl
  | tuple elements =>
      exact ofPatternList_eq_fragment elements
  | wildcard marker => rfl
  | literal literal => rfl
  | comptime marker expression => rfl
  | group inner => rfl

/-- A pattern visitor is exactly its outer span around its public payload
fragment. -/
@[simp] theorem ofPattern_mk (span : SourceSpan)
    (payload : PatternPayload) :
    ofPattern ⟨span, payload⟩ =
      located span [ofPatternPayload payload] := by
  unfold ofPattern
  rw [patternFragment]
  rw [ofPatternPayload_eq_fragment]
  rfl

/-- Ordered expression locations in the recursive visitor shape. -/
def ofExpressionList : List Expression → LocationFragment
  | [] => empty
  | head :: tail => merge [ofExpression head, ofExpressionList tail]

/-- Optional expression-list locations in the recursive visitor shape. -/
def ofExpressionListOption : Option (List Expression) → LocationFragment
  | none => empty
  | some expressions => ofExpressionList expressions

/-- The exact child fragment below one expression wrapper. -/
def ofExpressionPayload : ExpressionPayload → LocationFragment
  | .name name => ofIdentifier name
  | .call callee arguments =>
      merge [ofExpression callee, ofExpressionList arguments]
  | .select receiver field =>
      merge [ofExpression receiver, ofIdentifier field]
  | .dotConstructor marker name arguments =>
      merge [leaf marker.span, ofIdentifier name,
        ofExpressionListOption arguments]
  | .proxy marker typeExpression =>
      merge [leaf marker.span, ofTypeExpr typeExpression]
  | .literal literal => ofLiteral literal
  | .lambda parameters returnType body =>
      merge [ofList ofParameter parameters,
        ofOption ofTypeExpr returnType, ofBody body]
  | .annotation expression typeExpression =>
      merge [ofExpression expression, ofTypeExpr typeExpression]
  | .keywordConditional condition thenBranch elseBranch =>
      merge [ofExpression condition, ofExpression thenBranch,
        ofExpression elseBranch]
  | .ternaryConditional condition thenBranch elseBranch =>
      merge [ofExpression condition, ofExpression thenBranch,
        ofExpression elseBranch]
  | .index receiver index =>
      merge [ofExpression receiver, ofExpression index]
  | .prefix operator operand =>
      merge [leaf operator.span, ofExpression operand]
  | .infix operator left right =>
      merge [leaf operator.span, ofExpression left, ofExpression right]
  | .tuple elements => ofExpressionList elements
  | .group inner => ofExpression inner

private theorem ofExpressionList_eq_fragment
    (values : List Expression) :
    ofExpressionList values = expressionListFragment values := by
  induction values with
  | nil =>
      simp [ofExpressionList, expressionListFragment,
        empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofExpressionList, expressionListFragment, merge,
        ofExpression, inductionHypothesis]

private theorem ofExpressionListOption_eq_fragment
    (values : Option (List Expression)) :
    ofExpressionListOption values =
      expressionListOptionFragment values := by
  cases values with
  | none =>
      simp [ofExpressionListOption, expressionListOptionFragment,
        empty, emptyFragment]
  | some expressions =>
      exact ofExpressionList_eq_fragment expressions

private theorem ofExpressionPayload_eq_fragment
    (payload : ExpressionPayload) :
    ofExpressionPayload payload = expressionPayloadFragment payload := by
  cases payload with
  | name name => rfl
  | call callee arguments =>
      simp only [ofExpressionPayload, expressionPayloadFragment]
      rw [ofExpressionList_eq_fragment]
      rfl
  | select receiver field => rfl
  | dotConstructor marker name arguments =>
      simp only [ofExpressionPayload, expressionPayloadFragment]
      rw [ofExpressionListOption_eq_fragment]
      rfl
  | proxy marker typeExpression =>
      simp only [ofExpressionPayload, expressionPayloadFragment]
      rw [ofTypeExpr_eq_fragment]
      rfl
  | literal literal => rfl
  | lambda parameters returnType body =>
      simp only [ofExpressionPayload, expressionPayloadFragment]
      cases returnType with
      | none =>
          simp only [ofOption, optionFragment]
          rfl
      | some typeExpression =>
          simp only [ofOption, optionFragment]
          rw [ofTypeExpr_eq_fragment]
          rfl
  | annotation expression typeExpression =>
      simp only [ofExpressionPayload, expressionPayloadFragment]
      rw [ofTypeExpr_eq_fragment]
      rfl
  | keywordConditional condition thenBranch elseBranch => rfl
  | ternaryConditional condition thenBranch elseBranch => rfl
  | index receiver index => rfl
  | «prefix» operator operand => rfl
  | «infix» operator left right => rfl
  | tuple elements =>
      exact ofExpressionList_eq_fragment elements
  | group inner => rfl

/-- An expression visitor is exactly its outer span around its public payload
fragment. -/
@[simp] theorem ofExpression_mk (span : SourceSpan)
    (payload : ExpressionPayload) :
    ofExpression ⟨span, payload⟩ =
      located span [ofExpressionPayload payload] := by
  unfold ofExpression
  rw [expressionFragment]
  rw [ofExpressionPayload_eq_fragment]
  rfl

/-- The exact child fragment below one let-binding wrapper. -/
def ofLetBindingPayload (payload : LetBindingPayload) : LocationFragment :=
  merge [ofOption (fun marker => leaf marker.span) payload.comptime,
    ofIdentifier payload.name, ofOption ofTypeExpr payload.type,
    ofOption ofExpression payload.initializer]

private theorem ofLetBindingPayload_eq_fragment
    (payload : LetBindingPayload) :
    ofLetBindingPayload payload = letBindingPayloadFragment payload := by
  rcases payload with ⟨comptime, name, typeExpression, initializer⟩
  simp only [ofLetBindingPayload, letBindingPayloadFragment]
  cases comptime <;> cases typeExpression <;> cases initializer <;>
    simp only [ofOption, optionFragment]
  all_goals try rw [ofTypeExpr_eq_fragment]
  all_goals rfl

/-- A let-binding visitor is exactly its outer span around its public payload
fragment. -/
@[simp] theorem ofLetBinding_mk (span : SourceSpan)
    (payload : LetBindingPayload) :
    ofLetBinding ⟨span, payload⟩ =
      located span [ofLetBindingPayload payload] := by
  unfold ofLetBinding
  rw [letBindingFragment]
  rw [ofLetBindingPayload_eq_fragment]
  rfl

/-- The exact child fragment below one `for` initializer wrapper. -/
def ofForInitItemPayload : ForInitItemPayload → LocationFragment
  | .letBinding binding => ofLetBinding binding
  | .assignment operator left right =>
      merge [ofAssignmentOperator operator, ofExpression left,
        ofExpression right]
  | .expression expression => ofExpression expression

private theorem ofForInitItemPayload_eq_fragment
    (payload : ForInitItemPayload) :
    ofForInitItemPayload payload = forInitItemPayloadFragment payload := by
  cases payload <;> rfl

/-- A `for` initializer visitor is exactly its outer span around its public
payload fragment. -/
@[simp] theorem ofForInitItem_mk (span : SourceSpan)
    (payload : ForInitItemPayload) :
    ofForInitItem ⟨span, payload⟩ =
      located span [ofForInitItemPayload payload] := by
  unfold ofForInitItem
  rw [forInitItemFragment]
  rw [ofForInitItemPayload_eq_fragment]
  rfl

/-- The exact child fragment below one `for` post-item wrapper. -/
def ofForPostItemPayload : ForPostItemPayload → LocationFragment
  | .assignment operator left right =>
      merge [ofAssignmentOperator operator, ofExpression left,
        ofExpression right]
  | .expression expression => ofExpression expression

private theorem ofForPostItemPayload_eq_fragment
    (payload : ForPostItemPayload) :
    ofForPostItemPayload payload = forPostItemPayloadFragment payload := by
  cases payload <;> rfl

/-- A `for` post-item visitor is exactly its outer span around its public
payload fragment. -/
@[simp] theorem ofForPostItem_mk (span : SourceSpan)
    (payload : ForPostItemPayload) :
    ofForPostItem ⟨span, payload⟩ =
      located span [ofForPostItemPayload payload] := by
  unfold ofForPostItem
  rw [forPostItemFragment]
  rw [ofForPostItemPayload_eq_fragment]
  rfl

/-- Ordered statement locations in the recursive visitor shape. -/
def ofStatementList : List Statement → LocationFragment
  | [] => empty
  | head :: tail => merge [ofStatement head, ofStatementList tail]

/-- Ordered match-arm locations in the recursive visitor shape. -/
def ofMatchArmList : List MatchArm → LocationFragment
  | [] => empty
  | head :: tail => merge [ofMatchArm head, ofMatchArmList tail]

/-- Ordered `for` initializer locations in the recursive visitor shape. -/
def ofForInitItemList : List ForInitItem → LocationFragment
  | [] => empty
  | head :: tail => merge [ofForInitItem head, ofForInitItemList tail]

/-- Ordered `for` post-item locations in the recursive visitor shape. -/
def ofForPostItemList : List ForPostItem → LocationFragment
  | [] => empty
  | head :: tail => merge [ofForPostItem head, ofForPostItemList tail]

/-- Nonempty expression locations in the recursive visitor shape. -/
def ofExpressionNonempty (values : NonemptyList Expression) :
    LocationFragment :=
  merge [ofExpression values.head, ofExpressionList values.tail]

/-- Nonempty pattern locations in the recursive visitor shape. -/
def ofPatternNonempty (values : NonemptyList Pattern) : LocationFragment :=
  merge [ofPattern values.head, ofPatternList values.tail]

/-- Nonempty match-arm locations in the recursive visitor shape. -/
def ofMatchArmNonempty (values : NonemptyList MatchArm) :
    LocationFragment :=
  merge [ofMatchArm values.head, ofMatchArmList values.tail]

private theorem ofStatementList_eq_fragment (values : List Statement) :
    ofStatementList values = statementListFragment values := by
  induction values with
  | nil =>
      simp [ofStatementList, statementListFragment,
        empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofStatementList, statementListFragment, merge,
        ofStatement, inductionHypothesis]

private theorem ofMatchArmList_eq_fragment (values : List MatchArm) :
    ofMatchArmList values = matchArmListFragment values := by
  induction values with
  | nil =>
      simp [ofMatchArmList, matchArmListFragment,
        empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofMatchArmList, matchArmListFragment, merge,
        ofMatchArm, inductionHypothesis]

private theorem ofForInitItemList_eq_fragment
    (values : List ForInitItem) :
    ofForInitItemList values = forInitItemListFragment values := by
  induction values with
  | nil =>
      simp [ofForInitItemList, forInitItemListFragment,
        empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofForInitItemList, forInitItemListFragment, merge,
        ofForInitItem, inductionHypothesis]

private theorem ofForPostItemList_eq_fragment
    (values : List ForPostItem) :
    ofForPostItemList values = forPostItemListFragment values := by
  induction values with
  | nil =>
      simp [ofForPostItemList, forPostItemListFragment,
        empty, emptyFragment]
  | cons head tail inductionHypothesis =>
      simp [ofForPostItemList, forPostItemListFragment, merge,
        ofForPostItem, inductionHypothesis]

private theorem ofExpressionNonempty_eq_fragment
    (values : NonemptyList Expression) :
    ofExpressionNonempty values = expressionNonemptyFragment values := by
  rcases values with ⟨head, tail⟩
  simp [ofExpressionNonempty, expressionNonemptyFragment, merge,
    ofExpression, ofExpressionList_eq_fragment]

private theorem ofPatternNonempty_eq_fragment
    (values : NonemptyList Pattern) :
    ofPatternNonempty values = patternNonemptyFragment values := by
  rcases values with ⟨head, tail⟩
  simp [ofPatternNonempty, patternNonemptyFragment, merge,
    ofPattern, ofPatternList_eq_fragment]

private theorem ofMatchArmNonempty_eq_fragment
    (values : NonemptyList MatchArm) :
    ofMatchArmNonempty values = matchArmNonemptyFragment values := by
  rcases values with ⟨head, tail⟩
  simp [ofMatchArmNonempty, matchArmNonemptyFragment, merge,
    ofMatchArm, ofMatchArmList_eq_fragment]

/-- A braced body retains both braces under the body wrapper. -/
@[simp] theorem ofBody_braced (span openBrace closeBrace : SourceSpan)
    (statements : List Statement) :
    ofBody ⟨span, ⟨.braced openBrace closeBrace, statements⟩⟩ =
      located span [merge [raw openBrace, raw closeBrace,
        ofStatementList statements]] := by
  unfold ofBody
  rw [bodyFragment, bodyPayloadFragment]
  rw [ofStatementList_eq_fragment]
  rfl

/-- A match-arm body exposes its fat arrow as a root for the enclosing arm. -/
@[simp] theorem ofBody_matchArm (span fatArrow : SourceSpan)
    (statements : List Statement) :
    ofBody ⟨span, ⟨.matchArm fatArrow, statements⟩⟩ =
      locatedWithPromotedRoots span [fatArrow]
        [ofStatementList statements] := by
  unfold ofBody
  rw [bodyFragment, bodyPayloadFragment]
  rw [ofStatementList_eq_fragment]
  rfl

/-- The exact child fragment below one match-arm wrapper. -/
def ofMatchArmPayload (payload : MatchArmPayload) : LocationFragment :=
  merge [ofPatternNonempty payload.patterns, ofBody payload.body]

private theorem ofMatchArmPayload_eq_fragment
    (payload : MatchArmPayload) :
    ofMatchArmPayload payload = matchArmPayloadFragment payload := by
  rcases payload with ⟨patterns, body⟩
  simp only [ofMatchArmPayload, matchArmPayloadFragment]
  rw [ofPatternNonempty_eq_fragment]
  rfl

/-- A match-arm visitor is exactly its outer span around its public payload
fragment. -/
@[simp] theorem ofMatchArm_mk (span : SourceSpan)
    (payload : MatchArmPayload) :
    ofMatchArm ⟨span, payload⟩ =
      located span [ofMatchArmPayload payload] := by
  unfold ofMatchArm
  rw [matchArmFragment]
  rw [ofMatchArmPayload_eq_fragment]
  rfl

/-- The exact child fragment below one statement wrapper. -/
def ofStatementPayload : StatementPayload → LocationFragment
  | .assignment operator left right =>
      merge [ofAssignmentOperator operator, ofExpression left,
        ofExpression right]
  | .letBinding binding => ofLetBinding binding
  | .block body => ofBody body
  | .expression expression terminator =>
      merge [ofExpression expression, ofOption raw terminator]
  | .return value terminator =>
      merge [ofOption ofExpression value, raw terminator]
  | .match scrutinees arms terminator =>
      merge [ofExpressionNonempty scrutinees,
        ofMatchArmNonempty arms, ofOption raw terminator]
  | .assembly slice => ofAssemblySlice slice
  | .ifThenElse condition thenBody elseBody =>
      merge [ofExpression condition, ofBody thenBody,
        ofOption ofBody elseBody]
  | .forLoop initializers condition post body =>
      merge [ofForInitItemList initializers, ofExpression condition,
        ofForPostItemList post, ofBody body]
  | .break terminator => raw terminator
  | .continue terminator => raw terminator

private theorem ofStatementPayload_eq_fragment
    (payload : StatementPayload) :
    ofStatementPayload payload = statementPayloadFragment payload := by
  cases payload with
  | assignment operator left right => rfl
  | letBinding binding => rfl
  | block body => rfl
  | expression expression terminator =>
      cases terminator <;> rfl
  | «return» value terminator =>
      cases value <;> rfl
  | «match» scrutinees arms terminator =>
      simp only [ofStatementPayload, statementPayloadFragment]
      rw [ofExpressionNonempty_eq_fragment,
        ofMatchArmNonempty_eq_fragment]
      cases terminator <;> rfl
  | assembly slice => rfl
  | ifThenElse condition thenBody elseBody =>
      cases elseBody <;> rfl
  | forLoop initializers condition post body =>
      simp only [ofStatementPayload, statementPayloadFragment]
      rw [ofForInitItemList_eq_fragment,
        ofForPostItemList_eq_fragment]
      rfl
  | «break» terminator => rfl
  | «continue» terminator => rfl

/-- A statement visitor is exactly its outer span around its public payload
fragment. -/
@[simp] theorem ofStatement_mk (span : SourceSpan)
    (payload : StatementPayload) :
    ofStatement ⟨span, payload⟩ =
      located span [ofStatementPayload payload] := by
  unfold ofStatement
  rw [statementFragment]
  rw [ofStatementPayload_eq_fragment]
  rfl

/-- Proof-facing traversal of one located import selection. -/
def ofImportSelection (selection : ImportSelection) : LocationFragment :=
  importSelectionFragment selection

@[simp] theorem ofImportSelection_mk (span : SourceSpan)
    (entries : List ImportSelectorEntry) :
    ofImportSelection ⟨span, ⟨entries⟩⟩ =
      located span [merge (entries.map ofImportSelectorEntry)] := by
  rfl

/-- The unlocated import mode retains the roots of its located children. -/
def ofImportMode : ImportMode → LocationFragment
  | .module alias => ofOption ofIdentifier alias
  | .items selection hidingClause =>
      merge [ofImportSelection selection,
        ofOption ofHidingClause hidingClause]

private theorem ofImportMode_eq_fragment (mode : ImportMode) :
    ofImportMode mode = importModeFragment mode := by
  cases mode <;> rfl

/-- An import declaration exposes its module reference and import-mode roots
under the declaration wrapper. -/
@[simp] theorem ofImportDecl_mk (span : SourceSpan)
    (moduleRef : ModuleReference) (mode : ImportMode) :
    ofImportDecl ⟨span, ⟨moduleRef, mode⟩⟩ =
      located span [ofModuleReference moduleRef, ofImportMode mode] := by
  unfold ofImportDecl
  rw [importDeclFragment]
  rw [ofImportMode_eq_fragment]
  rfl

/-- Proof-facing traversal of one local export list. -/
def ofLocalExportList (selection : LocalExportList) : LocationFragment :=
  localExportListFragment selection

@[simp] theorem ofLocalExportList_mk (span : SourceSpan)
    (entries : List ExportEntry) :
    ofLocalExportList ⟨span, ⟨entries⟩⟩ =
      located span [merge (entries.map ofExportEntry)] := by
  rfl

/-- Proof-facing traversal of one remote export selection. -/
def ofRemoteExportSelection (selection : RemoteExportSelection) :
    LocationFragment :=
  remoteExportSelectionFragment selection

@[simp] theorem ofRemoteExportSelection_dotWildcard
    (span : SourceSpan) (marker : Marker) :
    ofRemoteExportSelection ⟨span, .dotWildcard marker⟩ =
      located span [leaf marker.span] := by
  rfl

@[simp] theorem ofRemoteExportSelection_braced
    (span : SourceSpan) (entries : List RemoteExportEntry) :
    ofRemoteExportSelection ⟨span, .braced entries⟩ =
      located span [merge (entries.map ofRemoteExportEntry)] := by
  rfl

/-- A local export declaration retains its located selection directly. -/
@[simp] theorem ofExportDecl_local (span : SourceSpan)
    (selection : LocalExportList) :
    ofExportDecl ⟨span, .local selection⟩ =
      located span [ofLocalExportList selection] := by
  rfl

/-- A module export declaration retains its reference and optional alias. -/
@[simp] theorem ofExportDecl_module (span : SourceSpan)
    (moduleRef : ModuleReference) (alias : Option IdentifierOccurrence) :
    ofExportDecl ⟨span, .module moduleRef alias⟩ =
      located span [ofModuleReference moduleRef,
        ofOption ofIdentifier alias] := by
  cases alias <;> rfl

/-- A remote export declaration retains its reference and selection. -/
@[simp] theorem ofExportDecl_from (span : SourceSpan)
    (moduleRef : ModuleReference) (selection : RemoteExportSelection) :
    ofExportDecl ⟨span, .from moduleRef selection⟩ =
      located span [ofModuleReference moduleRef,
        ofRemoteExportSelection selection] := by
  rfl

/-- Proof-facing traversal of one complete parsed module. -/
def ofParsedModule (module : ParsedModuleV1) : LocationFragment :=
  parsedModuleFragment module

@[simp] theorem ofParsedModule_roots (module : ParsedModuleV1) :
    (ofParsedModule module).roots = [module.span] := by
  rfl

@[simp] theorem ofParsedModule_mk (span : SourceSpan) (source : SourceId)
    (items : List TopItem) :
    ofParsedModule ⟨span, ⟨source, items⟩⟩ =
      located span [merge (items.map ofTopItem)] := by
  rfl

end LocationFragment

/-- Traverse one complete parsed module exactly once to collect its locations. -/
def locationInventory (module : ParsedModuleV1) : LocationInventory :=
  (LocationFragment.ofParsedModule module).inventory

/-- The proof-facing module fragment uses the canonical public inventory. -/
@[simp] theorem LocationFragment.ofParsedModule_inventory
    (module : ParsedModuleV1) :
    (LocationFragment.ofParsedModule module).inventory =
      locationInventory module := by
  rfl

/-- Every located wrapper and retained raw span is valid for the source file. -/
def AllLocationsValid (file : WorkspaceFile) (module : ParsedModuleV1) : Prop :=
  (locationInventory module).ValidFor file

/-- Every direct AST parent location contains its retained child location. -/
def AllLocationsNested (module : ParsedModuleV1) : Prop :=
  (locationInventory module).Nested

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
  simp [locationsValid, AllLocationsValid, LocationInventory.ValidFor,
    SourceSpan.isValidFor_eq_true_iff]

/-- Execute the direct parent-child containment check for a module. -/
def locationsNested (module : ParsedModuleV1) : Bool :=
  (locationInventory module).containments.all fun containment =>
    containment.1.contains containment.2

/-- The executable nesting check decides its logical predicate. -/
@[simp] theorem locationsNested_eq_true_iff (module : ParsedModuleV1) :
    locationsNested module = true ↔ AllLocationsNested module := by
  simp [locationsNested, AllLocationsNested, LocationInventory.Nested,
    SourceSpan.contains_eq_true_iff]

/-- Execute the complete location-validity and nesting check. -/
def everyLocationValid (file : WorkspaceFile) (module : ParsedModuleV1) : Bool :=
  locationsValid file module && locationsNested module

/-- The complete executable check decides `EveryLocationValid`. -/
@[simp] theorem everyLocationValid_eq_true_iff
    (file : WorkspaceFile) (module : ParsedModuleV1) :
    everyLocationValid file module = true ↔ EveryLocationValid file module := by
  simp [everyLocationValid, EveryLocationValid]

end Solcore.Surface.Multi
