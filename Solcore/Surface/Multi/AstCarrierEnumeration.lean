import Solcore.Surface.Multi.ResourceBounds

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- A concrete sequence of AST-carrier occurrences together with its checked
cardinality.  The cached cardinality lets the traversal retain the arithmetic
shape used by `astNodeMeasure`, while the final field proves that it counts the
materialized sequence. -/
structure AstCarrierFragment where
  occurrences : List AstCarrier
  cardinality : Nat
  cardinality_eq_length : cardinality = occurrences.length

namespace AstCarrierFragment

private def empty : AstCarrierFragment := {
  occurrences := []
  cardinality := 0
  cardinality_eq_length := rfl
}

private def singleton (carrier : AstCarrier) : AstCarrierFragment := {
  occurrences := [carrier]
  cardinality := 1
  cardinality_eq_length := rfl
}

private def append (left right : AstCarrierFragment) :
    AstCarrierFragment := {
  occurrences := left.occurrences ++ right.occurrences
  cardinality := left.cardinality + right.cardinality
  cardinality_eq_length := by
    simp only [List.length_append]
    rw [left.cardinality_eq_length, right.cardinality_eq_length]
}

private def group : List AstCarrierFragment → AstCarrierFragment
  | [] => empty
  | head :: tail => append head (group tail)

private def extend (base : AstCarrierFragment)
    (children : List AstCarrierFragment) : AstCarrierFragment :=
  children.foldl append base

private def ofList {alpha : Type} (visit : alpha → AstCarrierFragment) :
    List alpha → AstCarrierFragment
  | [] => empty
  | head :: tail => append (visit head) (ofList visit tail)

private def ofOption {alpha : Type} (visit : alpha → AstCarrierFragment) :
    Option alpha → AstCarrierFragment
  | none => empty
  | some value => visit value

private def ofNonempty {alpha : Type} (visit : alpha → AstCarrierFragment)
    (values : NonemptyList alpha) : AstCarrierFragment :=
  append (visit values.head) (ofList visit values.tail)

private theorem ofList_cardinality
    {alpha : Type} (visit : alpha → AstCarrierFragment)
    (measure : alpha → Nat)
    (same : ∀ value, (visit value).cardinality = measure value)
    (values : List alpha) :
    (ofList visit values).cardinality =
      AstCarrierMeasure.list measure values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [ofList, append]
      rw [same head, ih]
      rfl

private theorem ofOption_cardinality
    {alpha : Type} (visit : alpha → AstCarrierFragment)
    (measure : alpha → Nat)
    (same : ∀ value, (visit value).cardinality = measure value)
    (value : Option alpha) :
    (ofOption visit value).cardinality =
      AstCarrierMeasure.option measure value := by
  cases value with
  | none => rfl
  | some value => exact same value

private theorem ofNonempty_cardinality
    {alpha : Type} (visit : alpha → AstCarrierFragment)
    (measure : alpha → Nat)
    (same : ∀ value, (visit value).cardinality = measure value)
    (values : NonemptyList alpha) :
    (ofNonempty visit values).cardinality =
      AstCarrierMeasure.nonemptyList measure values := by
  cases values with
  | mk head tail =>
      simp only [ofNonempty, append]
      rw [same head, ofList_cardinality visit measure same tail]
      rfl

private def carrierPair (sort : AstCarrierSort) : AstCarrierFragment := {
  occurrences := [.located sort, .payload sort]
  cardinality := 2
  cardinality_eq_length := rfl
}

private def payloadCarrier (sort : AstCarrierSort) : AstCarrierFragment :=
  singleton (.payload sort)

private def locatedCarrier (sort : AstCarrierSort)
    (payload : AstCarrierFragment) : AstCarrierFragment :=
  append (singleton (.located sort)) payload

private def identifierFragment (_ : IdentifierOccurrence) :
    AstCarrierFragment :=
  carrierPair .identifier

private def pathComponentFragment (_ : PathComponent) :
    AstCarrierFragment :=
  carrierPair .pathComponent

private def externalLibraryNameFragment (_ : Located ExternalLibraryName) :
    AstCarrierFragment :=
  carrierPair .externalLibraryName

private def markerFragment (_ : Marker) : AstCarrierFragment :=
  carrierPair .syntaxMarker

private def unitMarkerFragment (_ : Located Unit) : AstCarrierFragment :=
  carrierPair .unitMarker

private def pragmaKindFragment (_ : Located PragmaKind) : AstCarrierFragment :=
  carrierPair .pragmaKind

private def prefixOperatorFragment (_ : Located PrefixOperator) :
    AstCarrierFragment :=
  carrierPair .prefixOperator

private def infixOperatorFragment (_ : Located InfixOperator) :
    AstCarrierFragment :=
  carrierPair .infixOperator

private def assignmentOperatorFragment (_ : Located AssignmentOperator) :
    AstCarrierFragment :=
  carrierPair .assignmentOperator

private def assemblySliceFragment (_ : AssemblySlice) : AstCarrierFragment :=
  carrierPair .assemblySlice

private def qualifiedNameFragment (name : QualifiedName) :
    AstCarrierFragment :=
  append (carrierPair .qualifiedName)
    (ofNonempty identifierFragment name.payload.components)

private def moduleReferenceFragment (reference : ModuleReference) :
    AstCarrierFragment :=
  let children :=
    match reference.payload with
    | .relative components =>
        ofNonempty pathComponentFragment components
    | .libraryRoot marker tail =>
        append (markerFragment marker)
          (ofNonempty pathComponentFragment tail)
    | .standard marker tail =>
        append (markerFragment marker) (ofList pathComponentFragment tail)
    | .external atMarker library tail =>
        extend (markerFragment atMarker) [
          externalLibraryNameFragment library,
          ofNonempty pathComponentFragment tail
        ]
  append (carrierPair .moduleReference) children

private def importSelectorEntryFragment (entry : ImportSelectorEntry) :
    AstCarrierFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => markerFragment marker
    | .named source alias =>
        append (identifierFragment source)
          (ofOption identifierFragment alias)
  append (carrierPair .importSelectorEntry) children

private def importSelectionFragment (selection : ImportSelection) :
    AstCarrierFragment :=
  append (carrierPair .importSelection)
    (ofList importSelectorEntryFragment selection.payload.entries)

private def hidingClauseFragment (clause : HidingClause) :
    AstCarrierFragment :=
  append (carrierPair .hidingClause)
    (ofList identifierFragment clause.payload.names)

private def importModeFragment (mode : ImportMode) : AstCarrierFragment :=
  let children :=
    match mode with
    | .module alias => ofOption identifierFragment alias
    | .items selection hidingClause =>
        append (importSelectionFragment selection)
          (ofOption hidingClauseFragment hidingClause)
  append (payloadCarrier .importMode) children

private def importDeclFragment (declaration : ImportDecl) :
    AstCarrierFragment :=
  extend (carrierPair .importDecl) [
    moduleReferenceFragment declaration.payload.moduleRef,
    importModeFragment declaration.payload.mode
  ]

private def constructorSelectionFragment (selection : ConstructorSelection) :
    AstCarrierFragment :=
  let children :=
    match selection.payload with
    | .all marker => markerFragment marker
    | .named constructors => ofNonempty identifierFragment constructors
  append (carrierPair .constructorSelection) children

private def exportItemFragment (item : ExportItem) : AstCarrierFragment :=
  extend (carrierPair .exportItem) [
    identifierFragment item.payload.name,
    ofOption constructorSelectionFragment item.payload.constructors
  ]

private def exportEntryFragment (entry : ExportEntry) : AstCarrierFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => markerFragment marker
    | .item item => exportItemFragment item
    | .allFrom moduleRef marker =>
        append (moduleReferenceFragment moduleRef) (markerFragment marker)
  append (carrierPair .exportEntry) children

private def localExportListFragment (selection : LocalExportList) :
    AstCarrierFragment :=
  append (carrierPair .localExportList)
    (ofList exportEntryFragment selection.payload.entries)

private def remoteExportEntryFragment (entry : RemoteExportEntry) :
    AstCarrierFragment :=
  let children :=
    match entry.payload with
    | .wildcard marker => markerFragment marker
    | .item item => exportItemFragment item
  append (carrierPair .remoteExportEntry) children

private def remoteExportSelectionFragment
    (selection : RemoteExportSelection) : AstCarrierFragment :=
  let children :=
    match selection.payload with
    | .dotWildcard marker => markerFragment marker
    | .braced entries => ofList remoteExportEntryFragment entries
  append (carrierPair .remoteExportSelection) children

private def exportModeFragment (declaration : ExportDecl) :
    AstCarrierFragment :=
  let children :=
    match declaration.payload with
    | .local selection => localExportListFragment selection
    | .module moduleRef alias =>
        append (moduleReferenceFragment moduleRef)
          (ofOption identifierFragment alias)
    | .from moduleRef selection =>
        append (moduleReferenceFragment moduleRef)
          (remoteExportSelectionFragment selection)
  append (carrierPair .exportMode) children

private def literalFragment (literal : Literal) : AstCarrierFragment :=
  let payload :=
    match literal.payload with
    | .decimal _ _ => payloadCarrier .literal
    | .hexadecimal _ _ => payloadCarrier .literal
    | .string _ _ => payloadCarrier .literal
  locatedCarrier .literal payload

private theorem qualifiedNameFragment_cardinality
    (name : QualifiedName) :
    (qualifiedNameFragment name).cardinality =
      AstCarrierMeasure.qualifiedName name := by
  simp only [qualifiedNameFragment, append]
  rw [ofNonempty_cardinality identifierFragment
    AstCarrierMeasure.identifier (fun _ => rfl)]
  rfl

private theorem moduleReferenceFragment_cardinality
    (reference : ModuleReference) :
    (moduleReferenceFragment reference).cardinality =
      AstCarrierMeasure.moduleReference reference := by
  cases reference with
  | mk span payload =>
      cases payload with
      | relative components =>
          simp only [moduleReferenceFragment, append,
            AstCarrierMeasure.moduleReference]
          rw [ofNonempty_cardinality pathComponentFragment
            AstCarrierMeasure.pathComponent (fun _ => rfl)]
          rfl
      | libraryRoot marker tail =>
          simp only [moduleReferenceFragment, append,
            AstCarrierMeasure.moduleReference]
          rw [ofNonempty_cardinality pathComponentFragment
            AstCarrierMeasure.pathComponent (fun _ => rfl)]
          rfl
      | standard marker tail =>
        simp only [moduleReferenceFragment, append,
          AstCarrierMeasure.moduleReference]
        rw [ofList_cardinality pathComponentFragment
          AstCarrierMeasure.pathComponent (fun _ => rfl)]
        rfl
      | external atMarker library tail =>
          simp only [moduleReferenceFragment, extend, List.foldl, append,
            AstCarrierMeasure.moduleReference]
          rw [ofNonempty_cardinality pathComponentFragment
            AstCarrierMeasure.pathComponent (fun _ => rfl)]
          rfl

private theorem importSelectorEntryFragment_cardinality
    (entry : ImportSelectorEntry) :
    (importSelectorEntryFragment entry).cardinality =
      AstCarrierMeasure.importSelectorEntry entry := by
  cases entry with
  | mk span payload =>
      cases payload <;>
        simp only [importSelectorEntryFragment, append,
          AstCarrierMeasure.importSelectorEntry]
      · rfl
      · rw [ofOption_cardinality identifierFragment
          AstCarrierMeasure.identifier (fun _ => rfl)]
        rfl

private theorem importSelectionFragment_cardinality
    (selection : ImportSelection) :
    (importSelectionFragment selection).cardinality =
      AstCarrierMeasure.importSelection selection := by
  simp only [importSelectionFragment, append,
    AstCarrierMeasure.importSelection]
  rw [ofList_cardinality importSelectorEntryFragment
    AstCarrierMeasure.importSelectorEntry
    importSelectorEntryFragment_cardinality]
  rfl

private theorem hidingClauseFragment_cardinality (clause : HidingClause) :
    (hidingClauseFragment clause).cardinality =
      AstCarrierMeasure.hidingClause clause := by
  simp only [hidingClauseFragment, append, AstCarrierMeasure.hidingClause]
  rw [ofList_cardinality identifierFragment AstCarrierMeasure.identifier
    (fun _ => rfl)]
  rfl

private theorem importModeFragment_cardinality (mode : ImportMode) :
    (importModeFragment mode).cardinality =
      AstCarrierMeasure.importMode mode := by
  cases mode <;>
    simp only [importModeFragment, append, AstCarrierMeasure.importMode]
  · rw [ofOption_cardinality identifierFragment AstCarrierMeasure.identifier
      (fun _ => rfl)]
    rfl
  · rw [importSelectionFragment_cardinality]
    rw [ofOption_cardinality hidingClauseFragment
      AstCarrierMeasure.hidingClause hidingClauseFragment_cardinality]
    rfl

private theorem importDeclFragment_cardinality (declaration : ImportDecl) :
    (importDeclFragment declaration).cardinality =
      AstCarrierMeasure.importDecl declaration := by
  simp only [importDeclFragment, extend, List.foldl, append,
    AstCarrierMeasure.importDecl]
  rw [moduleReferenceFragment_cardinality, importModeFragment_cardinality]
  rfl

private theorem constructorSelectionFragment_cardinality
    (selection : ConstructorSelection) :
    (constructorSelectionFragment selection).cardinality =
      AstCarrierMeasure.constructorSelection selection := by
  cases selection with
  | mk span payload =>
      cases payload <;>
        simp only [constructorSelectionFragment, append,
          AstCarrierMeasure.constructorSelection]
      · rfl
      · rw [ofNonempty_cardinality identifierFragment
          AstCarrierMeasure.identifier (fun _ => rfl)]
        rfl

private theorem exportItemFragment_cardinality (item : ExportItem) :
    (exportItemFragment item).cardinality =
      AstCarrierMeasure.exportItem item := by
  simp only [exportItemFragment, extend, List.foldl, append,
    AstCarrierMeasure.exportItem]
  rw [ofOption_cardinality constructorSelectionFragment
    AstCarrierMeasure.constructorSelection
    constructorSelectionFragment_cardinality]
  rfl

private theorem exportEntryFragment_cardinality (entry : ExportEntry) :
    (exportEntryFragment entry).cardinality =
      AstCarrierMeasure.exportEntry entry := by
  cases entry with
  | mk span payload =>
      cases payload <;>
        simp only [exportEntryFragment, append,
          AstCarrierMeasure.exportEntry]
      · rfl
      · rw [exportItemFragment_cardinality]
        rfl
      · rw [moduleReferenceFragment_cardinality]
        rfl

private theorem localExportListFragment_cardinality
    (selection : LocalExportList) :
    (localExportListFragment selection).cardinality =
      AstCarrierMeasure.localExportList selection := by
  simp only [localExportListFragment, append,
    AstCarrierMeasure.localExportList]
  rw [ofList_cardinality exportEntryFragment AstCarrierMeasure.exportEntry
    exportEntryFragment_cardinality]
  rfl

private theorem remoteExportEntryFragment_cardinality
    (entry : RemoteExportEntry) :
    (remoteExportEntryFragment entry).cardinality =
      AstCarrierMeasure.remoteExportEntry entry := by
  cases entry with
  | mk span payload =>
      cases payload <;>
        simp only [remoteExportEntryFragment, append,
          AstCarrierMeasure.remoteExportEntry]
      · rfl
      · rw [exportItemFragment_cardinality]
        rfl

private theorem remoteExportSelectionFragment_cardinality
    (selection : RemoteExportSelection) :
    (remoteExportSelectionFragment selection).cardinality =
      AstCarrierMeasure.remoteExportSelection selection := by
  cases selection with
  | mk span payload =>
      cases payload <;>
        simp only [remoteExportSelectionFragment, append,
          AstCarrierMeasure.remoteExportSelection]
      · rfl
      · rw [ofList_cardinality remoteExportEntryFragment
          AstCarrierMeasure.remoteExportEntry
          remoteExportEntryFragment_cardinality]
        rfl

private theorem exportModeFragment_cardinality (declaration : ExportDecl) :
    (exportModeFragment declaration).cardinality =
      AstCarrierMeasure.exportMode declaration := by
  cases declaration with
  | mk span payload =>
      cases payload <;>
        simp only [exportModeFragment, append, AstCarrierMeasure.exportMode]
      · rw [localExportListFragment_cardinality]
        rfl
      · rw [moduleReferenceFragment_cardinality]
        rw [ofOption_cardinality identifierFragment
          AstCarrierMeasure.identifier (fun _ => rfl)]
        rfl
      · rw [moduleReferenceFragment_cardinality,
          remoteExportSelectionFragment_cardinality]
        rfl

private theorem literalFragment_cardinality (literal : Literal) :
    (literalFragment literal).cardinality =
      AstCarrierMeasure.literal literal := by
  cases literal with
  | mk span payload => cases payload <;> rfl

mutual

private def typeExprPayloadFragment : TypeExprPayload → AstCarrierFragment
  | .named name arguments =>
      extend (payloadCarrier .typeExpr) [
        qualifiedNameFragment name,
        typeExprArgumentsFragment arguments
      ]
  | .proxy marker inner =>
      extend (payloadCarrier .typeExpr) [
        unitMarkerFragment marker,
        typeExprFragment inner
      ]
  | .function domain codomain =>
      extend (payloadCarrier .typeExpr) [
        typeExprFragment domain,
        typeExprFragment codomain
      ]
  | .tuple elements =>
      append (payloadCarrier .typeExpr) (typeExprListFragment elements)
  | .group inner =>
      append (payloadCarrier .typeExpr) (typeExprFragment inner)
  | .comptime marker inner =>
      extend (payloadCarrier .typeExpr) [
        markerFragment marker,
        typeExprFragment inner
      ]

private def typeExprFragment : TypeExpr → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .typeExpr (typeExprPayloadFragment payload)

private def typeExprArgumentsFragment :
    Option (NonemptyList TypeExpr) → AstCarrierFragment
  | none => empty
  | some arguments => typeExprNonemptyFragment arguments

private def typeExprNonemptyFragment :
    NonemptyList TypeExpr → AstCarrierFragment
  | ⟨head, tail⟩ =>
      append (typeExprFragment head) (typeExprListFragment tail)

private def typeExprListFragment : List TypeExpr → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (typeExprFragment head) (typeExprListFragment tail)

end

set_option linter.unusedSimpArgs false in
private theorem typeExprFragment_cardinality (value : TypeExpr) :
    (typeExprFragment value).cardinality =
      AstCarrierMeasure.typeExpr value := by
  apply typeExprFragment.induct
    (motive_1 := fun payload =>
      (typeExprPayloadFragment payload).cardinality =
        AstCarrierMeasure.typeExprPayload payload)
    (motive_2 := fun values =>
      (typeExprListFragment values).cardinality =
        AstCarrierMeasure.typeExprList values)
    (motive_3 := fun value =>
      (typeExprFragment value).cardinality =
        AstCarrierMeasure.typeExpr value)
    (motive_4 := fun value =>
      (typeExprArgumentsFragment value).cardinality =
        AstCarrierMeasure.typeExprArguments value)
    (motive_5 := fun values =>
      (typeExprNonemptyFragment values).cardinality =
        AstCarrierMeasure.typeExprNonempty values) <;>
    simp_all (config := { failIfUnchanged := false }) [
      typeExprFragment, typeExprPayloadFragment,
      typeExprArgumentsFragment, typeExprNonemptyFragment,
      typeExprListFragment, locatedCarrier, payloadCarrier, append, extend,
      empty, singleton, carrierPair, markerFragment, unitMarkerFragment,
      AstCarrierMeasure.typeExpr,
      AstCarrierMeasure.typeExprPayload,
      AstCarrierMeasure.typeExprArguments,
      AstCarrierMeasure.typeExprNonempty,
      AstCarrierMeasure.typeExprList,
      typeExprMeasure, typeExprPayloadMeasure, typeExprArgumentsMeasure,
      typeExprNonemptyMeasure, typeExprListMeasure, markerMeasure,
      unitMarkerMeasure,
      qualifiedNameFragment_cardinality]

private def forallBinderFragment (binder : ForallBinder) :
    AstCarrierFragment :=
  let children :=
    match binder.payload with
    | .bare name => identifierFragment name
    | .bounded name className arguments =>
        extend (identifierFragment name) [
          qualifiedNameFragment className,
          ofOption (ofNonempty typeExprFragment) arguments
        ]
  append (carrierPair .forallBinder) children

private def forallClauseFragment (clause : ForallClause) :
    AstCarrierFragment :=
  append (carrierPair .forallClause)
    (ofNonempty forallBinderFragment clause.payload.binders)

private def predicateFragment (predicate : Predicate) :
    AstCarrierFragment :=
  extend (carrierPair .predicate) [
    typeExprFragment predicate.payload.main,
    qualifiedNameFragment predicate.payload.className,
    ofOption (ofNonempty typeExprFragment) predicate.payload.parameters
  ]

private def genericPrefixFragment (genericPrefix : GenericPrefix) :
    AstCarrierFragment :=
  extend (carrierPair .genericPrefix) [
    forallClauseFragment genericPrefix.payload.forallClause,
    ofOption (ofNonempty predicateFragment) genericPrefix.payload.context
  ]

private def parameterFragment (parameter : Parameter) :
    AstCarrierFragment :=
  extend (carrierPair .parameter) [
    ofOption markerFragment parameter.payload.comptime,
    identifierFragment parameter.payload.name,
    ofOption typeExprFragment parameter.payload.type
  ]

private def functionSignatureFragment (signature : FunctionSignature) :
    AstCarrierFragment :=
  extend (carrierPair .functionSignature) [
    ofOption genericPrefixFragment signature.payload.genericPrefix,
    ofOption markerFragment signature.payload.public,
    ofOption markerFragment signature.payload.payable,
    identifierFragment signature.payload.name,
    ofList parameterFragment signature.payload.parameters,
    ofOption typeExprFragment signature.payload.returnType
  ]

set_option linter.unusedSimpArgs false in
private theorem forallBinderFragment_cardinality (binder : ForallBinder) :
    (forallBinderFragment binder).cardinality =
      AstCarrierMeasure.forallBinder binder := by
  cases binder with
  | mk span payload =>
      cases payload <;>
        simp [forallBinderFragment, forallBinderMeasure, append, extend,
          carrierPair, identifierFragment, qualifiedNameFragment_cardinality,
          typeExprFragment_cardinality, ofOption_cardinality,
          ofNonempty_cardinality, identifierMeasure]

private theorem forallClauseFragment_cardinality (clause : ForallClause) :
    (forallClauseFragment clause).cardinality =
      AstCarrierMeasure.forallClause clause := by
  simp only [forallClauseFragment, append, forallClauseMeasure]
  rw [ofNonempty_cardinality forallBinderFragment
    AstCarrierMeasure.forallBinder forallBinderFragment_cardinality]
  rfl

set_option linter.unusedSimpArgs false in
private theorem predicateFragment_cardinality (predicate : Predicate) :
    (predicateFragment predicate).cardinality =
      AstCarrierMeasure.predicate predicate := by
  simp [predicateFragment, predicateMeasure, extend, append, carrierPair,
    typeExprFragment_cardinality, qualifiedNameFragment_cardinality,
    ofOption_cardinality, ofNonempty_cardinality]

set_option linter.unusedSimpArgs false in
private theorem genericPrefixFragment_cardinality (value : GenericPrefix) :
    (genericPrefixFragment value).cardinality =
      AstCarrierMeasure.genericPrefix value := by
  simp [genericPrefixFragment, genericPrefixMeasure, extend, append,
    carrierPair, forallClauseFragment_cardinality,
    ofOption_cardinality, ofNonempty_cardinality,
    predicateFragment_cardinality]

set_option linter.unusedSimpArgs false in
private theorem parameterFragment_cardinality (parameter : Parameter) :
    (parameterFragment parameter).cardinality =
      AstCarrierMeasure.parameter parameter := by
  simp [parameterFragment, parameterMeasure, extend, append, carrierPair,
    ofOption_cardinality, markerFragment, identifierFragment,
    typeExprFragment_cardinality, markerMeasure, identifierMeasure,
    measureOption, AstCarrierMeasure.option, AstCarrierMeasure.typeExpr]

set_option linter.unusedSimpArgs false in
private theorem functionSignatureFragment_cardinality
    (signature : FunctionSignature) :
    (functionSignatureFragment signature).cardinality =
      AstCarrierMeasure.functionSignature signature := by
  simp [functionSignatureFragment, functionSignatureMeasure, extend, append,
    carrierPair, ofOption_cardinality, ofList_cardinality,
    genericPrefixFragment_cardinality, markerFragment, identifierFragment,
    parameterFragment_cardinality, typeExprFragment_cardinality,
    markerMeasure, identifierMeasure, measureOption, measureList,
    AstCarrierMeasure.option, AstCarrierMeasure.list,
    AstCarrierMeasure.genericPrefix, AstCarrierMeasure.parameter,
    AstCarrierMeasure.typeExpr]

mutual

private def expressionPayloadFragment : ExpressionPayload → AstCarrierFragment
  | .name name =>
      append (payloadCarrier .expression) (identifierFragment name)
  | .call callee arguments =>
      extend (payloadCarrier .expression) [
        expressionFragment callee,
        expressionListFragment arguments
      ]
  | .select receiver field =>
      extend (payloadCarrier .expression) [
        expressionFragment receiver,
        identifierFragment field
      ]
  | .dotConstructor marker name arguments =>
      extend (payloadCarrier .expression) [
        unitMarkerFragment marker,
        identifierFragment name,
        expressionListOptionFragment arguments
      ]
  | .proxy marker typeExpression =>
      extend (payloadCarrier .expression) [
        unitMarkerFragment marker,
        typeExprFragment typeExpression
      ]
  | .literal literal =>
      append (payloadCarrier .expression) (literalFragment literal)
  | .lambda parameters returnType body =>
      extend (payloadCarrier .expression) [
        ofList parameterFragment parameters,
        ofOption typeExprFragment returnType,
        bodyFragment body
      ]
  | .annotation expression typeExpression =>
      extend (payloadCarrier .expression) [
        expressionFragment expression,
        typeExprFragment typeExpression
      ]
  | .keywordConditional condition thenBranch elseBranch =>
      extend (payloadCarrier .expression) [
        expressionFragment condition,
        expressionFragment thenBranch,
        expressionFragment elseBranch
      ]
  | .ternaryConditional condition thenBranch elseBranch =>
      extend (payloadCarrier .expression) [
        expressionFragment condition,
        expressionFragment thenBranch,
        expressionFragment elseBranch
      ]
  | .index receiver index =>
      extend (payloadCarrier .expression) [
        expressionFragment receiver,
        expressionFragment index
      ]
  | .prefix operator operand =>
      extend (payloadCarrier .expression) [
        prefixOperatorFragment operator,
        expressionFragment operand
      ]
  | .infix operator left right =>
      extend (payloadCarrier .expression) [
        infixOperatorFragment operator,
        expressionFragment left,
        expressionFragment right
      ]
  | .tuple elements =>
      append (payloadCarrier .expression) (expressionListFragment elements)
  | .group inner =>
      append (payloadCarrier .expression) (expressionFragment inner)

private def patternPayloadFragment : PatternPayload → AstCarrierFragment
  | .named name arguments =>
      extend (payloadCarrier .pattern) [
        qualifiedNameFragment name,
        patternArgumentsFragment arguments
      ]
  | .dotConstructor marker name arguments =>
      extend (payloadCarrier .pattern) [
        unitMarkerFragment marker,
        identifierFragment name,
        patternArgumentsFragment arguments
      ]
  | .wildcard marker =>
      append (payloadCarrier .pattern) (markerFragment marker)
  | .literal literal =>
      append (payloadCarrier .pattern) (literalFragment literal)
  | .comptime marker expression =>
      extend (payloadCarrier .pattern) [
        markerFragment marker,
        expressionFragment expression
      ]
  | .tuple elements =>
      append (payloadCarrier .pattern) (patternListFragment elements)
  | .group inner =>
      append (payloadCarrier .pattern) (patternFragment inner)

private def bodyPayloadFragment : BodyPayload → AstCarrierFragment
  | ⟨_, statements⟩ =>
      append (payloadCarrier .body) (statementListFragment statements)

private def letBindingPayloadFragment : LetBindingPayload → AstCarrierFragment
  | ⟨comptime, name, typeExpression, initializer⟩ =>
      extend (payloadCarrier .letBinding) [
        ofOption markerFragment comptime,
        identifierFragment name,
        ofOption typeExprFragment typeExpression,
        expressionOptionFragment initializer
      ]

private def forInitItemPayloadFragment :
    ForInitItemPayload → AstCarrierFragment
  | .letBinding binding =>
      append (payloadCarrier .forInitItem) (letBindingFragment binding)
  | .assignment operator left right =>
      extend (payloadCarrier .forInitItem) [
        assignmentOperatorFragment operator,
        expressionFragment left,
        expressionFragment right
      ]
  | .expression expression =>
      append (payloadCarrier .forInitItem) (expressionFragment expression)

private def forPostItemPayloadFragment :
    ForPostItemPayload → AstCarrierFragment
  | .assignment operator left right =>
      extend (payloadCarrier .forPostItem) [
        assignmentOperatorFragment operator,
        expressionFragment left,
        expressionFragment right
      ]
  | .expression expression =>
      append (payloadCarrier .forPostItem) (expressionFragment expression)

private def matchArmPayloadFragment : MatchArmPayload → AstCarrierFragment
  | ⟨patterns, body⟩ =>
      extend (payloadCarrier .matchArm) [
        patternNonemptyFragment patterns,
        bodyFragment body
      ]

private def statementPayloadFragment : StatementPayload → AstCarrierFragment
  | .assignment operator left right =>
      extend (payloadCarrier .statement) [
        assignmentOperatorFragment operator,
        expressionFragment left,
        expressionFragment right
      ]
  | .letBinding binding =>
      append (payloadCarrier .statement) (letBindingFragment binding)
  | .block body =>
      append (payloadCarrier .statement) (bodyFragment body)
  | .expression expression _ =>
      append (payloadCarrier .statement) (expressionFragment expression)
  | .return value _ =>
      append (payloadCarrier .statement) (expressionOptionFragment value)
  | .match scrutinees arms _ =>
      extend (payloadCarrier .statement) [
        expressionNonemptyFragment scrutinees,
        matchArmNonemptyFragment arms
      ]
  | .assembly slice =>
      append (payloadCarrier .statement) (assemblySliceFragment slice)
  | .ifThenElse condition thenBody elseBody =>
      extend (payloadCarrier .statement) [
        expressionFragment condition,
        bodyFragment thenBody,
        bodyOptionFragment elseBody
      ]
  | .forLoop initializers condition post body =>
      extend (payloadCarrier .statement) [
        forInitItemListFragment initializers,
        expressionFragment condition,
        forPostItemListFragment post,
        bodyFragment body
      ]
  | .break _ => payloadCarrier .statement
  | .continue _ => payloadCarrier .statement

private def expressionFragment : Expression → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .expression (expressionPayloadFragment payload)

private def expressionListFragment : List Expression → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (expressionFragment head) (expressionListFragment tail)

private def expressionListOptionFragment :
    Option (List Expression) → AstCarrierFragment
  | none => empty
  | some expressions => expressionListFragment expressions

private def bodyFragment : Body → AstCarrierFragment
  | ⟨_, payload⟩ => locatedCarrier .body (bodyPayloadFragment payload)

private def patternArgumentsFragment :
    Option (NonemptyList Pattern) → AstCarrierFragment
  | none => empty
  | some patterns => patternNonemptyFragment patterns

private def patternListFragment : List Pattern → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (patternFragment head) (patternListFragment tail)

private def patternFragment : Pattern → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .pattern (patternPayloadFragment payload)

private def statementListFragment : List Statement → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (statementFragment head) (statementListFragment tail)

private def expressionOptionFragment : Option Expression → AstCarrierFragment
  | none => empty
  | some expression => expressionFragment expression

private def letBindingFragment : LetBinding → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .letBinding (letBindingPayloadFragment payload)

private def patternNonemptyFragment :
    NonemptyList Pattern → AstCarrierFragment
  | ⟨head, tail⟩ =>
      append (patternFragment head) (patternListFragment tail)

private def expressionNonemptyFragment :
    NonemptyList Expression → AstCarrierFragment
  | ⟨head, tail⟩ =>
      append (expressionFragment head) (expressionListFragment tail)

private def matchArmNonemptyFragment :
    NonemptyList MatchArm → AstCarrierFragment
  | ⟨head, tail⟩ =>
      append (matchArmFragment head) (matchArmListFragment tail)

private def bodyOptionFragment : Option Body → AstCarrierFragment
  | none => empty
  | some body => bodyFragment body

private def forInitItemListFragment :
    List ForInitItem → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (forInitItemFragment head) (forInitItemListFragment tail)

private def forPostItemListFragment :
    List ForPostItem → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (forPostItemFragment head) (forPostItemListFragment tail)

private def statementFragment : Statement → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .statement (statementPayloadFragment payload)

private def matchArmFragment : MatchArm → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .matchArm (matchArmPayloadFragment payload)

private def matchArmListFragment : List MatchArm → AstCarrierFragment
  | [] => empty
  | head :: tail =>
      append (matchArmFragment head) (matchArmListFragment tail)

private def forInitItemFragment : ForInitItem → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .forInitItem (forInitItemPayloadFragment payload)

private def forPostItemFragment : ForPostItem → AstCarrierFragment
  | ⟨_, payload⟩ =>
      locatedCarrier .forPostItem (forPostItemPayloadFragment payload)

end

set_option linter.unusedSimpArgs false in
private theorem expressionFragment_cardinality (value : Expression) :
    (expressionFragment value).cardinality =
      AstCarrierMeasure.expression value := by
  apply expressionFragment.induct
    (motive_1 := fun payload =>
      (expressionPayloadFragment payload).cardinality =
        AstCarrierMeasure.expressionPayload payload)
    (motive_2 := fun body =>
      (bodyFragment body).cardinality = AstCarrierMeasure.body body)
    (motive_3 := fun payload =>
      (bodyPayloadFragment payload).cardinality =
        AstCarrierMeasure.bodyPayload payload)
    (motive_4 := fun values =>
      (statementListFragment values).cardinality =
        AstCarrierMeasure.statementList values)
    (motive_5 := fun statement =>
      (statementFragment statement).cardinality =
        AstCarrierMeasure.statement statement)
    (motive_6 := fun payload =>
      (statementPayloadFragment payload).cardinality =
        AstCarrierMeasure.statementPayload payload)
    (motive_7 := fun values =>
      (forPostItemListFragment values).cardinality =
        AstCarrierMeasure.forPostItemList values)
    (motive_8 := fun item =>
      (forPostItemFragment item).cardinality =
        AstCarrierMeasure.forPostItem item)
    (motive_9 := fun payload =>
      (forPostItemPayloadFragment payload).cardinality =
        AstCarrierMeasure.forPostItemPayload payload)
    (motive_10 := fun expression =>
      (expressionFragment expression).cardinality =
        AstCarrierMeasure.expression expression)
    (motive_11 := fun values =>
      (forInitItemListFragment values).cardinality =
        AstCarrierMeasure.forInitItemList values)
    (motive_12 := fun item =>
      (forInitItemFragment item).cardinality =
        AstCarrierMeasure.forInitItem item)
    (motive_13 := fun payload =>
      (forInitItemPayloadFragment payload).cardinality =
        AstCarrierMeasure.forInitItemPayload payload)
    (motive_14 := fun binding =>
      (letBindingFragment binding).cardinality =
        AstCarrierMeasure.letBinding binding)
    (motive_15 := fun payload =>
      (letBindingPayloadFragment payload).cardinality =
        AstCarrierMeasure.letBindingPayload payload)
    (motive_16 := fun expression =>
      (expressionOptionFragment expression).cardinality =
        AstCarrierMeasure.expressionOption expression)
    (motive_17 := fun body =>
      (bodyOptionFragment body).cardinality =
        AstCarrierMeasure.bodyOption body)
    (motive_18 := fun values =>
      (matchArmNonemptyFragment values).cardinality =
        AstCarrierMeasure.matchArmNonempty values)
    (motive_19 := fun values =>
      (matchArmListFragment values).cardinality =
        AstCarrierMeasure.matchArmList values)
    (motive_20 := fun arm =>
      (matchArmFragment arm).cardinality = AstCarrierMeasure.matchArm arm)
    (motive_21 := fun payload =>
      (matchArmPayloadFragment payload).cardinality =
        AstCarrierMeasure.matchArmPayload payload)
    (motive_22 := fun values =>
      (patternNonemptyFragment values).cardinality =
        AstCarrierMeasure.patternNonempty values)
    (motive_23 := fun values =>
      (patternListFragment values).cardinality =
        AstCarrierMeasure.patternList values)
    (motive_24 := fun pattern =>
      (patternFragment pattern).cardinality = AstCarrierMeasure.pattern pattern)
    (motive_25 := fun payload =>
      (patternPayloadFragment payload).cardinality =
        AstCarrierMeasure.patternPayload payload)
    (motive_26 := fun patterns =>
      (patternArgumentsFragment patterns).cardinality =
        AstCarrierMeasure.patternArguments patterns)
    (motive_27 := fun values =>
      (expressionNonemptyFragment values).cardinality =
        AstCarrierMeasure.expressionNonempty values)
    (motive_28 := fun values =>
      (expressionListFragment values).cardinality =
        AstCarrierMeasure.expressionList values)
    (motive_29 := fun expressions =>
      (expressionListOptionFragment expressions).cardinality =
        AstCarrierMeasure.expressionListOption expressions) <;>
    simp_all (config := { failIfUnchanged := false }) [
      expressionPayloadFragment, patternPayloadFragment,
      bodyPayloadFragment, letBindingPayloadFragment,
      forInitItemPayloadFragment, forPostItemPayloadFragment,
      matchArmPayloadFragment, statementPayloadFragment,
      expressionFragment, expressionListFragment,
      expressionListOptionFragment, bodyFragment,
      patternArgumentsFragment, patternListFragment, patternFragment,
      statementListFragment, expressionOptionFragment, letBindingFragment,
      patternNonemptyFragment, expressionNonemptyFragment,
      matchArmNonemptyFragment, bodyOptionFragment,
      forInitItemListFragment, forPostItemListFragment,
      statementFragment, matchArmFragment, matchArmListFragment,
      forInitItemFragment, forPostItemFragment,
      expressionPayloadMeasure, patternPayloadMeasure, bodyPayloadMeasure,
      letBindingPayloadMeasure, forInitItemPayloadMeasure,
      forPostItemPayloadMeasure, matchArmPayloadMeasure,
      statementPayloadMeasure, expressionMeasure, expressionListMeasure,
      expressionListOptionMeasure, bodyMeasure, patternArgumentsMeasure,
      patternListMeasure, patternMeasure, statementListMeasure,
      expressionOptionMeasure, letBindingMeasure, patternNonemptyMeasure,
      expressionNonemptyMeasure, matchArmNonemptyMeasure,
      bodyOptionMeasure, forInitItemListMeasure, forPostItemListMeasure,
      statementMeasure, matchArmMeasure, matchArmListMeasure,
      forInitItemMeasure, forPostItemMeasure,
      locatedCarrier, payloadCarrier, append, extend, empty, singleton,
      carrierPair, identifierFragment, markerFragment, unitMarkerFragment,
      prefixOperatorFragment, infixOperatorFragment,
      assignmentOperatorFragment, assemblySliceFragment,
      identifierMeasure, markerMeasure, unitMarkerMeasure,
      prefixOperatorMeasure, infixOperatorMeasure,
      assignmentOperatorMeasure, assemblySliceMeasure,
      qualifiedNameFragment_cardinality, literalFragment_cardinality,
      typeExprFragment_cardinality, parameterFragment_cardinality,
      ofList_cardinality, ofOption_cardinality, ofNonempty_cardinality,
      measureList, measureOption, measureNonemptyList,
      AstCarrierMeasure.option, AstCarrierMeasure.typeExpr,
      AstCarrierMeasure.marker]

set_option linter.unusedSimpArgs false in
private theorem bodyFragment_cardinality (body : Body) :
    (bodyFragment body).cardinality = AstCarrierMeasure.body body := by
  let wrapper : Expression :=
    ⟨body.span, .lambda [] none body⟩
  have counted := expressionFragment_cardinality wrapper
  simp [wrapper, expressionFragment, expressionPayloadFragment,
    expressionMeasure, expressionPayloadMeasure, locatedCarrier,
    payloadCarrier, extend, append, singleton, empty, ofList, ofOption,
    measureList, measureOption, AstCarrierMeasure.body] at counted
  omega


private def classMethodDeclFragment (declaration : ClassMethodDecl) :
    AstCarrierFragment :=
  append (carrierPair .classMethodDecl)
    (functionSignatureFragment declaration.payload.signature)

private def functionDeclFragment (declaration : FunctionDecl) :
    AstCarrierFragment :=
  extend (carrierPair .functionDecl) [
    functionSignatureFragment declaration.payload.signature,
    bodyFragment declaration.payload.body
  ]

private def fallbackDeclFragment (declaration : FallbackDecl) :
    AstCarrierFragment :=
  extend (carrierPair .fallbackDecl) [
    ofOption genericPrefixFragment declaration.payload.genericPrefix,
    ofOption markerFragment declaration.payload.public,
    ofOption markerFragment declaration.payload.payable,
    markerFragment declaration.payload.marker,
    ofList parameterFragment declaration.payload.parameters,
    ofOption typeExprFragment declaration.payload.returnType,
    bodyFragment declaration.payload.body
  ]

private def contractConstructorDeclFragment
    (declaration : ContractConstructorDecl) : AstCarrierFragment :=
  extend (carrierPair .contractConstructorDecl) [
    ofOption markerFragment declaration.payload.public,
    ofOption markerFragment declaration.payload.payable,
    markerFragment declaration.payload.marker,
    ofList parameterFragment declaration.payload.parameters,
    bodyFragment declaration.payload.body
  ]

private def dataConstructorFragment (constructor : DataConstructor) :
    AstCarrierFragment :=
  extend (carrierPair .dataConstructor) [
    identifierFragment constructor.payload.name,
    ofOption (ofNonempty typeExprFragment) constructor.payload.fields
  ]

private def dataDeclFragment (declaration : DataDecl) :
    AstCarrierFragment :=
  extend (carrierPair .dataDecl) [
    identifierFragment declaration.payload.name,
    ofOption (ofNonempty identifierFragment) declaration.payload.parameters,
    ofOption (ofNonempty dataConstructorFragment)
      declaration.payload.constructors
  ]

private def typeAliasDeclFragment (declaration : TypeAliasDecl) :
    AstCarrierFragment :=
  extend (carrierPair .typeAliasDecl) [
    identifierFragment declaration.payload.name,
    ofOption (ofNonempty identifierFragment) declaration.payload.parameters,
    typeExprFragment declaration.payload.body
  ]

private def classDeclFragment (declaration : ClassDecl) :
    AstCarrierFragment :=
  extend (carrierPair .classDecl) [
    ofOption genericPrefixFragment declaration.payload.genericPrefix,
    typeExprFragment declaration.payload.main,
    identifierFragment declaration.payload.className,
    ofOption (ofNonempty typeExprFragment) declaration.payload.parameters,
    ofList classMethodDeclFragment declaration.payload.methods
  ]

private def instanceDeclFragment (declaration : InstanceDecl) :
    AstCarrierFragment :=
  extend (carrierPair .instanceDecl) [
    ofOption genericPrefixFragment declaration.payload.genericPrefix,
    ofOption markerFragment declaration.payload.default,
    typeExprFragment declaration.payload.main,
    qualifiedNameFragment declaration.payload.className,
    ofOption (ofNonempty typeExprFragment) declaration.payload.parameters,
    ofList functionDeclFragment declaration.payload.methods
  ]

private def pragmaDeclFragment (declaration : PragmaDecl) :
    AstCarrierFragment :=
  extend (carrierPair .pragmaDecl) [
    pragmaKindFragment declaration.payload.kind,
    ofList identifierFragment declaration.payload.targets
  ]

private def fieldDeclFragment (declaration : FieldDecl) :
    AstCarrierFragment :=
  extend (carrierPair .fieldDecl) [
    identifierFragment declaration.payload.name,
    typeExprFragment declaration.payload.type,
    ofOption expressionFragment declaration.payload.initializer
  ]

private def contractMemberFragment (member : ContractMember) :
    AstCarrierFragment :=
  let child :=
    match member.payload with
    | .dataDecl declaration => dataDeclFragment declaration
    | .typeAlias declaration => typeAliasDeclFragment declaration
    | .field declaration => fieldDeclFragment declaration
    | .function declaration => functionDeclFragment declaration
    | .fallback declaration => fallbackDeclFragment declaration
    | .constructor declaration =>
        contractConstructorDeclFragment declaration
  append (carrierPair .contractMember) child

private def contractDeclFragment (declaration : ContractDecl) :
    AstCarrierFragment :=
  extend (carrierPair .contractDecl) [
    identifierFragment declaration.payload.name,
    ofOption (ofNonempty identifierFragment) declaration.payload.parameters,
    ofList contractMemberFragment declaration.payload.members
  ]

private def topItemFragment (item : TopItem) : AstCarrierFragment :=
  let child :=
    match item.payload with
    | .importDecl declaration => importDeclFragment declaration
    | .exportDecl declaration => exportModeFragment declaration
    | .pragmaDecl declaration => pragmaDeclFragment declaration
    | .dataDecl declaration => dataDeclFragment declaration
    | .typeAliasDecl declaration => typeAliasDeclFragment declaration
    | .classDecl declaration => classDeclFragment declaration
    | .instanceDecl declaration => instanceDeclFragment declaration
    | .contractDecl declaration => contractDeclFragment declaration
    | .functionDecl declaration => functionDeclFragment declaration
  append (carrierPair .topItem) child

private def parsedModuleFragment (module : ParsedModuleV1) :
    AstCarrierFragment :=
  append (carrierPair .parsedModule)
    (ofList topItemFragment module.payload.items)

private theorem classMethodDeclFragment_cardinality
    (declaration : ClassMethodDecl) :
    (classMethodDeclFragment declaration).cardinality =
      AstCarrierMeasure.classMethodDecl declaration := by
  simp only [classMethodDeclFragment, append, classMethodDeclMeasure]
  rw [functionSignatureFragment_cardinality]
  rfl

private theorem functionDeclFragment_cardinality
    (declaration : FunctionDecl) :
    (functionDeclFragment declaration).cardinality =
      AstCarrierMeasure.functionDecl declaration := by
  simp only [functionDeclFragment, extend, List.foldl, append,
    functionDeclMeasure]
  rw [functionSignatureFragment_cardinality, bodyFragment_cardinality]
  rfl

private theorem fallbackDeclFragment_cardinality
    (declaration : FallbackDecl) :
    (fallbackDeclFragment declaration).cardinality =
      AstCarrierMeasure.fallbackDecl declaration := by
  simp only [fallbackDeclFragment, extend, List.foldl, append,
    fallbackDeclMeasure]
  rw [ofOption_cardinality genericPrefixFragment
    AstCarrierMeasure.genericPrefix genericPrefixFragment_cardinality]
  rw [ofOption_cardinality markerFragment AstCarrierMeasure.marker
    (fun _ => rfl)]
  rw [ofOption_cardinality markerFragment AstCarrierMeasure.marker
    (fun _ => rfl)]
  rw [ofList_cardinality parameterFragment AstCarrierMeasure.parameter
    parameterFragment_cardinality]
  rw [ofOption_cardinality typeExprFragment AstCarrierMeasure.typeExpr
    typeExprFragment_cardinality]
  rw [bodyFragment_cardinality]
  rfl

private theorem contractConstructorDeclFragment_cardinality
    (declaration : ContractConstructorDecl) :
    (contractConstructorDeclFragment declaration).cardinality =
      AstCarrierMeasure.contractConstructorDecl declaration := by
  simp only [contractConstructorDeclFragment, extend, List.foldl, append,
    contractConstructorDeclMeasure]
  rw [ofOption_cardinality markerFragment AstCarrierMeasure.marker
    (fun _ => rfl)]
  rw [ofOption_cardinality markerFragment AstCarrierMeasure.marker
    (fun _ => rfl)]
  rw [ofList_cardinality parameterFragment AstCarrierMeasure.parameter
    parameterFragment_cardinality]
  rw [bodyFragment_cardinality]
  rfl

private theorem dataConstructorFragment_cardinality
    (constructor : DataConstructor) :
    (dataConstructorFragment constructor).cardinality =
      AstCarrierMeasure.dataConstructor constructor := by
  simp only [dataConstructorFragment, extend, List.foldl, append,
    dataConstructorMeasure]
  rw [ofOption_cardinality (ofNonempty typeExprFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.typeExpr)
    (fun values => ofNonempty_cardinality typeExprFragment
      AstCarrierMeasure.typeExpr typeExprFragment_cardinality values)]
  rfl

private theorem dataDeclFragment_cardinality (declaration : DataDecl) :
    (dataDeclFragment declaration).cardinality =
      AstCarrierMeasure.dataDecl declaration := by
  simp only [dataDeclFragment, extend, List.foldl, append, dataDeclMeasure]
  rw [ofOption_cardinality (ofNonempty identifierFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.identifier)
    (fun values => ofNonempty_cardinality identifierFragment
      AstCarrierMeasure.identifier (fun _ => rfl) values)]
  rw [ofOption_cardinality (ofNonempty dataConstructorFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.dataConstructor)
    (fun values => ofNonempty_cardinality dataConstructorFragment
      AstCarrierMeasure.dataConstructor dataConstructorFragment_cardinality
      values)]
  rfl

private theorem typeAliasDeclFragment_cardinality
    (declaration : TypeAliasDecl) :
    (typeAliasDeclFragment declaration).cardinality =
      AstCarrierMeasure.typeAliasDecl declaration := by
  simp only [typeAliasDeclFragment, extend, List.foldl, append,
    typeAliasDeclMeasure]
  rw [ofOption_cardinality (ofNonempty identifierFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.identifier)
    (fun values => ofNonempty_cardinality identifierFragment
      AstCarrierMeasure.identifier (fun _ => rfl) values)]
  rw [typeExprFragment_cardinality]
  rfl

private theorem classDeclFragment_cardinality (declaration : ClassDecl) :
    (classDeclFragment declaration).cardinality =
      AstCarrierMeasure.classDecl declaration := by
  simp only [classDeclFragment, extend, List.foldl, append, classDeclMeasure]
  rw [ofOption_cardinality genericPrefixFragment
    AstCarrierMeasure.genericPrefix genericPrefixFragment_cardinality]
  rw [typeExprFragment_cardinality]
  rw [ofOption_cardinality (ofNonempty typeExprFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.typeExpr)
    (fun values => ofNonempty_cardinality typeExprFragment
      AstCarrierMeasure.typeExpr typeExprFragment_cardinality values)]
  rw [ofList_cardinality classMethodDeclFragment
    AstCarrierMeasure.classMethodDecl classMethodDeclFragment_cardinality]
  rfl

private theorem instanceDeclFragment_cardinality
    (declaration : InstanceDecl) :
    (instanceDeclFragment declaration).cardinality =
      AstCarrierMeasure.instanceDecl declaration := by
  simp only [instanceDeclFragment, extend, List.foldl, append,
    instanceDeclMeasure]
  rw [ofOption_cardinality genericPrefixFragment
    AstCarrierMeasure.genericPrefix genericPrefixFragment_cardinality]
  rw [ofOption_cardinality markerFragment AstCarrierMeasure.marker
    (fun _ => rfl)]
  rw [typeExprFragment_cardinality, qualifiedNameFragment_cardinality]
  rw [ofOption_cardinality (ofNonempty typeExprFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.typeExpr)
    (fun values => ofNonempty_cardinality typeExprFragment
      AstCarrierMeasure.typeExpr typeExprFragment_cardinality values)]
  rw [ofList_cardinality functionDeclFragment AstCarrierMeasure.functionDecl
    functionDeclFragment_cardinality]
  rfl

private theorem pragmaDeclFragment_cardinality (declaration : PragmaDecl) :
    (pragmaDeclFragment declaration).cardinality =
      AstCarrierMeasure.pragmaDecl declaration := by
  simp only [pragmaDeclFragment, extend, List.foldl, append,
    pragmaDeclMeasure]
  rw [ofList_cardinality identifierFragment AstCarrierMeasure.identifier
    (fun _ => rfl)]
  rfl

private theorem fieldDeclFragment_cardinality (declaration : FieldDecl) :
    (fieldDeclFragment declaration).cardinality =
      AstCarrierMeasure.fieldDecl declaration := by
  simp only [fieldDeclFragment, extend, List.foldl, append,
    fieldDeclMeasure]
  rw [typeExprFragment_cardinality]
  rw [ofOption_cardinality expressionFragment AstCarrierMeasure.expression
    expressionFragment_cardinality]
  rfl

private theorem contractMemberFragment_cardinality
    (member : ContractMember) :
    (contractMemberFragment member).cardinality =
      AstCarrierMeasure.contractMember member := by
  cases member with
  | mk span payload =>
      cases payload <;>
        simp only [contractMemberFragment, append, contractMemberMeasure]
      · rw [dataDeclFragment_cardinality]
        rfl
      · rw [typeAliasDeclFragment_cardinality]
        rfl
      · rw [fieldDeclFragment_cardinality]
        rfl
      · rw [functionDeclFragment_cardinality]
        rfl
      · rw [fallbackDeclFragment_cardinality]
        rfl
      · rw [contractConstructorDeclFragment_cardinality]
        rfl

private theorem contractDeclFragment_cardinality
    (declaration : ContractDecl) :
    (contractDeclFragment declaration).cardinality =
      AstCarrierMeasure.contractDecl declaration := by
  simp only [contractDeclFragment, extend, List.foldl, append,
    contractDeclMeasure]
  rw [ofOption_cardinality (ofNonempty identifierFragment)
    (AstCarrierMeasure.nonemptyList AstCarrierMeasure.identifier)
    (fun values => ofNonempty_cardinality identifierFragment
      AstCarrierMeasure.identifier (fun _ => rfl) values)]
  rw [ofList_cardinality contractMemberFragment
    AstCarrierMeasure.contractMember contractMemberFragment_cardinality]
  rfl

private theorem topItemFragment_cardinality (item : TopItem) :
    (topItemFragment item).cardinality = AstCarrierMeasure.topItem item := by
  cases item with
  | mk span payload =>
      cases payload <;> simp only [topItemFragment, append, topItemMeasure]
      · rw [importDeclFragment_cardinality]
        rfl
      · rw [exportModeFragment_cardinality]
        rfl
      · rw [pragmaDeclFragment_cardinality]
        rfl
      · rw [dataDeclFragment_cardinality]
        rfl
      · rw [typeAliasDeclFragment_cardinality]
        rfl
      · rw [classDeclFragment_cardinality]
        rfl
      · rw [instanceDeclFragment_cardinality]
        rfl
      · rw [contractDeclFragment_cardinality]
        rfl
      · rw [functionDeclFragment_cardinality]
        rfl

private theorem parsedModuleFragment_cardinality (module : ParsedModuleV1) :
    (parsedModuleFragment module).cardinality = astNodeMeasure module := by
  simp only [parsedModuleFragment, append, astNodeMeasure]
  rw [ofList_cardinality topItemFragment AstCarrierMeasure.topItem
    topItemFragment_cardinality]
  rfl

end AstCarrierFragment

/-- Enumerate every located-wrapper and payload occurrence in a parsed module,
in parent-before-children and source-list order.  Lists, options, spans, and
other non-carrier data do not add entries. -/
def astCarrierEnumeration (module : ParsedModuleV1) : List AstCarrier :=
  (AstCarrierFragment.parsedModuleFragment module).occurrences

/-- The executable enumeration and the parser's structural node measure count
exactly the same carrier occurrences. -/
theorem astNodeMeasure_eq_astCarrier_cardinality
    (module : ParsedModuleV1) :
    astNodeMeasure module = (astCarrierEnumeration module).length := by
  unfold astCarrierEnumeration
  rw [← (AstCarrierFragment.parsedModuleFragment module).cardinality_eq_length]
  exact (AstCarrierFragment.parsedModuleFragment_cardinality module).symm

/-- Replacing the node measure by the concrete carrier cardinality leaves the
ADR-fixed structural work bound unchanged. -/
theorem structureBound_astCarrier_cardinality
    (module : ParsedModuleV1) :
    structureBound (astCarrierEnumeration module).length =
      structureBound (astNodeMeasure module) := by
  rw [astNodeMeasure_eq_astCarrier_cardinality]

end Solcore.Surface.Multi
