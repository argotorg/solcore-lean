import Solcore.Surface.Multi.Structure

/-! Executable regression fixtures for Multi structural validation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def expectSourceId : IO SourceId := do
  match CanonicalSourcePath.parse "Structure.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the structural-test source path is invalid")

private def expectSourceIdFor (rawPath : String) : IO SourceId := do
  match CanonicalSourcePath.parse rawPath with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError
      s!"the structural-test source path is invalid: {rawPath}")

private def expectIdentifier (text : String) : IO Identifier := do
  match Identifier.parse text with
  | some identifier => pure identifier
  | none => throw (IO.userError s!"invalid structural-test identifier: {text}")

private def expectPathSegment (text : String) : IO PathSegment := do
  match PathSegment.parse text with
  | some segment => pure segment
  | none => throw (IO.userError s!"invalid structural-test path segment: {text}")

private def fixtureSpan (source : SourceId) (startByte : Nat) : SourceSpan := {
  source
  startByte
  endByte := startByte + 1
}

private def locatedAt {α : Type}
    (source : SourceId) (startByte : Nat) (payload : α) : Located α := {
  span := fixtureSpan source startByte
  payload
}

private def nonempty {α : Type}
    (head : α) (tail : List α := []) : NonemptyList α := {
  head
  tail
}

private def relativeReference
    (source : SourceId) (startByte : Nat)
    (component : PathSegment) : ModuleReference :=
  locatedAt source startByte (.relative (nonempty
    (locatedAt source (startByte + 1) component)))

private def identifierAt
    (source : SourceId) (startByte : Nat)
    (identifier : Identifier) : IdentifierOccurrence :=
  locatedAt source startByte identifier

private def markerAt
    (source : SourceId) (startByte : Nat)
    (marker : SyntaxMarker) : Marker :=
  locatedAt source startByte marker

private def qualifiedNameAt
    (source : SourceId) (startByte : Nat)
    (identifier : Identifier) : QualifiedName :=
  locatedAt source startByte {
    components := nonempty (identifierAt source (startByte + 1) identifier)
  }

private def namedTypeAt
    (source : SourceId) (startByte : Nat)
    (identifier : Identifier) : TypeExpr :=
  locatedAt source startByte
    (.named (qualifiedNameAt source (startByte + 1) identifier) none)

private def parameterAt
    (source : SourceId) (startByte nameByte : Nat)
    (name : Identifier) (parameterType : Option TypeExpr := none) : Parameter :=
  locatedAt source startByte {
    comptime := none
    name := identifierAt source nameByte name
    «type» := parameterType
  }

private def signatureAt
    (source : SourceId) (startByte : Nat)
    (name : Identifier)
    (publicMarker payableMarker : Option Marker)
    (parameters : List Parameter)
    (returnType : Option TypeExpr := none) : FunctionSignature :=
  locatedAt source startByte {
    genericPrefix := none
    «public» := publicMarker
    payable := payableMarker
    name := identifierAt source (startByte + 1) name
    parameters
    returnType
  }

private def bodyAt
    (source : SourceId) (startByte : Nat)
    (statements : List Statement := []) : Body :=
  locatedAt source startByte {
    origin := .braced
      (fixtureSpan source startByte)
      (fixtureSpan source (startByte + 1))
    statements
  }

private def nameExpressionAt
    (source : SourceId) (startByte : Nat)
    (name : Identifier) : Expression :=
  locatedAt source startByte
    (.name (identifierAt source startByte name))

private def functionAt
    (source : SourceId) (startByte : Nat)
    (signature : FunctionSignature) (body : Body) : FunctionDecl :=
  locatedAt source startByte { signature, body }

private def functionItemAt
    (source : SourceId) (startByte : Nat)
    (declaration : FunctionDecl) : TopItem :=
  locatedAt source startByte (.functionDecl declaration)

private def moduleAt
    (source : SourceId) (items : List TopItem) : ParsedModuleV1 :=
  locatedAt source 0 { source, items }

/-- Exercise every MSS constructor and the canonical structural-validation API. -/
def testMultiStructuralValidation : IO Unit := do
  let source ← expectSourceId
  let alpha ← expectIdentifier "Alpha"
  let beta ← expectIdentifier "Beta"
  let gamma ← expectIdentifier "Gamma"
  let exported ← expectIdentifier "Exported"
  let constructorName ← expectIdentifier "ConstructorName"
  let functionName ← expectIdentifier "f"
  let className ← expectIdentifier "ClassName"
  let contractName ← expectIdentifier "ContractName"
  let valueName ← expectIdentifier "value"
  let moduleComponent ← expectPathSegment "Module"

  let moduleReference := relativeReference source 2 moduleComponent

  let emptySelection : ImportSelection :=
    locatedAt source 10 { entries := [] }
  let emptyHiding : HidingClause :=
    locatedAt source 11 { names := [] }
  let emptyImport : ImportDecl := locatedAt source 9 {
    moduleRef := moduleReference
    mode := .items emptySelection (some emptyHiding)
  }
  let emptyImportItem : TopItem :=
    locatedAt source 9 (.importDecl emptyImport)

  let importWildcard : ImportSelectorEntry :=
    locatedAt source 20 (.wildcard (markerAt source 20 .wildcard))
  let firstImportName : ImportSelectorEntry :=
    locatedAt source 21 (.named
      (identifierAt source 21 alpha)
      (some (identifierAt source 22 beta)))
  let secondImportName : ImportSelectorEntry :=
    locatedAt source 23 (.named
      (identifierAt source 23 alpha)
      (some (identifierAt source 24 beta)))
  let duplicateHiding : HidingClause := locatedAt source 25 {
    names := [
      identifierAt source 25 gamma,
      identifierAt source 26 gamma
    ]
  }
  let badImportSelection : ImportSelection := locatedAt source 19 {
    entries := [importWildcard, firstImportName, secondImportName]
  }
  let badImport : ImportDecl := locatedAt source 18 {
    moduleRef := moduleReference
    mode := .items badImportSelection (some duplicateHiding)
  }
  let badImportItem : TopItem := locatedAt source 18 (.importDecl badImport)

  let emptyLocalSelection : LocalExportList :=
    locatedAt source 30 { entries := [] }
  let emptyLocalExport : ExportDecl :=
    locatedAt source 29 (.local emptyLocalSelection)
  let emptyLocalExportItem : TopItem :=
    locatedAt source 29 (.exportDecl emptyLocalExport)

  let emptyRemoteSelection : RemoteExportSelection :=
    locatedAt source 32 (.braced [])
  let emptyRemoteExport : ExportDecl :=
    locatedAt source 31 (.from moduleReference emptyRemoteSelection)
  let emptyRemoteExportItem : TopItem :=
    locatedAt source 31 (.exportDecl emptyRemoteExport)

  let exportWildcard : ExportEntry :=
    locatedAt source 40 (.wildcard (markerAt source 40 .wildcard))
  let firstExportItem : ExportItem := locatedAt source 41 {
    name := identifierAt source 41 exported
    constructors := none
  }
  let duplicateConstructors : ConstructorSelection :=
    locatedAt source 45 (.named (nonempty
      (identifierAt source 45 constructorName)
      [identifierAt source 46 constructorName]))
  let secondExportItem : ExportItem := locatedAt source 44 {
    name := identifierAt source 44 exported
    constructors := some duplicateConstructors
  }
  let firstExportEntry : ExportEntry :=
    locatedAt source 41 (.item firstExportItem)
  let secondExportEntry : ExportEntry :=
    locatedAt source 44 (.item secondExportItem)
  let firstAllFromReference := relativeReference source 47 moduleComponent
  let secondAllFromReference := relativeReference source 50 moduleComponent
  let firstAllFrom : ExportEntry := locatedAt source 47
    (.allFrom firstAllFromReference (markerAt source 49 .wildcard))
  let secondAllFrom : ExportEntry := locatedAt source 50
    (.allFrom secondAllFromReference (markerAt source 52 .wildcard))
  let badLocalSelection : LocalExportList := locatedAt source 39 {
    entries := [
      exportWildcard,
      firstExportEntry,
      secondExportEntry,
      firstAllFrom,
      secondAllFrom
    ]
  }
  let badLocalExport : ExportDecl :=
    locatedAt source 38 (.local badLocalSelection)
  let badLocalExportItem : TopItem :=
    locatedAt source 38 (.exportDecl badLocalExport)

  let firstScrutinee := nameExpressionAt source 56 valueName
  let secondScrutinee := nameExpressionAt source 57 valueName
  let solePattern : Pattern :=
    locatedAt source 58 (.wildcard (markerAt source 58 .wildcard))
  let matchArm : MatchArm := locatedAt source 60 {
    patterns := nonempty solePattern
    body := bodyAt source 59
  }
  let mismatchStatement : Statement := locatedAt source 59
    (.match
      (nonempty firstScrutinee [secondScrutinee])
      (nonempty matchArm)
      none)
  let outsideBreak : Statement :=
    locatedAt source 61 (.break (fixtureSpan source 61))
  let outsideContinue : Statement :=
    locatedAt source 62 (.continue (fixtureSpan source 62))
  let insideBreak : Statement :=
    locatedAt source 64 (.break (fixtureSpan source 64))
  let insideContinue : Statement :=
    locatedAt source 65 (.continue (fixtureSpan source 65))
  let lambdaBreak : Statement :=
    locatedAt source 68 (.break (fixtureSpan source 68))
  let lambdaBody := bodyAt source 67 [lambdaBreak]
  let lambdaExpression : Expression :=
    locatedAt source 67 (.lambda [] none lambdaBody)
  let lambdaStatement : Statement :=
    locatedAt source 67 (.expression lambdaExpression none)
  let loopBody := bodyAt source 63 [insideBreak, insideContinue, lambdaStatement]
  let loopStatement : Statement := locatedAt source 63
    (.forLoop [] (nameExpressionAt source 63 valueName) [] loopBody)
  let controlBody := bodyAt source 55 [
    mismatchStatement,
    outsideBreak,
    outsideContinue,
    loopStatement
  ]
  let controlSignature :=
    signatureAt source 54 functionName none none []
  let controlFunction :=
    functionAt source 54 controlSignature controlBody
  let controlItem := functionItemAt source 54 controlFunction

  let emptyGenericPragma : PragmaDecl := locatedAt source 71 {
    kind := locatedAt source 72 .noGenericInstanceFor
    targets := []
  }
  let emptyGenericPragmaItem : TopItem :=
    locatedAt source 71 (.pragmaDecl emptyGenericPragma)
  let duplicatePragma : PragmaDecl := locatedAt source 74 {
    kind := locatedAt source 74 .noCoverageCondition
    targets := [
      identifierAt source 75 alpha,
      identifierAt source 76 alpha
    ]
  }
  let duplicatePragmaItem : TopItem :=
    locatedAt source 74 (.pragmaDecl duplicatePragma)

  let topParameter := parameterAt source 83 84 valueName
  let topSignature := signatureAt source 80 functionName
    (some (markerAt source 81 .publicModifier))
    (some (markerAt source 82 .payableModifier))
    [topParameter]
  let topFunction := functionAt source 80 topSignature (bodyAt source 85)
  let topFunctionItem := functionItemAt source 80 topFunction

  let classParameter := parameterAt source 93 94 valueName
  let classSignature := signatureAt source 90 functionName
    (some (markerAt source 91 .publicModifier)) none [classParameter]
  let classMethod : ClassMethodDecl := locatedAt source 90 {
    signature := classSignature
    terminator := fixtureSpan source 95
  }
  let classDeclaration : ClassDecl := locatedAt source 89 {
    genericPrefix := none
    main := namedTypeAt source 89 valueName
    className := identifierAt source 89 className
    parameters := none
    methods := [classMethod]
  }
  let classItem : TopItem :=
    locatedAt source 89 (.classDecl classDeclaration)

  let instanceParameter := parameterAt source 103 104 valueName
  let instanceSignature := signatureAt source 100 functionName
    (some (markerAt source 101 .publicModifier)) none [instanceParameter]
  let instanceMethod :=
    functionAt source 100 instanceSignature (bodyAt source 105)
  let instanceDeclaration : InstanceDecl := locatedAt source 99 {
    genericPrefix := none
    default := none
    main := namedTypeAt source 99 valueName
    className := qualifiedNameAt source 99 className
    parameters := none
    methods := [instanceMethod]
  }
  let instanceItem : TopItem :=
    locatedAt source 99 (.instanceDecl instanceDeclaration)

  let contractFunctionParameter := parameterAt source 107 108 valueName
  let contractFunctionSignature := signatureAt source 106 functionName
    none none [contractFunctionParameter]
  let contractFunction := functionAt source 106 contractFunctionSignature
    (bodyAt source 109)
  let contractFunctionMember : ContractMember :=
    locatedAt source 106 (.function contractFunction)

  let fallbackParameters := [
    parameterAt source 113 114 valueName,
    parameterAt source 115 116 valueName
  ]
  let fallbackReturnType := namedTypeAt source 112 valueName
  let fallbackDeclaration : FallbackDecl := locatedAt source 110 {
    genericPrefix := none
    «public» := some (markerAt source 110 .publicModifier)
    payable := none
    marker := markerAt source 111 .fallbackName
    parameters := fallbackParameters
    returnType := some fallbackReturnType
    body := bodyAt source 117
  }
  let fallbackMember : ContractMember :=
    locatedAt source 110 (.fallback fallbackDeclaration)

  let constructorParameter := parameterAt source 122 123 valueName
  let constructorDeclaration : ContractConstructorDecl :=
    locatedAt source 120 {
      «public» := some (markerAt source 120 .publicModifier)
      payable := none
      marker := markerAt source 121 .contractConstructorName
      parameters := [constructorParameter]
      body := bodyAt source 124
    }
  let constructorMember : ContractMember :=
    locatedAt source 120 (.constructor constructorDeclaration)
  let contractDeclaration : ContractDecl := locatedAt source 106 {
    name := identifierAt source 106 contractName
    parameters := none
    members := [contractFunctionMember, fallbackMember, constructorMember]
  }
  let contractItem : TopItem :=
    locatedAt source 106 (.contractDecl contractDeclaration)

  let fixtureModule := moduleAt source [
    emptyImportItem,
    badImportItem,
    emptyLocalExportItem,
    emptyRemoteExportItem,
    badLocalExportItem,
    controlItem,
    emptyGenericPragmaItem,
    duplicatePragmaItem,
    topFunctionItem,
    classItem,
    instanceItem,
    contractItem
  ]

  let d01 : StructuralDiagnostic :=
    .emptyImportSelection (fixtureSpan source 10)
  let d02 : StructuralDiagnostic :=
    .mixedImportWildcard (fixtureSpan source 20)
  let d03 : StructuralDiagnostic :=
    .duplicateImportSourceName (fixtureSpan source 23) alpha
  let d04 : StructuralDiagnostic :=
    .duplicateImportLocalName (fixtureSpan source 24) beta
  let d05 : StructuralDiagnostic :=
    .emptyHidingClause (fixtureSpan source 11)
  let d06 : StructuralDiagnostic :=
    .duplicateHiddenName (fixtureSpan source 26) gamma
  let d07 : StructuralDiagnostic :=
    .emptyLocalExportList (fixtureSpan source 30)
  let d08 : StructuralDiagnostic :=
    .emptyRemoteExportList (fixtureSpan source 32)
  let d09 : StructuralDiagnostic :=
    .mixedExportWildcard (fixtureSpan source 40)
  let d10 : StructuralDiagnostic :=
    .duplicateExportName (fixtureSpan source 44) exported
  let duplicateReferenceShape : ModuleReferenceShape :=
    .relative (nonempty moduleComponent)
  let d11 : StructuralDiagnostic :=
    .duplicateExportModuleReference
      (fixtureSpan source 50) duplicateReferenceShape
  let d12 : StructuralDiagnostic :=
    .duplicateExportConstructor (fixtureSpan source 46) constructorName
  let d13 : StructuralDiagnostic :=
    .matchPatternArityMismatch (fixtureSpan source 60) 2 1
  let d14 : StructuralDiagnostic :=
    .emptyGenericPragmaTargets (fixtureSpan source 72)
  let d15 : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 76) alpha
  let d16TopPublic : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 81)
      .topLevelFunction .publicModifier
  let d16TopPayable : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 82)
      .topLevelFunction .payableModifier
  let d16Class : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 91)
      .classMethod .publicModifier
  let d16Instance : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 101)
      .instanceMethod .publicModifier
  let d16Fallback : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 110)
      .fallback .publicModifier
  let d16Constructor : StructuralDiagnostic :=
    .modifierNotAllowed (fixtureSpan source 120)
      .contractConstructor .publicModifier
  let d17 : StructuralDiagnostic :=
    .fallbackHasParameters (fixtureSpan source 111) 2
  let d18 : StructuralDiagnostic :=
    .fallbackHasNonUnitReturn (fixtureSpan source 112)
  let d19Top : StructuralDiagnostic :=
    .requiredParameterTypeMissing (fixtureSpan source 84) .topLevelFunction
  let d19Class : StructuralDiagnostic :=
    .requiredParameterTypeMissing (fixtureSpan source 94) .classMethod
  let d19Instance : StructuralDiagnostic :=
    .requiredParameterTypeMissing (fixtureSpan source 104) .instanceMethod
  let d19Contract : StructuralDiagnostic :=
    .requiredParameterTypeMissing (fixtureSpan source 108) .contractFunction
  let d19Constructor : StructuralDiagnostic :=
    .requiredParameterTypeMissing
      (fixtureSpan source 123) .contractConstructor
  let d20Break : StructuralDiagnostic :=
    .controlOutsideLoop (fixtureSpan source 61) .breakControl
  let d20Continue : StructuralDiagnostic :=
    .controlOutsideLoop (fixtureSpan source 62) .continueControl
  let d20LambdaBreak : StructuralDiagnostic :=
    .controlOutsideLoop (fixtureSpan source 68) .breakControl

  let expectedCandidates : List StructuralDiagnostic := [
    d01, d05,
    d02, d03, d04, d06,
    d07,
    d08,
    d09, d10, d11, d12,
    d13, d20Break, d20Continue, d20LambdaBreak,
    d14,
    d15,
    d16TopPublic, d16TopPayable, d19Top,
    d16Class, d19Class,
    d16Instance, d19Instance,
    d19Contract,
    d16Fallback, d17, d18,
    d16Constructor, d19Constructor
  ]
  let actualCandidates := Structure.diagnosticCandidates fixtureModule
  assertTrue (actualCandidates == expectedCandidates)
    s!"structural diagnostic candidates changed:\n{reprStr actualCandidates}"

  let expectedCanonical : List StructuralDiagnostic := [
    d01, d02, d03, d04, d05, d06, d07, d08, d09, d10,
    d11, d12, d13, d14, d15,
    d16TopPublic, d16TopPayable, d16Class, d16Instance,
    d16Fallback, d16Constructor,
    d17, d18,
    d19Top, d19Class, d19Instance, d19Contract, d19Constructor,
    d20Break, d20Continue, d20LambdaBreak
  ]
  let actualCanonical := Structure.diagnostics fixtureModule
  assertTrue (actualCanonical == expectedCanonical)
    s!"canonical structural diagnostics changed:\n{reprStr actualCanonical}"
  assertTrue
    (actualCanonical.map StructuralDiagnostic.code == [
      "MSS0001", "MSS0002", "MSS0003", "MSS0004", "MSS0005",
      "MSS0006", "MSS0007", "MSS0008", "MSS0009", "MSS0010",
      "MSS0011", "MSS0012", "MSS0013", "MSS0014", "MSS0015",
      "MSS0016", "MSS0016", "MSS0016", "MSS0016", "MSS0016",
      "MSS0016", "MSS0017", "MSS0018", "MSS0019", "MSS0019",
      "MSS0019", "MSS0019", "MSS0019", "MSS0020", "MSS0020",
      "MSS0020"
    ])
    "structural diagnostics are not in canonical MSS-code order"
  match validateStructure fixtureModule with
  | .ok _ =>
      throw (IO.userError "structural validation accepted an invalid fixture")
  | .error emitted =>
      assertTrue (emitted.head :: emitted.tail == expectedCanonical)
        "validateStructure did not return the complete canonical diagnostic list"

  let typedParameter := parameterAt source 201 202 valueName
    (some (namedTypeAt source 203 valueName))
  let cleanLoopBody := bodyAt source 207 [
    locatedAt source 208 (.break (fixtureSpan source 208)),
    locatedAt source 209 (.continue (fixtureSpan source 209))
  ]
  let cleanLoop : Statement := locatedAt source 206
    (.forLoop [] (nameExpressionAt source 206 valueName) [] cleanLoopBody)
  let cleanSignature := signatureAt source 200 functionName
    none none [typedParameter]
  let cleanFunction := functionAt source 200 cleanSignature
    (bodyAt source 205 [cleanLoop])
  let unitType : TypeExpr :=
    locatedAt source 213 (.group (locatedAt source 214 (.tuple [])))
  let cleanFallback : FallbackDecl := locatedAt source 210 {
    genericPrefix := none
    «public» := none
    payable := some (markerAt source 211 .payableModifier)
    marker := markerAt source 212 .fallbackName
    parameters := []
    returnType := some unitType
    body := bodyAt source 215
  }
  let cleanContract : ContractDecl := locatedAt source 210 {
    name := identifierAt source 210 contractName
    parameters := none
    members := [locatedAt source 210 (.fallback cleanFallback)]
  }
  let cleanModule := moduleAt source [
    functionItemAt source 200 cleanFunction,
    locatedAt source 210 (.contractDecl cleanContract)
  ]
  assertTrue (Structure.diagnosticCandidates cleanModule == [])
    "valid loop controls or grouped-unit fallback produced a candidate"
  assertTrue (Structure.diagnostics cleanModule == [])
    "valid structural fixture produced a canonical diagnostic"
  match validateStructure cleanModule with
  | .ok _ => pure ()
  | .error emitted =>
      throw (IO.userError
        s!"structural validation rejected a valid fixture: {reprStr emitted}")

  let remoteWildcard : RemoteExportEntry :=
    locatedAt source 300 (.wildcard (markerAt source 300 .wildcard))
  let remoteConstructors : ConstructorSelection :=
    locatedAt source 302 (.named (nonempty
      (identifierAt source 302 constructorName)
      [identifierAt source 303 constructorName]))
  let firstRemoteItem : ExportItem := locatedAt source 301 {
    name := identifierAt source 301 exported
    constructors := some remoteConstructors
  }
  let secondRemoteItem : ExportItem := locatedAt source 304 {
    name := identifierAt source 304 exported
    constructors := none
  }
  let remoteSelection : RemoteExportSelection := locatedAt source 299
    (.braced [
      remoteWildcard,
      locatedAt source 301 (.item firstRemoteItem),
      locatedAt source 304 (.item secondRemoteItem)
    ])
  let remoteDeclaration : ExportDecl :=
    locatedAt source 298 (.from moduleReference remoteSelection)
  let remoteMixed : StructuralDiagnostic :=
    .mixedExportWildcard (fixtureSpan source 300)
  let remoteDuplicateName : StructuralDiagnostic :=
    .duplicateExportName (fixtureSpan source 304) exported
  let remoteDuplicateConstructor : StructuralDiagnostic :=
    .duplicateExportConstructor (fixtureSpan source 303) constructorName
  assertTrue
    (Structure.exportDiagnostics remoteDeclaration == [
      remoteMixed,
      remoteDuplicateName,
      remoteDuplicateConstructor
    ])
    "braced remote export diagnostics changed"

  let triplePragma : PragmaDecl := locatedAt source 320 {
    kind := locatedAt source 320 .noCoverageCondition
    targets := [
      identifierAt source 321 alpha,
      identifierAt source 322 alpha,
      identifierAt source 323 alpha
    ]
  }
  let triplePragmaModule := moduleAt source [
    locatedAt source 320 (.pragmaDecl triplePragma)
  ]
  let tripleSecond : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 322) alpha
  let tripleThird : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 323) alpha
  assertTrue
    (Structure.diagnosticCandidates triplePragmaModule ==
      [tripleSecond, tripleThird])
    "a third equal pragma target did not produce a second diagnostic"

  let laterWildcard : ImportSelectorEntry :=
    locatedAt source 350 (.wildcard (markerAt source 350 .wildcard))
  let soleNamedImport : ImportSelectorEntry :=
    locatedAt source 345 (.named (identifierAt source 345 alpha) none)
  let earlierWildcard : ImportSelectorEntry :=
    locatedAt source 340 (.wildcard (markerAt source 340 .wildcard))
  let leastWildcardSelection : ImportSelection := locatedAt source 339 {
    entries := [laterWildcard, soleNamedImport, earlierWildcard]
  }
  let leastWildcardImport : ImportDecl := locatedAt source 338 {
    moduleRef := moduleReference
    mode := .items leastWildcardSelection none
  }
  assertTrue
    (Structure.importDiagnostics leastWildcardImport == [
      .mixedImportWildcard (fixtureSpan source 340)
    ])
    "mixed import wildcard did not select the least marker span"

  let repeatedPragma : PragmaDecl := locatedAt source 360 {
    kind := locatedAt source 360 .noPattersonCondition
    targets := [
      identifierAt source 361 beta,
      identifierAt source 362 beta
    ]
  }
  let repeatedPragmaItem : TopItem :=
    locatedAt source 360 (.pragmaDecl repeatedPragma)
  let exactDuplicateModule := moduleAt source [
    repeatedPragmaItem,
    repeatedPragmaItem
  ]
  let repeatedDiagnostic : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 362) beta
  assertTrue
    (Structure.diagnosticCandidates exactDuplicateModule ==
      [repeatedDiagnostic, repeatedDiagnostic])
    "the exact-duplicate fixture did not create two candidates"
  assertTrue
    (Structure.diagnostics exactDuplicateModule == [repeatedDiagnostic])
    "canonical structural diagnostics did not remove an exact duplicate"

  let laterSource ← expectSourceIdFor "Ztructure.solc"
  let sourceFirst : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 390) alpha
  let sourceSecond : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan laterSource 1) alpha
  assertTrue
    (StructuralDiagnostic.compare sourceFirst sourceSecond == .lt)
    "structural diagnostic comparison did not prioritize source identity"

  let startFirst : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 400) alpha
  let startSecond : StructuralDiagnostic :=
    .duplicatePragmaTarget (fixtureSpan source 401) alpha
  assertTrue
    (StructuralDiagnostic.compare startFirst startSecond == .lt)
    "structural diagnostic comparison did not prioritize the start byte"

  let shortSpan : SourceSpan := {
    source
    startByte := 410
    endByte := 411
  }
  let longSpan : SourceSpan := {
    source
    startByte := 410
    endByte := 412
  }
  let endFirst : StructuralDiagnostic :=
    .duplicatePragmaTarget shortSpan alpha
  let endSecond : StructuralDiagnostic :=
    .duplicatePragmaTarget longSpan alpha
  assertTrue
    (StructuralDiagnostic.compare endFirst endSecond == .lt)
    "structural diagnostic comparison did not prioritize the end byte"

  let payloadSpan := fixtureSpan source 420
  let payloadFirst : StructuralDiagnostic :=
    .duplicatePragmaTarget payloadSpan alpha
  let payloadSecond : StructuralDiagnostic :=
    .duplicatePragmaTarget payloadSpan beta
  assertTrue
    (StructuralDiagnostic.compare payloadFirst payloadSecond == .lt)
    "structural diagnostic comparison did not use the remaining payload"

  let allowedContractParameter := parameterAt source 432 433 valueName
    (some (namedTypeAt source 434 valueName))
  let allowedContractSignature := signatureAt source 430 functionName
    (some (markerAt source 430 .publicModifier))
    (some (markerAt source 431 .payableModifier))
    [allowedContractParameter]
  let allowedContractFunction := functionAt source 430
    allowedContractSignature (bodyAt source 435)
  let untypedLambdaParameter := parameterAt source 442 443 valueName
  let allowedLambda : Expression := locatedAt source 441
    (.lambda [untypedLambdaParameter] none (bodyAt source 444))
  let allowedLambdaStatement : Statement :=
    locatedAt source 441 (.expression allowedLambda none)
  let allowedLambdaSignature := signatureAt source 440 functionName none none []
  let allowedLambdaFunction := functionAt source 440 allowedLambdaSignature
    (bodyAt source 440 [allowedLambdaStatement])
  let nestedUnitType : TypeExpr := locatedAt source 451
    (.group (locatedAt source 452
      (.group (locatedAt source 453 (.tuple [])))))
  let nestedUnitFallback : FallbackDecl := locatedAt source 450 {
    genericPrefix := none
    «public» := none
    payable := none
    marker := markerAt source 450 .fallbackName
    parameters := []
    returnType := some nestedUnitType
    body := bodyAt source 454
  }
  let allowedContract : ContractDecl := locatedAt source 429 {
    name := identifierAt source 429 contractName
    parameters := none
    members := [
      locatedAt source 430 (.function allowedContractFunction),
      locatedAt source 450 (.fallback nestedUnitFallback)
    ]
  }
  let allowedModule := moduleAt source [
    functionItemAt source 440 allowedLambdaFunction,
    locatedAt source 429 (.contractDecl allowedContract)
  ]
  assertTrue (Structure.diagnosticCandidates allowedModule == [])
    "allowed modifiers, lambda parameters, or grouped unit were rejected"

  let deeplyGroupedUnitType : TypeExpr := locatedAt source 460
    (.group (locatedAt source 461
      (.group (locatedAt source 462
        (.group (locatedAt source 463
          (.group (locatedAt source 464
            (.group (locatedAt source 465 (.tuple [])))))))))))
  let zeroFuelUnitFallback : FallbackDecl := locatedAt source 459 {
    genericPrefix := none
    «public» := none
    payable := none
    marker := markerAt source 459 .fallbackName
    parameters := []
    returnType := some deeplyGroupedUnitType
    body := bodyAt source 466
  }
  let zeroFuelUnitDiagnostics :=
    Structure.fallbackDiagnostics 0 zeroFuelUnitFallback
  assertTrue (zeroFuelUnitDiagnostics == [])
    "deeply grouped unit return emitted a zero-fuel fallback diagnostic"

  let zeroFuelNonUnitType := namedTypeAt source 470 valueName
  let zeroFuelNonUnitFallback : FallbackDecl := locatedAt source 469 {
    genericPrefix := none
    «public» := none
    payable := none
    marker := markerAt source 469 .fallbackName
    parameters := []
    returnType := some zeroFuelNonUnitType
    body := bodyAt source 471
  }
  let zeroFuelNonUnitDiagnostics :=
    Structure.fallbackDiagnostics 0 zeroFuelNonUnitFallback
  assertTrue
    (zeroFuelNonUnitDiagnostics == [
      .fallbackHasNonUnitReturn (fixtureSpan source 470)
    ])
    "non-unit return did not emit the zero-fuel fallback diagnostic"
  assertTrue
    (zeroFuelNonUnitDiagnostics.map StructuralDiagnostic.code == ["MSS0018"])
    "zero-fuel non-unit fallback did not report MSS0018"

end Tests
