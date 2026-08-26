import Solcore.Surface.Multi.Location

/-! Executable regression fixtures for complete Multi AST location traversal. -/

set_option autoImplicit false

namespace Tests

open Solcore.Workspace
open Solcore.Surface.Multi

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Compare finite bags without depending on traversal order. -/
private def sameBag {alpha : Type} [BEq alpha]
    (left right : List alpha) : Bool :=
  left.length == right.length &&
    left.all (fun value => left.count value == right.count value) &&
    right.all (fun value => left.count value == right.count value)

private def expectSourceId : IO SourceId := do
  match CanonicalSourcePath.parse "Location.solc" with
  | some path => pure { library := .main, path }
  | none => throw (IO.userError "the location-test source path is invalid")

private def expectIdentifier (text : String) : IO Identifier := do
  match Identifier.parse text with
  | some identifier => pure identifier
  | none => throw (IO.userError s!"invalid location-test identifier: {text}")

private def expectPathSegment (text : String) : IO PathSegment := do
  match PathSegment.parse text with
  | some segment => pure segment
  | none => throw (IO.userError s!"invalid location-test path segment: {text}")

private def testSpan
    (source : SourceId) (startByte endByte : Nat) : SourceSpan := {
  source
  startByte
  endByte
}

private def locatedWith {alpha : Type}
    (span : SourceSpan) (payload : alpha) : Located alpha := {
  span
  payload
}

private def nonempty {alpha : Type}
    (head : alpha) (tail : List alpha := []) : NonemptyList alpha := {
  head
  tail
}

private def assertInventory
    (name : String) (actual : LocationInventory)
    (expectedSpans : List SourceSpan)
    (expectedContainments : List (SourceSpan × SourceSpan)) : IO Unit := do
  assertTrue (sameBag actual.spans expectedSpans)
    s!"{name} location spans changed:\n{reprStr actual.spans}"
  assertTrue (sameBag actual.containments expectedContainments)
    s!"{name} location containment edges changed:\n{reprStr actual.containments}"

/--
Exercise unlocated `ImportMode` branches and every retained raw source span.
-/
def testMultiLocationInventory : IO Unit := do
  let source <- expectSourceId
  let sourceName <- expectIdentifier "SourceName"
  let localName <- expectIdentifier "LocalName"
  let hiddenName <- expectIdentifier "HiddenName"
  let moduleAlias <- expectIdentifier "ModuleAlias"
  let functionName <- expectIdentifier "f"
  let valueName <- expectIdentifier "value"
  let className <- expectIdentifier "ClassName"
  let methodName <- expectIdentifier "method"
  let modulePath <- expectPathSegment "Module"
  let file : WorkspaceFile := {
    id := source
    content := String.ofList (List.replicate 512 'x')
  }

  let moduleSpan := testSpan source 0 200
  let itemsTopSpan := testSpan source 1 100
  let itemsDeclSpan := testSpan source 2 99
  let itemsReferenceSpan := testSpan source 3 20
  let itemsPathSpan := testSpan source 4 5
  let selectionSpan := testSpan source 21 70
  let entrySpan := testSpan source 22 40
  let sourceNameSpan := testSpan source 23 24
  let localNameSpan := testSpan source 25 26
  let hidingSpan := testSpan source 41 60
  let hiddenNameSpan := testSpan source 42 43
  let moduleTopSpan := testSpan source 101 199
  let moduleDeclSpan := testSpan source 102 198
  let moduleReferenceSpan := testSpan source 103 120
  let modulePathSpan := testSpan source 104 105
  let moduleAliasSpan := testSpan source 121 122

  let itemsPath : PathComponent :=
    locatedWith itemsPathSpan modulePath
  let itemsReference : ModuleReference :=
    locatedWith itemsReferenceSpan (.relative (nonempty itemsPath))
  let selectorEntry : ImportSelectorEntry :=
    locatedWith entrySpan (.named
      (locatedWith sourceNameSpan sourceName)
      (some (locatedWith localNameSpan localName)))
  let selection : ImportSelection :=
    locatedWith selectionSpan { entries := [selectorEntry] }
  let hidingClause : HidingClause :=
    locatedWith hidingSpan {
      names := [locatedWith hiddenNameSpan hiddenName]
    }
  let itemsDeclaration : ImportDecl :=
    locatedWith itemsDeclSpan {
      moduleRef := itemsReference
      mode := .items selection (some hidingClause)
    }
  let itemsTop : TopItem :=
    locatedWith itemsTopSpan (.importDecl itemsDeclaration)

  let modulePathComponent : PathComponent :=
    locatedWith modulePathSpan modulePath
  let moduleReference : ModuleReference :=
    locatedWith moduleReferenceSpan
      (.relative (nonempty modulePathComponent))
  let moduleDeclaration : ImportDecl :=
    locatedWith moduleDeclSpan {
      moduleRef := moduleReference
      mode := .module (some (locatedWith moduleAliasSpan moduleAlias))
    }
  let moduleTop : TopItem :=
    locatedWith moduleTopSpan (.importDecl moduleDeclaration)
  let importModule : ParsedModuleV1 :=
    locatedWith moduleSpan {
      source
      items := [itemsTop, moduleTop]
    }

  let expectedImportSpans := [
    moduleSpan,
    itemsTopSpan, itemsDeclSpan, itemsReferenceSpan, itemsPathSpan,
    selectionSpan, entrySpan, sourceNameSpan, localNameSpan,
    hidingSpan, hiddenNameSpan,
    moduleTopSpan, moduleDeclSpan, moduleReferenceSpan, modulePathSpan,
    moduleAliasSpan
  ]
  let expectedImportContainments := [
    (moduleSpan, itemsTopSpan),
    (moduleSpan, moduleTopSpan),
    (itemsTopSpan, itemsDeclSpan),
    (itemsDeclSpan, itemsReferenceSpan),
    (itemsDeclSpan, selectionSpan),
    (itemsDeclSpan, hidingSpan),
    (itemsReferenceSpan, itemsPathSpan),
    (selectionSpan, entrySpan),
    (entrySpan, sourceNameSpan),
    (entrySpan, localNameSpan),
    (hidingSpan, hiddenNameSpan),
    (moduleTopSpan, moduleDeclSpan),
    (moduleDeclSpan, moduleReferenceSpan),
    (moduleDeclSpan, moduleAliasSpan),
    (moduleReferenceSpan, modulePathSpan)
  ]
  let importInventory := locationInventory importModule
  assertInventory "import-mode" importInventory
    expectedImportSpans expectedImportContainments
  assertTrue
    (importInventory.spans.all (fun span => span.isValidFor file))
    "the import-mode fixture contains an invalid source span"
  assertTrue
    (importInventory.containments.all
      (fun containment => containment.1.contains containment.2))
    "the import-mode fixture contains a non-nested location edge"
  assertTrue (everyLocationValid file importModule)
    "the complete import-mode location check failed"

  let rawModuleSpan := testSpan source 0 500
  let functionTopSpan := testSpan source 1 299
  let functionDeclSpan := testSpan source 2 298
  let signatureSpan := testSpan source 3 20
  let functionNameSpan := testSpan source 4 5
  let outerBodySpan := testSpan source 21 297
  let outerOpenSpan := testSpan source 21 22
  let outerCloseSpan := testSpan source 296 297
  let expressionStatementSpan := testSpan source 30 50
  let expressionSpan := testSpan source 31 45
  let expressionNameSpan := testSpan source 32 33
  let expressionTerminatorSpan := testSpan source 49 50
  let returnStatementSpan := testSpan source 51 59
  let returnTerminatorSpan := testSpan source 58 59
  let matchStatementSpan := testSpan source 60 160
  let scrutineeSpan := testSpan source 61 70
  let scrutineeNameSpan := testSpan source 62 63
  let matchArmSpan := testSpan source 71 150
  let patternSpan := testSpan source 72 79
  let wildcardSpan := testSpan source 73 74
  let fatArrowSpan := testSpan source 80 82
  let armBodySpan := testSpan source 82 149
  let matchTerminatorSpan := testSpan source 159 160
  let assemblyStatementSpan := testSpan source 161 210
  let assemblySliceSpan := testSpan source 170 200
  let assemblyOpenSpan := testSpan source 170 171
  let assemblyContentsSpan := testSpan source 171 199
  let assemblyCloseSpan := testSpan source 199 200
  let breakStatementSpan := testSpan source 211 220
  let breakTerminatorSpan := testSpan source 219 220
  let continueStatementSpan := testSpan source 221 230
  let continueTerminatorSpan := testSpan source 229 230
  let classTopSpan := testSpan source 300 499
  let classDeclSpan := testSpan source 301 498
  let classMainTypeSpan := testSpan source 302 320
  let classNameSpan := testSpan source 321 322
  let classMethodSpan := testSpan source 330 400
  let methodSignatureSpan := testSpan source 331 390
  let methodNameSpan := testSpan source 332 333
  let classMethodTerminatorSpan := testSpan source 399 400

  let expression : Expression :=
    locatedWith expressionSpan
      (.name (locatedWith expressionNameSpan valueName))
  let expressionStatement : Statement :=
    locatedWith expressionStatementSpan
      (.expression expression (some expressionTerminatorSpan))
  let returnStatement : Statement :=
    locatedWith returnStatementSpan
      (.return none returnTerminatorSpan)
  let scrutinee : Expression :=
    locatedWith scrutineeSpan
      (.name (locatedWith scrutineeNameSpan valueName))
  let pattern : Pattern :=
    locatedWith patternSpan
      (.wildcard (locatedWith wildcardSpan .wildcard))
  let armBody : Body :=
    locatedWith armBodySpan {
      origin := .matchArm fatArrowSpan
      statements := []
    }
  let matchArm : MatchArm :=
    locatedWith matchArmSpan {
      patterns := nonempty pattern
      body := armBody
    }
  let matchStatement : Statement :=
    locatedWith matchStatementSpan
      (.match (nonempty scrutinee) (nonempty matchArm)
        (some matchTerminatorSpan))
  let assemblySlice : AssemblySlice :=
    locatedWith assemblySliceSpan {
      openBrace := assemblyOpenSpan
      contents := assemblyContentsSpan
      closeBrace := assemblyCloseSpan
    }
  let assemblyStatement : Statement :=
    locatedWith assemblyStatementSpan (.assembly assemblySlice)
  let breakStatement : Statement :=
    locatedWith breakStatementSpan (.break breakTerminatorSpan)
  let continueStatement : Statement :=
    locatedWith continueStatementSpan (.continue continueTerminatorSpan)
  let outerBody : Body :=
    locatedWith outerBodySpan {
      origin := .braced outerOpenSpan outerCloseSpan
      statements := [
        expressionStatement,
        returnStatement,
        matchStatement,
        assemblyStatement,
        breakStatement,
        continueStatement
      ]
    }
  let signature : FunctionSignature :=
    locatedWith signatureSpan {
      genericPrefix := none
      «public» := none
      payable := none
      name := locatedWith functionNameSpan functionName
      parameters := []
      returnType := none
    }
  let functionDeclaration : FunctionDecl :=
    locatedWith functionDeclSpan {
      signature
      body := outerBody
    }
  let functionTop : TopItem :=
    locatedWith functionTopSpan (.functionDecl functionDeclaration)

  let methodSignature : FunctionSignature :=
    locatedWith methodSignatureSpan {
      genericPrefix := none
      «public» := none
      payable := none
      name := locatedWith methodNameSpan methodName
      parameters := []
      returnType := none
    }
  let classMethod : ClassMethodDecl :=
    locatedWith classMethodSpan {
      signature := methodSignature
      terminator := classMethodTerminatorSpan
    }
  let classDeclaration : ClassDecl :=
    locatedWith classDeclSpan {
      genericPrefix := none
      main := locatedWith classMainTypeSpan (.tuple [])
      className := locatedWith classNameSpan className
      parameters := none
      methods := [classMethod]
    }
  let classTop : TopItem :=
    locatedWith classTopSpan (.classDecl classDeclaration)
  let rawModule : ParsedModuleV1 :=
    locatedWith rawModuleSpan {
      source
      items := [functionTop, classTop]
    }

  let expectedRawSpans := [
    outerOpenSpan,
    outerCloseSpan,
    expressionTerminatorSpan,
    returnTerminatorSpan,
    fatArrowSpan,
    matchTerminatorSpan,
    assemblyOpenSpan,
    assemblyContentsSpan,
    assemblyCloseSpan,
    breakTerminatorSpan,
    continueTerminatorSpan,
    classMethodTerminatorSpan
  ]
  let expectedSpans := [
    rawModuleSpan,
    functionTopSpan, functionDeclSpan, signatureSpan, functionNameSpan,
    outerBodySpan, outerOpenSpan, outerCloseSpan,
    expressionStatementSpan, expressionSpan, expressionNameSpan,
    expressionTerminatorSpan,
    returnStatementSpan, returnTerminatorSpan,
    matchStatementSpan, scrutineeSpan, scrutineeNameSpan,
    matchArmSpan, patternSpan, wildcardSpan, armBodySpan, fatArrowSpan,
    matchTerminatorSpan,
    assemblyStatementSpan, assemblySliceSpan,
    assemblyOpenSpan, assemblyContentsSpan, assemblyCloseSpan,
    breakStatementSpan, breakTerminatorSpan,
    continueStatementSpan, continueTerminatorSpan,
    classTopSpan, classDeclSpan, classMainTypeSpan, classNameSpan,
    classMethodSpan, methodSignatureSpan, methodNameSpan,
    classMethodTerminatorSpan
  ]
  let expectedRawContainments := [
    (outerBodySpan, outerOpenSpan),
    (outerBodySpan, outerCloseSpan),
    (expressionStatementSpan, expressionTerminatorSpan),
    (returnStatementSpan, returnTerminatorSpan),
    (matchArmSpan, fatArrowSpan),
    (matchStatementSpan, matchTerminatorSpan),
    (assemblySliceSpan, assemblyOpenSpan),
    (assemblySliceSpan, assemblyContentsSpan),
    (assemblySliceSpan, assemblyCloseSpan),
    (breakStatementSpan, breakTerminatorSpan),
    (continueStatementSpan, continueTerminatorSpan),
    (classMethodSpan, classMethodTerminatorSpan)
  ]
  let expectedContainments := [
    (rawModuleSpan, functionTopSpan),
    (rawModuleSpan, classTopSpan),
    (functionTopSpan, functionDeclSpan),
    (functionDeclSpan, signatureSpan),
    (functionDeclSpan, outerBodySpan),
    (signatureSpan, functionNameSpan),
    (outerBodySpan, outerOpenSpan),
    (outerBodySpan, outerCloseSpan),
    (outerBodySpan, expressionStatementSpan),
    (outerBodySpan, returnStatementSpan),
    (outerBodySpan, matchStatementSpan),
    (outerBodySpan, assemblyStatementSpan),
    (outerBodySpan, breakStatementSpan),
    (outerBodySpan, continueStatementSpan),
    (expressionStatementSpan, expressionSpan),
    (expressionStatementSpan, expressionTerminatorSpan),
    (expressionSpan, expressionNameSpan),
    (returnStatementSpan, returnTerminatorSpan),
    (matchStatementSpan, scrutineeSpan),
    (matchStatementSpan, matchArmSpan),
    (matchStatementSpan, matchTerminatorSpan),
    (scrutineeSpan, scrutineeNameSpan),
    (matchArmSpan, patternSpan),
    (matchArmSpan, armBodySpan),
    (matchArmSpan, fatArrowSpan),
    (patternSpan, wildcardSpan),
    (assemblyStatementSpan, assemblySliceSpan),
    (assemblySliceSpan, assemblyOpenSpan),
    (assemblySliceSpan, assemblyContentsSpan),
    (assemblySliceSpan, assemblyCloseSpan),
    (breakStatementSpan, breakTerminatorSpan),
    (continueStatementSpan, continueTerminatorSpan),
    (classTopSpan, classDeclSpan),
    (classDeclSpan, classMainTypeSpan),
    (classDeclSpan, classNameSpan),
    (classDeclSpan, classMethodSpan),
    (classMethodSpan, methodSignatureSpan),
    (classMethodSpan, classMethodTerminatorSpan),
    (methodSignatureSpan, methodNameSpan)
  ]
  let inventory := locationInventory rawModule
  assertInventory "retained-raw-span" inventory
    expectedSpans expectedContainments
  let actualRawSpans := inventory.spans.filter
    (fun span => expectedRawSpans.contains span)
  assertTrue (sameBag actualRawSpans expectedRawSpans)
    "the twelve retained raw source spans changed"
  let actualRawContainments := inventory.containments.filter
    (fun containment => expectedRawSpans.contains containment.2)
  assertTrue (sameBag actualRawContainments expectedRawContainments)
    s!"retained raw-span parents changed:\n{reprStr actualRawContainments}"
  assertTrue (inventory.containments.contains (matchArmSpan, fatArrowSpan))
    "the match arm does not directly contain its fat arrow"
  assertTrue (!inventory.containments.contains (armBodySpan, fatArrowSpan))
    "the match-arm body incorrectly contains the preceding fat arrow"
  assertTrue (inventory.spans.all (fun span => span.isValidFor file))
    "the raw-span fixture contains an invalid source span"
  assertTrue
    (inventory.containments.all
      (fun containment => containment.1.contains containment.2))
    "the raw-span fixture contains a non-nested location edge"
  assertTrue (everyLocationValid file rawModule)
    "the complete retained-raw-span location check failed"

end Tests
