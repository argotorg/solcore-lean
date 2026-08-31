import Solcore.Syntax.Parser

/-! Executable canonical enum, derive, trait, and impl regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def declarationSource : SourceId := {
  origin := .main
  path := "parser-enum-trait-impl.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := declarationSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics [] s!"{label} lexical diagnostics"
      unless output.parsed.items.all (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid item span")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure output

private def qualifiedText (name : QualifiedName) : String :=
  String.intercalate "."
    (name.value.components.toList.map (fun item => item.value))

private def typeName? (type : TypeExpr) : Option String :=
  match type.value with
  | .named name none => some (qualifiedText name)
  | _ => none

private def genericNames (parameters : GenericParameters) : List String :=
  parameters.elements.toList.map (fun name => name.value)

private def parameterNames
    (parameters : DelimitedList FunctionParameter) : List String :=
  parameters.elements.filterMap fun parameter => match parameter.value with
    | .typed _ name _ => some name.value
    | .error => none

private def enumFieldNames
    (fields : Option (DelimitedList TypeExpr)) : Option (List String) :=
  fields.map fun values => values.elements.map fun type =>
    (typeName? type).getD "<non-name>"

private def tailName? (body : Block) : Option String :=
  match body.value with
  | [{ value := .expression expression false, .. }] =>
      match expression.value with
      | .identifier name => some name.value
      | _ => none
  | _ => none

private def testEnumAndDerive : IO Unit := do
  let source :=
    "#[derive(pkg.Eq, Ord)] enum Option<a,> { None, Some(a), Pair(a, word), }"
  let output ← checkedParse "enum and derive" source
  assertEqual output.parseDiagnostics [] "enum diagnostics"
  match output.parsed.items with
  | [{ span := itemSpan, value := .enum declaration, .. }] =>
      assertEqual (byteRange itemSpan) (0, 72) "derived enum item span"
      assertEqual declaration.value.name.value "Option" "enum name"
      assertEqual (declaration.value.parameters.map genericNames)
        (some ["a"]) "enum generic trailing comma"
      assertEqual (declaration.value.parameters.map
        (fun values => byteRange values.span)) (some (34, 38))
        "enum generic span"
      assertEqual (byteRange declaration.value.bodySpan) (39, 72)
        "enum body span"
      match declaration.value.deriveAttribute with
      | some derive =>
          assertEqual (byteRange derive.span) (0, 22) "derive attribute span"
          assertEqual (derive.value.targets.elements.map qualifiedText)
            ["pkg.Eq", "Ord"] "derive target paths"
      | none => throw (IO.userError "enum derive attribute was lost")
      match declaration.value.constructors with
      | [nullaryCtor, unaryCtor, pairCtor] =>
          assertEqual (nullaryCtor.value.name.value,
              enumFieldNames nullaryCtor.value.fields)
            ("None", none) "nullary enum constructor"
          assertEqual (unaryCtor.value.name.value,
              enumFieldNames unaryCtor.value.fields)
            ("Some", some ["a"]) "unary enum constructor"
          assertEqual (pairCtor.value.name.value,
              enumFieldNames pairCtor.value.fields)
            ("Pair", some ["a", "word"]) "product enum constructor"
          assertEqual [byteRange nullaryCtor.span, byteRange unaryCtor.span,
              byteRange pairCtor.span]
            [(41, 45), (47, 54), (56, 69)] "constructor spans"
      | constructors => throw (IO.userError
          s!"enum constructors changed: {reprStr constructors}")
  | items => throw (IO.userError s!"enum item changed: {reprStr items}")

private def testDeriveDiagnostics : IO Unit := do
  let empty ← checkedParse "empty derive" "#[derive()] enum Empty {}"
  match empty.parsed.items, empty.parseDiagnostics with
  | [{ value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .deriveRequiresTarget }] =>
      assertEqual (byteRange span) (0, 11) "empty derive diagnostic span"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements) (some []) "empty derive retained"
  | items, diagnostics => throw (IO.userError
      s!"empty derive changed: {reprStr items}; {reprStr diagnostics}")

  let reserved ← checkedParse "reserved derive target"
    "#[derive(contract)] enum Reserved { Only }"
  match reserved.parsed.items, reserved.parseDiagnostics with
  | [{ value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation
          (.reservedDeriveTarget .contractKw) }] =>
      assertEqual (byteRange span) (9, 17) "reserved target span"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements.map qualifiedText)
        (some ["contract"]) "reserved target source text"
  | items, diagnostics => throw (IO.userError
      s!"reserved derive changed: {reprStr items}; {reprStr diagnostics}")

  let misplaced ← checkedParse "misplaced derive"
    "#[derive(Eq)] type Alias = word;"
  match misplaced.parsed.items, misplaced.parseDiagnostics with
  | [{ span := itemSpan, value := .typeAlias alias, .. }],
      [{ span, kind := .constraintViolation .deriveOnlyEnum }] =>
      assertEqual (byteRange span) (0, 13) "misplaced derive diagnostic span"
      assertEqual (byteRange itemSpan) (0, 32) "misplaced derive item span"
      assertEqual (byteRange alias.span) (0, 32)
        "misplaced derive declaration span"
      assertEqual alias.value.name.value "Alias" "following declaration retained"
  | items, diagnostics => throw (IO.userError
      s!"misplaced derive changed: {reprStr items}; {reprStr diagnostics}")

private def testDeriveRecovery : IO Unit := do
  let malformed ← checkedParse "closed malformed derive"
    "#[derive(Eq,)] enum Closed { One }"
  match malformed.parsed.items, malformed.parseDiagnostics with
  | [{ span := itemSpan, value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .malformedDeriveAttribute }] =>
      assertEqual (byteRange span) (0, 14) "malformed derive span"
      assertEqual (byteRange itemSpan) (0, 34) "malformed enum item span"
      assertEqual declaration.value.name.value "Closed"
        "declaration after malformed derive"
      assertEqual (declaration.value.deriveAttribute.map fun derive =>
        derive.value.targets.elements) (some []) "recovered malformed attribute"
  | items, diagnostics => throw (IO.userError
      s!"malformed derive changed: {reprStr items}; {reprStr diagnostics}")

  let unclosed ← checkedParse "unclosed top-level derive"
    "#[derive(Eq)\nenum Open { One }"
  match unclosed.parsed.items, unclosed.parseDiagnostics with
  | [{ span := itemSpan, value := .enum declaration, .. }],
      [{ span, kind := .constraintViolation .unclosedDeriveAttribute }] =>
      assertEqual (byteRange span) (0, 12) "unclosed derive span"
      assertEqual (byteRange itemSpan) (0, 30) "unclosed enum item span"
      assertEqual declaration.value.name.value "Open"
        "declaration after unclosed derive"
  | items, diagnostics => throw (IO.userError
      s!"unclosed derive changed: {reprStr items}; {reprStr diagnostics}")

  let content := "#[derive(Eq) }"
  let file : SourceFile := { id := declarationSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"derive right-brace lexer invariant: {reprStr error}")
  match Parser.deriveAttribute (Parser.State.initial file lexed) with
  | .ok derive state =>
      assertEqual (byteRange derive.span) (0, 12)
        "right-brace recovered derive span"
      assertEqual state.peekKind? (some (.symbol .rightBrace))
        "right brace remains unconsumed"
      assertEqual (state.diagnostics.map fun diagnostic => diagnostic.kind)
        [.constraintViolation .unclosedDeriveAttribute]
        "right-brace derive diagnostic"
  | .reject failure _ => throw (IO.userError
      s!"right-brace derive rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"right-brace derive invariant: {reprStr error}")

private def testTraitDeclaration : IO Unit := do
  let source :=
    "trait Convert<a, b,> where a: Eq, { function convert(value: a) returns (b,); }"
  let output ← checkedParse "trait declaration" source
  assertEqual output.parseDiagnostics [] "trait diagnostics"
  match output.parsed.items with
  | [{ value := .trait declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 78) "trait span"
      assertEqual declaration.value.name.value "Convert" "trait name"
      assertEqual (genericNames declaration.value.genericParameters)
        ["a", "b"] "trait generic parameters"
      assertEqual (byteRange declaration.value.genericParameters.span)
        (13, 20) "trait generic span"
      assertEqual (declaration.value.whereClause.map fun clause =>
        clause.predicates.toList.length) (some 1) "trait predicate count"
      assertEqual (byteRange declaration.value.bodySpan) (34, 78)
        "trait body span"
      match declaration.value.methods with
      | [method] =>
          assertEqual (byteRange method.span) (36, 76) "trait method span"
          assertEqual method.value.signature.name.value "convert"
            "trait method name"
          assertEqual (parameterNames method.value.signature.parameters)
            ["value"] "trait method parameters"
          assertEqual (method.value.signature.returnsClause.map fun returns =>
            returns.types.elements.map typeName?)
            (some [some "b"]) "trait method return type"
          assertEqual (byteRange method.value.semicolon) (75, 76)
            "trait method semicolon span"
      | methods => throw (IO.userError
          s!"trait methods changed: {reprStr methods}")
  | items => throw (IO.userError s!"trait item changed: {reprStr items}")

private def testImplDeclaration : IO Unit := do
  let source :=
    "default impl<t,> Convert<t, word,> where t: Eq, { function convert(value: t) returns (word) { value } }"
  let output ← checkedParse "impl declaration" source
  assertEqual output.parseDiagnostics [] "impl diagnostics"
  match output.parsed.items with
  | [{ value := .impl declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 103) "impl span"
      assertEqual (declaration.value.defaultMarker.map byteRange)
        (some (0, 7)) "default marker span"
      assertEqual (declaration.value.genericParameters.map genericNames)
        (some ["t"]) "impl generic parameters"
      assertEqual declaration.value.traitName.value "Convert" "impl trait name"
      assertEqual (declaration.value.headArguments.elements.toList.map typeName?)
        [some "t", some "word"] "impl head arguments"
      assertEqual (byteRange declaration.value.headArguments.span) (24, 34)
        "impl head span"
      assertEqual (declaration.value.whereClause.map fun clause =>
        clause.predicates.toList.length) (some 1) "impl predicate count"
      assertEqual (byteRange declaration.value.bodySpan) (48, 103)
        "impl body span"
      match declaration.value.methods with
      | [method] =>
          assertEqual (byteRange method.span) (50, 101) "impl method span"
          assertEqual method.value.declaration.value.signature.name.value
            "convert" "impl method name"
          assertEqual (tailName? method.value.declaration.value.body)
            (some "value") "impl method tail expression"
      | methods => throw (IO.userError
          s!"impl methods changed: {reprStr methods}")
  | items => throw (IO.userError s!"impl item changed: {reprStr items}")

/-- Run canonical enum, derive, trait, and impl parser regressions. -/
def testSyntaxParserEnumTraitImpl : IO Unit := do
  testEnumAndDerive
  testDeriveDiagnostics
  testDeriveRecovery
  testTraitDeclaration
  testImplDeclaration

end Tests
