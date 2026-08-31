import Solcore.Syntax.Parser

/-! Executable canonical contract declaration and entry-point regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def contractSource : SourceId := {
  origin := .main
  path := "parser-contracts.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := contractSource, content }
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

private def tailName? (body : Block) : Option String :=
  match body.value with
  | [{ value := .expression expression false, .. }] =>
      match expression.value with
      | .identifier name => some name.value
      | _ => none
  | _ => none

private def testDeriveContractFieldBoundary : IO Unit := do
  let output ← checkedParse "derive contract-field boundary"
    "contract C { #[derive(Eq)\nvalue: word; }"
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((13, 25), .constraintViolation .unclosedDeriveAttribute),
      ((13, 25), .constraintViolation .deriveOnlyEnum)
    ] "contract-field boundary diagnostics"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      match declaration.value.members with
      | [{ span := memberSpan, value := .field field, .. }] =>
          assertEqual (byteRange memberSpan) (13, 38)
            "derived field member span"
          assertEqual (byteRange field.span) (13, 38)
            "derived field declaration span"
          assertEqual field.value.name.value "value"
            "field after unclosed derive"
      | members => throw (IO.userError
          s!"derive field boundary changed: {reprStr members}")
  | items => throw (IO.userError
      s!"derive field contract changed: {reprStr items}")

private def testMalformedFieldRecovery : IO Unit := do
  let output ← checkedParse "malformed contract field"
    "contract C { broken: ; function good() {} } function after() {}"
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((13, 22), .recovered .contractMember)
    ] "malformed field diagnostics"
  match output.parsed.items with
  | [
      { span := contractSpan, value := .contract declaration, .. },
      { span := afterSpan, value := .function after, .. }
    ] =>
      assertEqual (byteRange contractSpan) (0, 43)
        "recovered contract span"
      assertEqual (byteRange afterSpan) (44, 63)
        "top item after recovered contract"
      assertEqual after.value.signature.name.value "after"
        "function after recovered contract"
      match declaration.value.members with
      | [errorMember, goodMember] =>
          assertEqual (byteRange errorMember.span) (13, 22)
            "malformed field recovery span"
          assertEqual errorMember.value .error
            "malformed field recovery node"
          match goodMember.value with
          | .function good =>
              assertEqual good.value.signature.name.value "good"
                "member after malformed field"
          | value => throw (IO.userError
              s!"member after malformed field changed: {reprStr value}")
      | members => throw (IO.userError
          s!"malformed field members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"malformed field items changed: {reprStr items}")

private def testContractDeclaration : IO Unit := do
  let source := String.intercalate "\n" [
    "contract Vault<t,> {",
    "  balance: word = 0;",
    "  function get() public returns (word) { balance }",
    "  constructor(seed: word,) public payable { balance = seed; }",
    "  fallback(arg: word) public payable { return; }",
    "  type Local = word;",
    "  #[derive(Eq)] enum Flag { Off, On(word), }",
    "}"
  ]
  let output ← checkedParse "contract declaration" source
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
    (byteRange diagnostic.span, diagnostic.kind)) [
      ((120, 126), .constraintViolation
        (.implicitPublicModifier .constructorKw)),
      ((165, 176), .constraintViolation .fallbackRequiresNoParameters),
      ((177, 183), .constraintViolation
        (.implicitPublicModifier .fallbackKw))
    ] "contract entry diagnostics"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      assertEqual (byteRange declaration.span) (0, 271) "contract span"
      assertEqual declaration.value.name.value "Vault" "contract name"
      assertEqual (declaration.value.genericParameters.map genericNames)
        (some ["t"]) "contract generic parameters"
      assertEqual (byteRange declaration.value.bodySpan) (19, 271)
        "contract body span"
      match declaration.value.members with
      | [field, function, constructor, fallback, alias, enum] =>
          assertEqual [byteRange field.span, byteRange function.span,
              byteRange constructor.span, byteRange fallback.span,
              byteRange alias.span, byteRange enum.span]
            [(23, 41), (44, 92), (95, 154), (157, 203),
              (206, 224), (227, 269)] "contract member order and spans"
          match field.value with
          | .field declaration =>
              assertEqual declaration.value.name.value "balance" "field name"
              assertEqual (typeName? declaration.value.type) (some "word")
                "field type"
              match declaration.value.initializer with
              | some { value := .literal { value := .decimal "0", .. }, .. } =>
                  pure ()
              | initializer => throw (IO.userError
                  s!"field initializer changed: {reprStr initializer}")
          | value => throw (IO.userError s!"field member changed: {reprStr value}")
          match function.value with
          | .function declaration =>
              assertEqual declaration.value.signature.name.value "get"
                "contract function name"
              assertEqual (declaration.value.signature.modifiers.publicMarker.map
                byteRange) (some (59, 65)) "contract public marker"
              assertEqual (tailName? declaration.value.body) (some "balance")
                "contract function tail"
          | value => throw (IO.userError
              s!"function member changed: {reprStr value}")
          match constructor.value with
          | .constructor declaration =>
              assertEqual (parameterNames declaration.value.parameters) ["seed"]
                "constructor parameters"
              assertEqual (declaration.value.payableMarker.map byteRange)
                (some (127, 134)) "constructor payable marker"
          | value => throw (IO.userError
              s!"constructor member changed: {reprStr value}")
          match fallback.value with
          | .fallback declaration =>
              assertEqual (parameterNames declaration.value.parameters) ["arg"]
                "invalid fallback parameter retained"
              assertEqual (declaration.value.payableMarker.map byteRange)
                (some (184, 191)) "fallback payable marker"
          | value => throw (IO.userError
              s!"fallback member changed: {reprStr value}")
          match alias.value with
          | .typeAlias declaration =>
              assertEqual declaration.value.name.value "Local"
                "contract type alias"
          | value => throw (IO.userError s!"alias member changed: {reprStr value}")
          match enum.value with
          | .enum declaration =>
              assertEqual declaration.value.name.value "Flag" "contract enum name"
              assertEqual (declaration.value.deriveAttribute.map fun derive =>
                derive.value.targets.elements.map qualifiedText)
                (some ["Eq"]) "contract enum derive"
              assertEqual (declaration.value.constructors.map fun constructor =>
                constructor.value.name.value) ["Off", "On"]
                "contract enum constructors"
          | value => throw (IO.userError s!"enum member changed: {reprStr value}")
      | members => throw (IO.userError
          s!"contract members changed: {reprStr members}")
  | items => throw (IO.userError s!"contract item changed: {reprStr items}")

/-- Run canonical contract declaration and entry-point parser regressions. -/
def testSyntaxParserContracts : IO Unit := do
  testDeriveContractFieldBoundary
  testMalformedFieldRecovery
  testContractDeclaration

end Tests
