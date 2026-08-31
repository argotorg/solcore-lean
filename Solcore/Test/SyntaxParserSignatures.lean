import Solcore.Syntax.Parser.Signature

/-! Direct executable regressions for canonical function signatures. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Parser.genericParameters_validFor
example := @Parser.genericParameters_preservesTokenWindow
example := @Parser.genericParameters_preservesTokensOnSuccess
example := @Parser.genericParameters_cursorMonotoneOnSuccess
example := @Parser.genericParameters_startsAtCurrentTokenOnSuccess
example := @Parser.optionalGenericParameters_validFor
example := @Parser.optionalGenericParameters_preservesTokenWindow
example := @Parser.optionalGenericParameters_preservesTokensOnSuccess
example := @Parser.optionalGenericParameters_cursorMonotoneOnSuccess

private abbrev ByteRange := Nat × Nat

private def parserSource : SourceId := {
  origin := .main
  path := "parser-signatures.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private structure SignatureRun where
  signature : FunctionSignature
  diagnostics : List ParseDiagnostic

private def runSignature (label content : String)
    (location : Parser.FunctionLocation) : IO SignatureRun := do
  let file : SourceFile := { id := parserSource, content }
  let lexed ← match Lexer.lex file with
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
    | .ok value => pure value
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match Parser.functionSignature location (Parser.State.initial file lexed) with
  | .ok signature state =>
      unless state.atEnd do
        throw (IO.userError
          s!"{label}: left {state.remainingCount} token(s) unconsumed")
      unless signature.span.isValidFor file do
        throw (IO.userError s!"{label}: invalid signature span")
      unless state.diagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: invalid diagnostic span")
      pure { signature, diagnostics := state.diagnostics }
  | .reject failure _ => throw (IO.userError
      s!"{label}: parser rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private inductive SignatureTypeShape where
  | named (path : List String) (arguments : Option (List SignatureTypeShape))
  | tuple (elements : List SignatureTypeShape)
  | comptime (inner : SignatureTypeShape)
  | other
  | error
  deriving Repr, BEq, Inhabited

private partial def typeShape (type : TypeExpr) : SignatureTypeShape :=
  match type.value with
  | .named name arguments => .named
      (name.value.components.toList.map (fun item => item.value))
      (arguments.map fun items => items.elements.toList.map typeShape)
  | .tuple elements => .tuple (elements.map typeShape)
  | .comptime _ _ inner => .comptime (typeShape inner)
  | .error => .error
  | _ => .other

private inductive SignatureParameterShape where
  | typed (comptime : Bool) (name : String) (type : SignatureTypeShape)
  | error
  deriving Repr, BEq

private def parameterShape (parameter : FunctionParameter) : SignatureParameterShape :=
  match parameter.value with
  | .typed marker name type =>
      .typed marker.isSome name.value (typeShape type)
  | .error => .error

private structure SignaturePredicateShape where
  subject : SignatureTypeShape
  traitName : String
  arguments : Option (List SignatureTypeShape)
  deriving Repr, BEq

private def predicateShape (predicate : Predicate) : SignaturePredicateShape := {
  subject := typeShape predicate.subject
  traitName := predicate.traitName.value
  arguments := predicate.arguments.map fun values =>
    values.elements.toList.map typeShape
}

private def names (values : GenericParameters) : List String :=
  values.elements.toList.map (fun name => name.value)

private def named (name : String) : SignatureTypeShape := .named [name] none

private def testCanonicalContractSignature : IO Unit := do
  let source :=
    "function combine<a, b,>(left: pkg.Box<a>, comptime right: b,) public payable returns (pkg.Pair<a, b>,) where (a: Eq, pkg.Box<b>: Convert<a, b>,)"
  let run ← runSignature "canonical contract signature" source .contract
  let signature := run.signature
  assertEqual run.diagnostics [] "canonical signature diagnostics"
  assertEqual signature.name.value "combine" "canonical signature name"
  assertEqual (signature.genericParameters.map names)
    (some ["a", "b"]) "generic trailing comma"
  assertEqual (signature.parameters.elements.map parameterShape) [
    .typed false "left" (.named ["pkg", "Box"] (some [named "a"])),
    .typed true "right" (named "b")
  ] "typed and comptime parameters"
  assertEqual (signature.modifiers.publicMarker.map byteRange) (some (62, 68))
    "public marker span"
  assertEqual (signature.modifiers.payableMarker.map byteRange) (some (69, 76))
    "payable marker span"
  assertEqual (signature.returnsClause.map fun clause =>
      clause.types.elements.map typeShape)
    (some [.named ["pkg", "Pair"] (some [named "a", named "b"])])
    "trailing return list"
  assertEqual (signature.whereClause.map fun clause =>
      clause.predicates.toList.map predicateShape) (some [
    ⟨named "a", "Eq", none⟩,
    ⟨.named ["pkg", "Box"] (some [named "b"]), "Convert",
      some [named "a", named "b"]⟩
  ]) "grouped predicates and trait arguments"
  assertEqual (byteRange signature.span) (0, 144) "signature span"
  assertEqual (signature.genericParameters.map
    (fun values => byteRange values.span)) (some (16, 23)) "generic span"
  assertEqual (byteRange signature.parameters.span) (23, 61) "parameter span"
  assertEqual (signature.parameters.elements.map
    (fun parameter => byteRange parameter.span)) [(24, 40), (42, 59)]
    "individual parameter spans"
  assertEqual (signature.returnsClause.map
    (fun clause => byteRange clause.span)) (some (77, 102)) "returns span"
  assertEqual (signature.whereClause.map
    (fun clause => byteRange clause.span)) (some (103, 144)) "where span"

private def testEmptyAndTrailingLists : IO Unit := do
  let implicit ← runSignature "implicit unit" "function implicit()" .module
  assertEqual implicit.diagnostics [] "implicit-unit diagnostics"
  assertEqual implicit.signature.parameters.elements [] "empty parameters"
  assertEqual implicit.signature.returnsClause none "absent returns clause"

  let explicit ← runSignature "explicit unit"
    "function explicit() returns ()" .module
  assertEqual explicit.diagnostics [] "explicit-unit diagnostics"
  assertEqual (explicit.signature.returnsClause.map
    (fun clause => clause.types.elements)) (some []) "empty return list"

  let trailing ← runSignature "trailing lists"
    "function trailing<t,>(value: t,) returns (t,)" .module
  assertEqual trailing.diagnostics [] "trailing-list diagnostics"
  assertEqual (trailing.signature.genericParameters.map names) (some ["t"])
    "trailing generic list"
  assertEqual (trailing.signature.parameters.elements.map parameterShape)
    [.typed false "value" (named "t")] "trailing parameter list"
  assertEqual (trailing.signature.returnsClause.map fun clause =>
    clause.types.elements.map typeShape) (some [named "t"])
    "trailing returns list"

private def testModifierLocations : IO Unit := do
  let source := "function exposed() public payable"
  let moduleRun ← runSignature "module modifiers" source .module
  assertEqual (moduleRun.signature.modifiers.publicMarker.map byteRange)
    (some (19, 25)) "module public marker retained"
  assertEqual (moduleRun.signature.modifiers.payableMarker.map byteRange)
    (some (26, 33)) "module payable marker retained"
  assertEqual (moduleRun.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((19, 25), .constraintViolation
      (.modifierOutsideContract .publicKw)),
    ((26, 33), .constraintViolation
      (.modifierOutsideContract .payableKw))
  ] "module modifier diagnostics"
  let contractRun ← runSignature "contract modifiers" source .contract
  assertEqual contractRun.diagnostics [] "contract modifier allowance"
  assertEqual contractRun.signature.modifiers moduleRun.signature.modifiers
    "modifier source shape independent of location"

private def testBareWhereClause : IO Unit := do
  let run ← runSignature "bare where clause"
    "function constrained<t>() where t: Eq, pkg.Box<t>: Convert<word, t,>,"
    .module
  assertEqual run.diagnostics [] "bare where diagnostics"
  assertEqual (run.signature.whereClause.map fun clause =>
      clause.predicates.toList.map predicateShape) (some [
    ⟨named "t", "Eq", none⟩,
    ⟨.named ["pkg", "Box"] (some [named "t"]), "Convert",
      some [named "word", named "t"]⟩
  ]) "bare predicates and trailing trait arguments"
  match run.signature.whereClause with
  | some clause =>
      assertEqual clause.predicates.toList.length 2 "bare predicate count"
      assertEqual clause.span.endByte
        "function constrained<t>() where t: Eq, pkg.Box<t>: Convert<word, t,>,".utf8ByteSize
        "bare trailing comma included in span"
  | none => throw (IO.userError "bare where clause was lost")

private def testParameterDiagnostics : IO Unit := do
  let untyped ← runSignature "untyped parameter"
    "function missing(value)" .module
  assertEqual (untyped.signature.parameters.elements.map parameterShape)
    [.error] "untyped parameter recovery shape"
  assertEqual (untyped.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((17, 22), .constraintViolation .namedParameterRequiresType)
  ] "untyped parameter diagnostic"

  let comptimeType ← runSignature "comptime parameter type"
    "function invalid(value: comptime<word>)" .module
  assertEqual (comptimeType.signature.parameters.elements.map parameterShape)
    [.typed false "value" (.comptime (named "word"))]
    "comptime type source shape"
  match comptimeType.diagnostics with
  | [{ span, kind := .constraintViolation .comptimeTypeInParameter }] =>
      assertEqual (byteRange span) (24, 38) "comptime-type diagnostic span"
  | diagnostics => throw (IO.userError
      s!"comptime parameter type: unexpected diagnostics {reprStr diagnostics}")

  let recovered ← runSignature "parameter recovery"
    "function recover(+ -, good: word)" .module
  assertEqual (recovered.signature.parameters.elements.map parameterShape)
    [.error, .typed false "good" (named "word")]
    "recovered parameter and following parameter"
  match recovered.diagnostics with
  | [{ span := first, kind := firstKind },
      { span := consumed, kind := secondKind }] =>
      assertEqual firstKind (.unexpected (some (.symbol .plus))
        { head := .identifier, tail := [] } .parameter)
        "parameter failure diagnostic"
      assertEqual secondKind (.recovered .functionParameter)
        "parameter recovery diagnostic"
      assertEqual (byteRange first) (17, 18) "parameter failure span"
      assertEqual (byteRange consumed) (17, 20) "parameter recovery span"
  | diagnostics => throw (IO.userError
      s!"parameter recovery: unexpected diagnostics {reprStr diagnostics}")

/-- Run direct canonical function-signature parser regressions. -/
def testSyntaxParserSignatures : IO Unit := do
  testCanonicalContractSignature
  testEmptyAndTrailingLists
  testModifierLocations
  testBareWhereClause
  testParameterDiagnostics

end Tests
