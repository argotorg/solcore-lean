import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramSignatures
import Solcore.Frontend.TypedTraitResolution

/-! Executable source-to-signature and source-to-impl-rule regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramSignatures

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def parsed (path content : String) : IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := {
    id := { origin := .main, path }
    content
  }
  match Syntax.Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{path}: parser invariant: {reprStr error}")
  | .ok output => pure output.parsed

private def catalog (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors =>
      throw (IO.userError s!"environment failure: {reprStr errors}")

private def declarationNamed (environment : ProgramEnvironment)
    (name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.name == some name with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing declaration {name}")

private def testSuccessfulCollection : IO Unit := do
  let source ← parsed "signatures.solc" (String.intercalate "\n" [
    "trait Eq<T> {}",
    "trait Convert<Subject, Target> {}",
    "enum Box<T> { Wrap(T) }",
    "impl<T> Convert<Box<T>, Word> where T: Eq {}",
    "function choose<T>(left: T, right: T) returns (T) where T: Eq { left }"
  ])
  let environment ← catalog [source]
  let eqTrait ← declarationNamed environment "Eq"
  let convertTrait ← declarationNamed environment "Convert"
  let box ← declarationNamed environment "Box"
  let choose ← declarationNamed environment "choose"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"signature failure: {reprStr errors}")
  assertTrue (decide (signatures.functions.length = 1 ∧
      signatures.implRules.length = 1 ∧ signatures.dataTypes.length = 1))
    "function/impl source collection changed"
  assertTrue (decide ((signatures.functionsNamed "choose").length = 1 ∧
      (signatures.localFunctionsNamed choose.id.moduleId "choose").length = 1))
    "overload-preserving function lookup changed"
  match signatures.functions with
  | [signature] =>
      let parameter : TypeSystem.Ty :=
        .parameter { owner := choose.id, index := 0 }
      assertTrue (decide (signature.parameterNames = ["left", "right"] ∧
          signature.parameterTypes = [parameter, parameter] ∧
          signature.returnTypes = [parameter] ∧
          signature.scheme.parameters = [{ owner := choose.id, index := 0 }] ∧
          signature.scheme.body = .function (.product parameter parameter) parameter))
        "resolved generic function scheme changed"
      match signature.scheme.predicates with
      | [predicate] =>
          assertTrue (decide (predicate.trait = .declaration eqTrait.id ∧
              predicate.subject = parameter ∧ predicate.arguments = []))
            "function where predicate changed"
      | predicates => throw (IO.userError
          s!"function predicates changed: {reprStr predicates}")
      let instantiated := signature.scheme.instantiate 7
      assertTrue (decide (instantiated.parameterSubstitution =
          [({ owner := choose.id, index := 0 }, .variable ⟨7⟩)] ∧
          instantiated.body =
          .function (.product (.variable ⟨7⟩) (.variable ⟨7⟩))
            (.variable ⟨7⟩) ∧
          instantiated.predicates = [{
            trait := eqTrait.id
            subject := .variable ⟨7⟩
            arguments := []
          }] ∧ instantiated.next = 8))
        "scheme instantiation did not share fresh variables"
  | functions => throw (IO.userError
      s!"function signatures changed: {reprStr functions}")
  match signatures.implRules with
  | [rule] =>
      let some implementation := rule.id.declaration?
        | throw (IO.userError "source impl rule lost its declaration identity")
      let parameter : TypeSystem.Ty :=
        .parameter { owner := implementation, index := 0 }
      assertTrue (decide (rule.id = .declaration implementation ∧
          rule.head.trait = .declaration convertTrait.id ∧
          rule.head.subject = TypeSystem.Ty.nominal box.id [parameter] ∧
          rule.head.arguments = [.word] ∧
          rule.wherePredicates = [{
            trait := .declaration eqTrait.id
            subject := parameter
            arguments := []
          }]))
        "impl head/where predicate resolution changed"
  | rules => throw (IO.userError s!"impl rules changed: {reprStr rules}")
  let dataType ← match signatures.dataType? box.id with
    | some dataType => pure dataType
    | none => throw (IO.userError "missing Box data signature")
  let dataParameter : TypeSystem.Ty :=
    .parameter { owner := box.id, index := 0 }
  match dataType.constructors with
  | [constructor] =>
      assertTrue (decide (dataType.name = "Box" ∧
          dataType.parameters = [{ owner := box.id, index := 0 }] ∧
          constructor.id = { dataType := box.id, constructorIndex := 0 } ∧
          constructor.name = "Wrap" ∧
          constructor.payloadTypes = [dataParameter]))
        "generic data constructor catalog changed"
  | constructors => throw (IO.userError
      s!"Box constructor catalog changed: {reprStr constructors}")

private def testContractCatalog : IO Unit := do
  let source ← parsed "contracts.solc" (String.intercalate "\n" [
    "contract Vault<T> {",
    "  enum Inner { Empty }",
    "  function keep(value: T) {}",
    "}",
    "enum Outside { Only }",
    "contract Registry {}"
  ])
  let environment ← catalog [source]
  let vault ← declarationNamed environment "Vault"
  let outside ← declarationNamed environment "Outside"
  let registry ← declarationNamed environment "Registry"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"contract signature failure: {reprStr errors}")
  match signatures.contracts with
  | [vaultSignature, registrySignature] =>
      assertTrue (decide (
          vaultSignature.id = vault.id ∧
          vaultSignature.name = "Vault" ∧
          vaultSignature.parameters = [{ owner := vault.id, index := 0 }] ∧
          vaultSignature.source.value.members.length = 2 ∧
          registrySignature.id = registry.id ∧
          registrySignature.name = "Registry" ∧
          registrySignature.parameters = []))
        "contract catalog lost source order, identity, or generic scope"
  | contracts => throw (IO.userError
      s!"contract catalog changed: {reprStr contracts}")
  let catalogedVault ← match signatures.contract? vault.id with
    | some signature => pure signature
    | none => throw (IO.userError "contract identity lookup lost Vault")
  assertTrue (decide (catalogedVault.id = vault.id ∧
      catalogedVault.name = "Vault"))
    "contract identity lookup returned the wrong signature"
  match signatures.dataTypes with
  | [dataType] =>
      assertTrue (decide (dataType.id = outside.id ∧
          dataType.name = "Outside" ∧ signatures.functions.length = 0))
        "contract members leaked into top-level function/data catalogs"
  | dataTypes => throw (IO.userError
      s!"contract declarations entered the data catalog: {reprStr dataTypes}")

private def testDefaultImplementationMarkerCollection : IO Unit := do
  let source ← parsed "default_implementations.solc" (String.intercalate "\n" [
    "trait Select<T> {}",
    "default impl<T> Select<T> {}",
    "impl Select<Word> {}"
  ])
  let environment ← catalog [source]
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"default implementation signature failure: {reprStr errors}")
  match signatures.implementations, signatures.implRules with
  | [fallback, specific], [fallbackRule, specificRule] =>
      assertTrue (decide (
          fallback.isDefault ∧ fallback.source.value.defaultMarker.isSome ∧
          fallbackRule.isDefault ∧ fallbackRule.id = fallback.id ∧
          !specific.isDefault ∧ specific.source.value.defaultMarker.isNone ∧
          !specificRule.isDefault ∧ specificRule.id = specific.id))
        "default impl marker was not preserved by the signature/rule projection"
  | implementations, rules => throw (IO.userError
      s!"default implementation catalog changed: {reprStr implementations}; {reprStr rules}")

private def testComptimeMarkerCollection : IO Unit := do
  let source ← parsed "comptime_signatures.solc" (String.intercalate "\n" [
    "trait Stage<T> {",
    "  function stage(comptime value: T) returns (comptime<T>);",
    "}",
    "impl Stage<Word> {",
    "  function stage(comptime value: Word) returns (comptime<Word>) {",
    "    return value;",
    "  }",
    "}",
    "function choose<T>(comptime value: T, other: Word) returns (comptime<T>) {",
    "  return value;",
    "}"
  ])
  let environment ← catalog [source]
  let stage ← declarationNamed environment "Stage"
  let choose ← declarationNamed environment "choose"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"comptime signature failure: {reprStr errors}")
  let chooseSignature ← match signatures.functions with
    | [signature] => pure signature
    | functions => throw (IO.userError
        s!"comptime function catalog changed: {reprStr functions}")
  let parameter : TypeSystem.Ty :=
    .parameter { owner := choose.id, index := 0 }
  assertTrue (decide (chooseSignature.parameterNames = ["value", "other"] ∧
      chooseSignature.parameterTypes = [parameter, .word] ∧
      chooseSignature.parameterComptime = [true, false] ∧
      chooseSignature.returnTypes = [parameter] ∧
      chooseSignature.returnComptime ∧
      chooseSignature.scheme.body =
        .function (.product parameter .word) parameter))
    "function comptime markers were dropped or embedded in semantic types"
  let traitSignature ← match signatures.trait? stage.id with
    | some signature => pure signature
    | none => throw (IO.userError "missing staged trait signature")
  let traitMethod ← match traitSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"staged trait method catalog changed: {reprStr methods}")
  let traitParameter : TypeSystem.Ty :=
    .parameter { owner := stage.id, index := 0 }
  assertTrue (decide (traitMethod.parameterTypes = [traitParameter] ∧
      traitMethod.parameterComptime = [true] ∧
      traitMethod.returnTypes = [traitParameter] ∧
      traitMethod.returnComptime))
    "trait method comptime markers were not normalized"
  let implementation ← match signatures.implementations with
    | [implementation] => pure implementation
    | implementations => throw (IO.userError
        s!"staged implementation catalog changed: {reprStr implementations}")
  let implMethod ← match implementation.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"staged implementation method catalog changed: {reprStr methods}")
  let synthetic := implementation.functionSignatureOfMethod implMethod
  assertTrue (decide (implMethod.parameterTypes = [.word] ∧
      implMethod.parameterComptime = [true] ∧
      implMethod.returnTypes = [.word] ∧ implMethod.returnComptime ∧
      synthetic.parameterComptime = [true] ∧
      synthetic.returnComptime ∧
      synthetic.scheme.body = .function .word .word))
    "implementation method comptime markers did not reach its function view"

private def testBuiltinIntResolutionProfile : IO Unit := do
  let source ← parsed "source_int.solc" (String.intercalate "\n" [
    "trait Int<T> {}",
    "impl Int<Bool> {}"
  ])
  let environment ← catalog [source]
  let sourceTrait ← declarationNamed environment "Int"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"builtin Int profile failed: {reprStr errors}")
  let sourceRule ← match signatures.implRules with
    | [rule] => pure rule
    | rules => throw (IO.userError
        s!"source Int catalog changed: {reprStr rules}")
  let some sourceImplementation := sourceRule.id.declaration?
    | throw (IO.userError "source Int rule lost its declaration identity")
  assertTrue (decide (signatures.resolutionRules =
      [ProgramSignatures.builtinIntWordRule,
        ProgramSignatures.builtinIntIntegerRule, sourceRule] ∧
      signatures.traits.length = 1 ∧
      signatures.implementations.length = 1 ∧
      signatures.implRules.length = 1 ∧
      signatures.resolutionRules.length = 3))
    "combined resolution rules lost builtin-first order or source-only counts"
  let builtinWord := ProgramSignatures.builtinIntPredicate .word
  let builtinInteger := ProgramSignatures.builtinIntPredicate .integer
  let builtinBool := ProgramSignatures.builtinIntPredicate .bool
  let builtinFlexible := ProgramSignatures.builtinIntPredicate (.variable ⟨0⟩)
  let builtinExtraArgument : ProgramPredicate := {
    ProgramSignatures.builtinIntPredicate .word with
    arguments := [.bool]
  }
  let sourceBool : ProgramPredicate := {
    trait := sourceTrait.id
    subject := .bool
    arguments := []
  }
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinWord).outcome with
  | .success (.byImpl goal (.builtin .intWord) []) =>
      assertTrue (decide (goal = builtinWord))
        "builtin Word evidence retained the wrong goal"
  | outcome => throw (IO.userError
      s!"builtin Int<Word> resolution changed: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinInteger).outcome with
  | .success (.byImpl goal (.builtin .intInteger) []) =>
      assertTrue (decide (goal = builtinInteger))
        "builtin integer evidence retained the wrong goal"
  | outcome => throw (IO.userError
      s!"builtin Int<integer> resolution changed: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinBool).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int<Bool> unexpectedly crossed into source Int: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinFlexible).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int rules defaulted a caller-owned variable: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      builtinExtraArgument).outcome with
  | .noSolution => pure ()
  | outcome => throw (IO.userError
      s!"builtin Int accepted an extra argument: {reprStr outcome}")
  match (TypedTraitResolution.resolve signatures.resolutionRules 1
      sourceBool).outcome with
  | .success (.byImpl goal (.declaration implementation) []) =>
      assertTrue (decide (goal = sourceBool ∧ implementation = sourceImplementation))
        "source Int evidence retained the wrong tagged goal or implementation"
  | outcome => throw (IO.userError
      s!"source trait named Int did not remain resolvable: {reprStr outcome}")

private def testMethodCatalog : IO Unit := do
  let source ← parsed "methods.solc" (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Add<T> where T: Marker {",
    "  function add(left: T, right: T) returns (T) where T: Marker;",
    "}",
    "impl Add<Word> where Word: Marker {",
    "  function add(left: Word, right: Word) returns (Word) where Word: Marker {",
    "    return left - right;",
    "  }",
    "}"
  ])
  let environment ← catalog [source]
  let marker ← declarationNamed environment "Marker"
  let add ← declarationNamed environment "Add"
  let implementation ← match environment.declarations.find? fun declaration =>
      declaration.kind == ProgramDeclarationKind.implementation with
    | some declaration => pure declaration
    | none => throw (IO.userError "missing Add implementation")
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors =>
        throw (IO.userError s!"method signature failure: {reprStr errors}")
  assertTrue (decide (signatures.traits.length = 2 ∧
      signatures.implementations.length = 1 ∧
      signatures.implRules.length = 1))
    "trait/implementation catalog sizes changed"
  let some traitSignature := signatures.trait? add.id
    | throw (IO.userError "missing Add trait signature")
  let traitParameter : TypeSystem.Ty :=
    .parameter { owner := add.id, index := 0 }
  assertTrue (decide (traitSignature.parameters =
      [{ owner := add.id, index := 0 }] ∧
      traitSignature.wherePredicates = [{
        trait := marker.id
        subject := traitParameter
        arguments := []
      }]))
    "trait parameters or declaration predicates changed"
  let traitMethod ← match traitSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"trait method catalog changed: {reprStr methods}")
  assertTrue (decide (traitMethod.id = {
        trait := add.id
        methodIndex := 0
      } ∧ traitMethod.name = "add" ∧
      traitMethod.parameterNames = ["left", "right"] ∧
      traitMethod.parameterTypes = [traitParameter, traitParameter] ∧
      traitMethod.returnTypes = [traitParameter] ∧
      traitMethod.wherePredicates = [{
        trait := marker.id
        subject := traitParameter
        arguments := []
      }]))
    "resolved trait method signature changed"
  let some implementationSignature := signatures.implementation? implementation.id
    | throw (IO.userError "missing Add implementation signature")
  assertTrue (decide (implementationSignature.parameters = [] ∧
      implementationSignature.head = {
        trait := add.id
        subject := .word
        arguments := []
      } ∧ implementationSignature.wherePredicates = [{
        trait := marker.id
        subject := .word
        arguments := []
      }]))
    "implementation head or declaration predicates changed"
  let implMethod ← match implementationSignature.methods with
    | [method] => pure method
    | methods => throw (IO.userError
        s!"implementation method catalog changed: {reprStr methods}")
  assertTrue (decide (implMethod.id = {
        implementation := implementation.id
        methodIndex := 0
      } ∧ implMethod.traitMethod = traitMethod.id ∧
      implMethod.name = "add" ∧
      implMethod.parameterNames = ["left", "right"] ∧
      implMethod.parameterTypes = [.word, .word] ∧
      implMethod.returnTypes = [.word] ∧
      implMethod.wherePredicates = [{
        trait := marker.id
        subject := .word
        arguments := []
      }]))
    "resolved implementation method signature changed"
  assertTrue (decide ((signatures.traitMethod? traitMethod.id).isSome ∧
      (signatures.implMethod? implMethod.id).isSome))
    "role-tagged method lookup changed"
  let synthetic := implementationSignature.functionSignatureOfMethod implMethod
  assertTrue (decide (synthetic.id = implementation.id ∧
      synthetic.name = "add" ∧
      synthetic.parameterNames = ["left", "right"] ∧
      synthetic.parameterTypes = [.word, .word] ∧
      synthetic.returnTypes = [.word] ∧
      synthetic.scheme.parameters = [] ∧
      synthetic.scheme.predicates =
        implementationSignature.wherePredicates ++ implMethod.wherePredicates ∧
      synthetic.scheme.body = .function (.product .word .word) .word))
    "implementation method function projection changed"

private def expectSingleError (content : String)
    (accept : ProgramSignatureError → Bool) : IO Unit := do
  let source ← parsed "failure.solc" content
  let environment ← catalog [source]
  match buildProgramSignatures environment with
  | .error [error] =>
      assertTrue (accept error) s!"unexpected signature error: {reprStr error}"
  | result => throw (IO.userError s!"unexpected signature result: {reprStr result}")

private def testFailures : IO Unit := do
  expectSingleError
    "function duplicate<T>(left: T, left: T) { return; }"
    fun error => match error with
      | .duplicateFunctionParameter _ "left" 0 1 => true
      | _ => false
  expectSingleError
    "function duplicateGeneric<T, T>() { return; }"
    fun error => match error with
      | .typeResolution _ (.duplicateGenericParameter "T" 0 1) => true
      | _ => false
  expectSingleError
    "contract Duplicate<T, T> {}"
    fun error => match error with
      | .typeResolution _ (.duplicateGenericParameter "T" 0 1) => true
      | _ => false
  expectSingleError
    "function malformed(value) { return; }"
    fun error => match error with
      | .malformedFunctionParameter _ 0 => true
      | _ => false
  expectSingleError
    "function missing(value: Missing) { return; }"
    fun error => match error with
      | .typeResolution _ (.unknownTypeName ["Missing"]) => true
      | _ => false
  expectSingleError
    "function constrained<T>() where T: Missing { return; }"
    fun error => match error with
      | .unknownTrait _ "Missing" => true
      | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Convert<Subject, Target> {}",
    "function constrained<T>() where T: Convert { return; }"
  ]) fun error => match error with
    | .traitArityMismatch _ _ 2 1 => true
    | _ => false
  expectSingleError
    "function nested() returns (comptime<comptime<Word>>) { return 0; }"
    fun error => match error with
      | .nestedComptimeReturn _ 0 => true
      | _ => false
  expectSingleError
    "function mixed() returns (Word, comptime<Word>) { return (0, 0); }"
    fun error => match error with
      | .comptimeReturnMustBeSingleton _ 1 2 => true
      | _ => false
  expectSingleError
    "enum Duplicate { Same, Same(Word) }"
    fun error => match error with
      | .duplicateDataConstructor _ "Same" 0 1 => true
      | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Identity<T> {}",
    "impl<T, U> Identity<T> {}"
  ]) fun error => match error with
    | .implementationParameterNotInHead implementation parameter =>
        decide (parameter.owner = implementation ∧ parameter.index = 1)
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Required<T> where T: Marker {}",
    "impl Required<Word> {}"
  ]) fun error => match error with
    | .missingImplementationTraitPredicate implementation predicate =>
        match predicate.trait with
        | .declaration trait => decide (
            implementation.declarationIndex = 2 ∧
            trait.declarationIndex = 0 ∧
            trait.moduleId = implementation.moduleId ∧
            predicate.subject = .word ∧ predicate.arguments = [])
        | .builtin _ => false
    | _ => false

private def testTraitPredicateContainmentAllowsReorderingAndExtras : IO Unit := do
  let source ← parsed "predicates.solc"
    (String.intercalate "\n" [
      "trait First<T> {}",
      "trait Second<T> {}",
      "trait Extra<T> {}",
      "trait Required<T> where T: First, T: Second {}",
      "impl Required<Word> where Word: Extra, Word: Second, Word: First {}"
    ])
  let environment ← catalog [source]
  match buildProgramSignatures environment with
  | .ok signatures =>
      assertTrue (signatures.implementations.length == 1)
        "reordered required predicates plus an extra predicate changed collection"
  | .error errors => throw (IO.userError
      s!"valid reordered implementation predicates were rejected: {reprStr errors}")

private def testMethodFailures : IO Unit := do
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {}"
  ]) fun error => match error with
    | .missingImplMethod _ { methodIndex := 0, .. } "add" => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> {}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ]) fun error => match error with
    | .extraImplMethod { methodIndex := 0, .. } "add" => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(left: T, right: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(left: Bool, right: Bool) returns (Bool) { return left; }",
    "}"
  ]) fun error => match error with
    | .implMethodSignatureMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [.word, .word] [.bool, .bool]
        [.word] [.bool] => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Stage<T> {",
    "  function stage(comptime value: T) returns (comptime<T>);",
    "}",
    "impl Stage<Word> {",
    "  function stage(value: Word) returns (Word) { return value; }",
    "}"
  ]) fun error => match error with
    | .implMethodComptimeMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [true] [false] true false => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Marker<T> {}",
    "trait Add<T> {",
    "  function add(left: T, right: T) returns (T) where T: Marker;",
    "}",
    "impl Add<Word> {",
    "  function add(left: Word, right: Word) returns (Word) { return left; }",
    "}"
  ]) fun error => match error with
    | .implMethodPredicateMismatch { methodIndex := 0, .. }
        { methodIndex := 0, .. } [_] [] => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add(value: T) returns (T); }",
    "impl Add<Word> {",
    "  function add(value: Word) returns (Word) { return value; }",
    "  function add(other: Word) returns (Word) { return other; }",
    "}"
  ]) fun error => match error with
    | .duplicateImplMethod _ "add" 0 1 => true
    | _ => false
  expectSingleError (String.intercalate "\n" [
    "trait Add<T> { function add<U>(value: T) returns (T); }",
    "impl Add<Word> {}"
  ]) fun error => match error with
    | .traitMethodLocalGenerics { methodIndex := 0, .. } => true
    | _ => false

private def testAmbiguousTrait : IO Unit := do
  let left ← parsed "left.solc" "export {Shared}; trait Shared<T> {}"
  let right ← parsed "right.solc" "export {Shared}; trait Shared<T> {}"
  let consumer ← parsed "consumer.solc" (String.intercalate "\n" [
    "import * from left;",
    "import * from right;",
    "function constrained<T>() where T: Shared { return; }"
  ])
  let environment ← catalog [left, right, consumer]
  match buildProgramSignatures environment with
  | .error [.ambiguousTrait _ "Shared" candidates] =>
      assertTrue (candidates.length == 2)
        "ambiguous trait candidates were not retained"
  | result => throw (IO.userError
      s!"ambiguous trait result changed: {reprStr result}")

private def testStrictTraitVisibility : IO Unit := do
  let provider ← parsed "provider.solc"
    "export {Hidden}; trait Hidden<T> {}"
  let unrelated ← parsed "unrelated.solc"
    "export {*}; enum Visible { Only }"
  let consumer ← parsed "consumer.solc" (String.intercalate "\n" [
    "import * from unrelated;",
    "function constrained<T>() where T: Hidden { return; }"
  ])
  let environment ← catalog [provider, unrelated, consumer]
  match buildProgramSignatures environment with
  | .error [.unknownTrait _ "Hidden"] => pure ()
  | result => throw (IO.userError
      s!"an unimported trait reached signature resolution: {reprStr result}")

end ProgramSignatures

/-- Run the first source-connected signature and trait-rule vertical slice. -/
def testProgramSignatures : IO Unit := do
  ProgramSignatures.testSuccessfulCollection
  ProgramSignatures.testContractCatalog
  ProgramSignatures.testDefaultImplementationMarkerCollection
  ProgramSignatures.testComptimeMarkerCollection
  ProgramSignatures.testBuiltinIntResolutionProfile
  ProgramSignatures.testMethodCatalog
  ProgramSignatures.testFailures
  ProgramSignatures.testTraitPredicateContainmentAllowsReorderingAndExtras
  ProgramSignatures.testMethodFailures
  ProgramSignatures.testAmbiguousTrait
  ProgramSignatures.testStrictTraitVisibility

end Tests
