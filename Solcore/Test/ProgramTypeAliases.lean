import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramSignatures

/-! Executable regressions for transparent whole-program type aliases. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

namespace ProgramTypeAliases

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (origin : Syntax.SourceOrigin) (path content : String) :
    IO Syntax.ParsedFile := do
  let file : Syntax.SourceFile := { id := { origin, path }, content }
  match Syntax.Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{path}: parser invariant: {reprStr error}")
  | .ok output =>
      unless output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"{path}: source diagnostics: {reprStr output.lexicalDiagnostics}; {reprStr output.parseDiagnostics}")
      pure output.parsed

private def build (sources : List Syntax.ParsedFile) : IO ProgramEnvironment := do
  match buildProgramEnvironment sources with
  | .ok environment => pure environment
  | .error errors =>
      throw (IO.userError s!"program environment failed: {reprStr errors}")

private def declaration (environment : ProgramEnvironment)
    (modulePath name : String) : IO ProgramDeclaration := do
  match environment.declarations.find? fun declaration =>
      declaration.id.moduleId.path.render == modulePath &&
        declaration.name == some name with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"missing declaration {modulePath}.{name}")

private def aliasBody (declaration : ProgramDeclaration) : IO Syntax.TypeExpr := do
  match declaration.source.value with
  | .typeAlias alias => pure alias.value.value
  | _ => throw (IO.userError "selected declaration was not a type alias")

private def resolveAliasBodyResult (environment : ProgramEnvironment)
    (declaration : ProgramDeclaration) :
    IO (Except ProgramTypeResolutionError TypeSystem.Ty) := do
  let source ← aliasBody declaration
  pure (resolveProgramTypeAliasBody environment declaration source)

private def resolveAliasBody (environment : ProgramEnvironment)
    (modulePath name : String) : IO TypeSystem.Ty := do
  let selected ← declaration environment modulePath name
  match ← resolveAliasBodyResult environment selected with
  | .ok type => pure type
  | .error error =>
      throw (IO.userError s!"{modulePath}.{name} did not resolve: {reprStr error}")

private def testTransparentSubstitution : IO Unit := do
  let source ← parsed .main "aliases.solc" (String.intercalate "\n" [
    "enum Box<T> { Wrap(T) }",
    "type Id(T) = T;",
    "type Pair(A, B) = (A, B);",
    "type Reverse(A, B) = Pair<B, A>;",
    "type Boxed(T) = Box<Id<T>>;",
    "type UseId = Id<Word>;",
    "type UsePair = Reverse<Word, Bool>;",
    "type UseBox = Boxed<Bool>;"
  ])
  let environment ← build [source]
  let box ← declaration environment "aliases" "Box"
  let useId ← resolveAliasBody environment "aliases" "UseId"
  let usePair ← resolveAliasBody environment "aliases" "UsePair"
  let useBox ← resolveAliasBody environment "aliases" "UseBox"
  assertTrue (decide (useId = TypeSystem.Ty.word))
    "a generic identity alias remained nominal"
  assertTrue (decide (usePair =
      TypeSystem.Ty.product TypeSystem.Ty.bool TypeSystem.Ty.word))
    "nested aliases did not compose their parameter substitutions"
  assertTrue (decide (useBox = TypeSystem.Ty.nominal box.id [.bool]))
    "an alias nested in a nominal argument was not expanded"

private def testDefinitionSiteScope : IO Unit := do
  let provider ← parsed .main "base.solc" (String.intercalate "\n" [
    "enum Hidden { Provider }",
    "export {Hidden};"
  ])
  let alias ← parsed .main "alias.solc" (String.intercalate "\n" [
    "import {Hidden} from base;",
    "type PublicAlias = Hidden;",
    "export {PublicAlias};"
  ])
  let consumer ← parsed .main "consumer.solc" (String.intercalate "\n" [
    "import {PublicAlias} from alias;",
    "enum Hidden { Consumer }",
    "type Use = PublicAlias;"
  ])
  let environment ← build [provider, alias, consumer]
  let providerHidden ← declaration environment "base" "Hidden"
  let consumerHidden ← declaration environment "consumer" "Hidden"
  let use ← resolveAliasBody environment "consumer" "Use"
  assertTrue (decide (use = TypeSystem.Ty.nominal providerHidden.id []))
    "an alias did not retain its definition-site private import"
  assertTrue (decide (use ≠ TypeSystem.Ty.nominal consumerHidden.id []))
    "a use-site declaration captured an alias body"

private def testResolvedAliasPositions : IO Unit := do
  let source ← parsed .main "positions.solc" (String.intercalate "\n" [
    "type Scalar = Word;",
    "type Table = mapping(Scalar => Scalar);",
    "type Reference = @Scalar;",
    "type Staged = comptime<Scalar>;",
    "trait Marker<T> {}",
    "impl Marker<Scalar> {}",
    "function keep(value: Scalar) returns (Scalar) where Scalar: Marker {",
    "  return value;",
    "}"
  ])
  let environment ← build [source]
  let marker ← declaration environment "positions" "Marker"
  let table ← resolveAliasBody environment "positions" "Table"
  let reference ← resolveAliasBody environment "positions" "Reference"
  let staged ← resolveAliasBody environment "positions" "Staged"
  assertTrue (decide (table = TypeSystem.Ty.mapping .word .word ∧
      reference = TypeSystem.Ty.proxy .word ∧
      staged = TypeSystem.Ty.comptime .word))
    "aliases did not normalize inside mapping, proxy, or comptime types"
  let signatures ← match buildProgramSignatures environment with
    | .ok signatures => pure signatures
    | .error errors => throw (IO.userError
        s!"alias position signatures failed: {reprStr errors}")
  match signatures.functions, signatures.implRules with
  | [signature], [rule] =>
      assertTrue (decide (
          signature.parameterTypes = [.word] ∧
          signature.returnTypes = [.word] ∧
          signature.scheme.predicates = [{
            trait := .declaration marker.id
            subject := .word
            arguments := []
          }] ∧
          rule.head = {
            trait := .declaration marker.id
            subject := .word
            arguments := []
          }))
        "aliases did not normalize in a signature predicate or impl head"
  | functions, rules => throw (IO.userError
      s!"alias position catalogs changed: {reprStr functions}; {reprStr rules}")

private def testCycleDiagnostics : IO Unit := do
  let source ← parsed .main "cycles.solc" (String.intercalate "\n" [
    "type Direct = Direct;",
    "type Left = Right;",
    "type Right = Left;",
    "type UseMutual = Left;"
  ])
  let environment ← build [source]
  let direct ← declaration environment "cycles" "Direct"
  let left ← declaration environment "cycles" "Left"
  let right ← declaration environment "cycles" "Right"
  match ← resolveAliasBodyResult environment direct with
  | .error (.cyclicTypeAlias cycle) =>
      assertTrue (decide (cycle = [direct.id, direct.id]))
        "a direct alias cycle did not retain its closed declaration path"
  | result => throw (IO.userError
      s!"direct alias cycle result changed: {reprStr result}")
  let useMutual ← declaration environment "cycles" "UseMutual"
  match ← resolveAliasBodyResult environment useMutual with
  | .error (.cyclicTypeAlias cycle) =>
      assertTrue (decide (cycle = [left.id, right.id, left.id]))
        "a mutual alias cycle did not retain its closed declaration path"
  | result => throw (IO.userError
      s!"mutual alias cycle result changed: {reprStr result}")

private def testExpansionBudget : IO Unit := do
  let source ← parsed .main "fuel.solc" (String.intercalate "\n" [
    "type Base = Word;",
    "type Middle = Base;",
    "type Use = Middle;"
  ])
  let environment ← build [source]
  let use ← declaration environment "fuel" "Use"
  let body ← aliasBody use
  match resolveProgramTypeAliasBodyWithBudgets environment use 1 1 body with
  | .error .aliasExpansionLimit => pure ()
  | result => throw (IO.userError
      s!"independent alias expansion budget result changed: {reprStr result}")

private def testSharedNodeBudget : IO Unit := do
  let source ← parsed .main "branching_fuel.solc" (String.intercalate "\n" [
    "type Base = Word;",
    "type Pair = (Base, Base);",
    "type Quad = (Pair, Pair);",
    "type Use = Quad;"
  ])
  let environment ← build [source]
  let use ← declaration environment "branching_fuel" "Use"
  let body ← aliasBody use
  match resolveProgramTypeAliasBodyWithBudgets environment use 16 8 body with
  | .error .aliasExpansionLimit => pure ()
  | result => throw (IO.userError
      s!"branching aliases did not share their node budget: {reprStr result}")
  match resolveProgramTypeAliasBodyWithBudgets environment use 16 32 body with
  | .ok type =>
      let pair := TypeSystem.Ty.product .word .word
      assertTrue (decide (type = TypeSystem.Ty.product pair pair))
        "branching alias normalization changed below its node budget"
  | .error error => throw (IO.userError
      s!"branching aliases exhausted a sufficient budget: {reprStr error}")

private def testDefaultEagerExpansionBudget : IO Unit := do
  let source ← parsed .main "default_fuel.solc" (String.intercalate "\n" [
    "type T0 = Word;",
    "type T1 = (T0, T0);",
    "type T2 = (T1, T1);",
    "type T3 = (T2, T2);",
    "type T4 = (T3, T3);",
    "type T5 = (T4, T4);",
    "type T6 = (T5, T5);",
    "type T7 = (T6, T6);",
    "type T8 = (T7, T7);",
    "type T9 = (T8, T8);",
    "type T10 = (T9, T9);",
    "type T11 = (T10, T10);",
    "type T12 = (T11, T11);",
    "type T13 = (T12, T12);"
  ])
  let environment ← build [source]
  let terminal ← declaration environment "default_fuel" "T13"
  match buildProgramSignatures environment with
  | .error [.typeResolution id .aliasExpansionLimit] =>
      assertTrue (decide (id = terminal.id))
        "default alias node-budget failure lost its declaration owner"
  | result => throw (IO.userError
      s!"default eager alias budget result changed: {reprStr result}")

private def testUnusedAliasValidation : IO Unit := do
  let source ← parsed .main "invalid_aliases.solc" (String.intercalate "\n" [
    "type Id(T) = T;",
    "type Duplicate(T, T) = T;",
    "type Missing = Absent;",
    "type WrongArity = Id;",
    "type TooMany = Id<Word, Bool>;",
    "type Direct = Direct;",
    "type Left = Right;",
    "type Right = Left;"
  ])
  let environment ← build [source]
  let duplicate ← declaration environment "invalid_aliases" "Duplicate"
  let missing ← declaration environment "invalid_aliases" "Missing"
  let wrongArity ← declaration environment "invalid_aliases" "WrongArity"
  let tooMany ← declaration environment "invalid_aliases" "TooMany"
  let direct ← declaration environment "invalid_aliases" "Direct"
  let left ← declaration environment "invalid_aliases" "Left"
  let right ← declaration environment "invalid_aliases" "Right"
  match buildProgramSignatures environment with
  | .error [
      .typeResolution duplicateId
        (.duplicateGenericParameter "T" 0 1),
      .typeResolution missingId (.unknownTypeName ["Absent"]),
      .typeResolution wrongArityId (.typeArityMismatch ["Id"] 1 0),
      .typeResolution tooManyId (.typeArityMismatch ["Id"] 1 2),
      .typeResolution directId (.cyclicTypeAlias directCycle),
      .typeResolution leftId (.cyclicTypeAlias leftCycle),
      .typeResolution rightId (.cyclicTypeAlias rightCycle)
    ] =>
      assertTrue (decide (
          duplicateId = duplicate.id ∧
          missingId = missing.id ∧
          wrongArityId = wrongArity.id ∧
          tooManyId = tooMany.id ∧
          directId = direct.id ∧
          leftId = left.id ∧
          rightId = right.id ∧
          directCycle = [direct.id, direct.id] ∧
          leftCycle = [left.id, right.id, left.id] ∧
          rightCycle = [right.id, left.id, right.id]))
        "unused alias diagnostics lost declaration order or cycle paths"
  | result => throw (IO.userError
      s!"unused alias validation result changed: {reprStr result}")

end ProgramTypeAliases

/-- Run transparent type-alias expansion and diagnostic regressions. -/
def testProgramTypeAliases : IO Unit := do
  ProgramTypeAliases.testTransparentSubstitution
  ProgramTypeAliases.testDefinitionSiteScope
  ProgramTypeAliases.testResolvedAliasPositions
  ProgramTypeAliases.testCycleDiagnostics
  ProgramTypeAliases.testExpansionBudget
  ProgramTypeAliases.testSharedNodeBudget
  ProgramTypeAliases.testDefaultEagerExpansionBudget
  ProgramTypeAliases.testUnusedAliasValidation

end Tests
