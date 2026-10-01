import Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternMetadata
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

/-! Actual compatible compiler consumers use general payloads and ambient
nominal definitions. The formal leaf results require only input representation,
not a matcher trace. Composite runtime fixtures retain raw constructor guards;
full composite matching and marked arm allocation are separate proof layers. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace Tests.SourceCoreCompatiblePatternProofs
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatiblePatternLeaves

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_pattern_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_pattern_proofs.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def functionType : TypeSystem.Ty := .function .word .word
private def mapType : TypeSystem.Ty := .mapping .word .word
private def types : List TypeSystem.Ty := [.word, .integer, functionType, .proxy .word, mapType]
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 30 types).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 30 types).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem valid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩ }
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "bound", .mono type, [], false, none⟩
private def pattern (type : TypeSystem.Ty) : TypedMatchPattern := {
  source := .group span (.binder span "bound"), type, resolution := .binder (binder type) }
private def fallback : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled (type : TypeSystem.Ty) : SourceCoreCompatibleDataMatches.CertifiedPattern compilation.definitions :=
  match SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span type (pattern type) with
  | .ok result => result | .error _ => fallback
private theorem functionAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    functionType (pattern functionType) = .ok (compiled functionType) := by cbv
private theorem mappingAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    mapType (pattern mapType) = .ok (compiled mapType) := by cbv
private theorem proxyAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    (.proxy .word) (pattern (.proxy .word)) = .ok (compiled (.proxy .word)) := by cbv
private theorem wordAccepted : SourceCoreCompatibleDataMatches.compilePattern compilation 10 source [] site span
    .word (pattern .word) = .ok (compiled .word) := by cbv
private theorem sourceMatches (type : TypeSystem.Ty) (value : Dynamic.Value) :
    Dynamic.PatternMatches context (pattern type) value [(binder type, value)] :=
  .intro (.group (.binder rfl)) .binder

/-- The actual compiler receipt certifies its matcher in the extended ambient
world, rather than substituting the base catalog's typing judgment. -/
example : CompatiblePatternCertificates.Certificate compilation source [] site span functionType
    (pattern functionType) (compiled functionType).pattern :=
  CompatiblePatternCertificates.certificate_of_compilePattern compilation 10 source [] site span functionType
    (pattern functionType) (compiled functionType) functionAccepted

/-- Binding a function retains its complete native identity, descriptor and
capture payload. The function model is unchanged by the pure matcher. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Value} {native : Core.Value}
    (represented : ValueRep checked registry functions mapping world functionType function native
      (compiled functionType).pattern.type) (environment : Environment) (store : Store) :
    ∃ bound, BindingsRep checked registry functions mapping world (compiled functionType).pattern.bindings
      [(binder functionType, function)] bound ∧
      Evaluates (native :: environment) store (.apply (compiled functionType).pattern.matcher (.var 0))
        (.inRight .unit (DataPatternValues.packValues bound)) store :=
  compilePattern_leaf_success_preserves compilation 10 source [] site span functionType (pattern functionType)
    (compiled functionType) functionAccepted context valid (.binder _) represented (sourceMatches _ _) environment store

/-- Ordered mappings, including their exact raw header, duplicates and
transported default, are bound without decoding or re-encoding. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native : Core.Value}
    (represented : ValueRep checked registry functions mapping world mapType sourceValue native
      (compiled mapType).pattern.type) (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep checked registry functions mapping world context (pattern mapType)
      (compiled mapType).pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply (compiled mapType).pattern.matcher (.var 0)) (native :: environment) store) = .done outcome store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply (compiled mapType).pattern.matcher (.var 0)) (native :: environment) store) = .done actual after →
        actual = outcome ∧ after = store) :=
  compilePattern_leaf_run_preserves compilation 10 source [] site span mapType (pattern mapType)
    (compiled mapType) mappingAccepted context valid (.binder _) represented environment store

/-- Reflection starts with completed Core execution and reconstructs source
meaning for an opaque proxy carrier. Native typing is not raw authenticity. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native outcome : Core.Value}
    (represented : ValueRep checked registry functions mapping world (.proxy .word) sourceValue native
      (compiled (.proxy .word)).pattern.type) {environment : Environment} {store after : Store}
    (completed : Evaluates (native :: environment) store
      (.apply (compiled (.proxy .word)).pattern.matcher (.var 0)) outcome after) :
    OutcomeRep checked registry functions mapping world context (pattern (.proxy .word))
      (compiled (.proxy .word)).pattern sourceValue outcome ∧ after = store :=
  compilePattern_leaf_reflects compilation 10 source [] site span (.proxy .word) (pattern (.proxy .word))
    (compiled (.proxy .word)) proxyAccepted context valid (.binder _) represented completed

private def noFunctions : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem wordRep (word : Word) : ValueRep checked values.registry noFunctions [] []
    .word (.word word) (.word word) (compiled .word).pattern.type := by
  change ValueRep checked values.registry noFunctions [] [] .word (.word word) (.word word) .word
  exact .word word
example (word : Word) (environment : Environment) (store : Store) :
    ∃ outcome, OutcomeRep checked values.registry noFunctions [] [] context (pattern .word)
      (compiled .word).pattern (.word word) outcome ∧
      Evaluates (.word word :: environment) store (.apply (compiled .word).pattern.matcher (.var 0)) outcome store :=
  compilePattern_leaf_preserves compilation 10 source [] site span .word (pattern .word) (compiled .word)
    wordAccepted context valid (.binder _) (wordRep word) environment store

/-- Exact retained metadata, including substitution order, follows from
independent runtime agreement only under authentic well-formed declarations. -/
example {left right : DataConstructorInstantiation} (catalogValid : SignatureCatalogWellFormed checked.signatures)
    (leftAuthentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures left = true)
    (rightAuthentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures right = true)
    (agrees : Dynamic.ConstructorInstantiationsAgree left right) : left = right :=
  CompatiblePatternMetadata.metadata_eq catalogValid leftAuthentic rightAuthentic agrees

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "enum Box<T> { Box(T) }",
    "function closure(marker: Word) returns (Word) { match (lam(x: Word) -> Word { marker = marker + x; return marker; }) { case f { let first: Word = f(2); return f(3); } } }",
    "function mapping(m: mapping(Word => Word)) returns (Word) { match (m) { case bound { return bound[7] + bound[9]; } } }",
    "function wildcard(m: mapping(Word => Word)) returns (Word) { match (m) { case _ { return 41; } } }",
    "function nested(tree: Tree) returns (Word) { match (tree) { case .Pair(.Leaf(left), .Leaf(0)) { return left; } case .Pair(.Leaf(left), .Leaf(right)) { return left + right; } default { return 99; } } }",
    "function numeric(value: Word) returns (Word) { match (value) { case 115792089237316195423570985008687907853269984665640564039457584007913129639936 { return 1; } case bound { return bound; } } }",
    "function failed(marker: Word) returns (Word) { match (marker) { case bound { marker = bound + 1; let absent: Word; return absent; } } }"]}] }

private def checkRawGuard (program : CheckedProgram) : IO Unit := do
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "Box signature missing")
  let boxType := TypeSystem.Ty.nominal box.id [.word]
  let stagedType := TypeSystem.Ty.nominal box.id [.comptime .word]
  let ordinary : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.word], [.word], boxType⟩
  let staged : DataConstructorInstantiation := ⟨⟨box.id, 0⟩, box.parameters.zip [.comptime .word], [.comptime .word], stagedType⟩
  let checked ← SourceCompilerFeatureSupport.get "raw pattern catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 100 [boxType, stagedType])
  let first ← SourceCompilerFeatureSupport.get "ordinary constructor input"
    (SourceCoreCompatibleValues.encode 100 (.initial checked) boxType (.constructed ordinary [.word (Word.ofNatModulo 7)]))
  let second ← SourceCompilerFeatureSupport.get "staged constructor input"
    (SourceCoreCompatibleValues.encode 100 first.context boxType (.constructed staged [.word (Word.ofNatModulo 7)]))
  let definitions := checked.catalog.definitions ++ [⟨[.unit]⟩]
  let compilation : SourceCoreCompatibleDataMatches.Context := ⟨second.context, [], none, some definitions⟩
  let sourcePattern : TypedMatchPattern := {
    source := .group span (.constructor span (some span) [] "Box" 1), type := boxType
    resolution := .constructor ordinary [.wildcard] }
  let compiled ← SourceCompilerFeatureSupport.get "actual compatible raw matcher"
    (SourceCoreCompatibleDataMatches.compilePattern compilation 20 source [] site span boxType sourcePattern)
  for (input, expected) in [(first.value, Core.Value.inRight .unit .unit),
      (second.value, .inLeft .unit .unit)] do
    let expression ← match SourceCoreCompatibleDataExpressions.quote input with
      | some expression => pure expression | none => throw (IO.userError "constructor was not quotable")
    let code := Core.Expr.apply compiled.pattern.matcher expression
    SourceCompilerFeatureSupport.require ((Core.Program.mk compiled.pattern.resultType code definitions).check)
      "actual ambient matcher failed native checking"
    let sentinel : Core.Store := [.integer 901, .cellRef .integer 0]
    match Core.runStateful 1000 (.initial code [] sentinel) with
    | .done actual after =>
      SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
        "raw constructor guard erased the staged instantiation or changed surrounding state"
    | _ => throw (IO.userError "raw constructor matcher failed to finish")
    for budget in [0, 2, 11] do
      match Core.runStateful budget (.initial code [] sentinel) with
      | .outOfFuel pending =>
        match Core.runStateful 1000 pending with
        | .done actual after =>
          SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
            "resumed raw constructor matcher changed outcome or state"
        | _ => throw (IO.userError "raw matcher checkpoint did not finish")
      | .done actual after =>
        SourceCompilerFeatureSupport.require (actual == expected && after == sentinel)
          "completed small-budget raw matcher changed outcome"
      | .fault _ _ => throw (IO.userError "raw matcher faulted")

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "compatible pattern checker" (checkProgram workspace)
  checkRawGuard program
  let w := Word.ofNatModulo
  let mapping : SourceCoreExecution.Value := .mapping .word .word
    [(.word (w 7), .word (w 13)), (.word (w 7), .word (w 90)), (.word (w 9), .word (w 29))]
  for (name, inputs, expected) in [
      ("closure", [.word (w 10)], (.word (w 15) : SourceCoreExecution.Value)),
      ("mapping", [mapping], .word (w 42)), ("wildcard", [mapping], .word (w 41)),
      ("numeric", [.word (w 0)], .word (w 1)), ("numeric", [.word (w 9)], .word (w 9))] do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == expected) "compatible leaf matcher changed result"
    for budget in [0, 7, 47] do entry.checkResume inputs expected budget
  let tree ← match program.signatures.dataTypes.find? (·.name == "Tree") with
    | some tree => pure tree | none => throw (IO.userError "Tree signature missing")
  let leafMetadata : DataConstructorInstantiation := ⟨⟨tree.id, 0⟩, [], [.word], .nominal tree.id []⟩
  let pairMetadata : DataConstructorInstantiation := ⟨⟨tree.id, 1⟩, [], [.nominal tree.id [], .nominal tree.id []], .nominal tree.id []⟩
  let leaf (value : Nat) : SourceCoreExecution.Value := .constructed leafMetadata [.word (w value)]
  let nested ← SourceCompilerFeatureSupport.compileNamed program "nested"
  for (argument, expected) in [(.constructed pairMetadata [leaf 11, leaf 0], (.word (w 11) : SourceCoreExecution.Value)),
      (.constructed pairMetadata [leaf 11, leaf 3], .word (w 14)), (leaf 8, .word (w 99))] do
    SourceCompilerFeatureSupport.require ((← nested.run [argument]) == expected) "nested compatible pattern changed ordered bindings"
    nested.checkResume [argument] expected
  let failed ← SourceCompilerFeatureSupport.compileNamed program "failed"
  match (← failed.invoke [.word (w 7)]).outcome with
  | .failed _ _ => pure ()
  | _ => throw (IO.userError "selected pattern arm lost its source fault")
  IO.println "compatible patterns: general leaf preservation/reflection, ordered bindings and ambient raw guards GREEN"
end Tests.SourceCoreCompatiblePatternProofs
