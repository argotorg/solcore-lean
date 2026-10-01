import Solcore.SourceSemantics.CoreLowering.CompatiblePatternDecision
import Solcore.Test.SourceCoreCompatiblePatternProofs

/-! Actual accepted nested tuple patterns bind whole function and mapping
carriers. Formal consumers preserve independent source binding order and
reflect completed Core alone, in an extended ambient nominal world. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace Tests.SourceCoreCompatibleCompositePatterns
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues CompatiblePayload CompatiblePatternLeaves
open SourceCoreCompatibleDataMatches CompatiblePatternDecision
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_composite_patterns", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "compatible_composite_patterns.solc"⟩, 0, 1⟩
private def site : StatementId := ⟨⟨owner, 0⟩⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := .ofSignatures signatures
private theorem signatureValid : SignatureCatalogWellFormed signatures := by
  constructor <;> simp [signatures, signatureDeclarationIds]
private def functionType : TypeSystem.Ty := .function .word .word
private def mapType : TypeSystem.Ty := .mapping .word .word
private def tupleType : TypeSystem.Ty := .product (.comptime functionType) (.product (.proxy .word) mapType)
private theorem checkExists : (SourceCoreCompatibleCatalog.prepare signatures 50 [tupleType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 50 [tupleType]).toOption.get checkExists
private def values := SourceCoreCompatibleValues.Context.initial checked
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [⟨[.unit]⟩]
private def compilation : SourceCoreCompatibleDataMatches.Context := ⟨values, [], none, some ambient.definitions⟩
private theorem valid : ContextValid compilation context := {
  signatures := rfl, ledger := rfl
  valid := ⟨by simp [RequirementIdsUnique, context, Context.ofSignatures],
    by intro requirement member; cases member⟩ }
private def functionBinder : TypedBinder := ⟨⟨owner, 0⟩, "f", .mono (.comptime functionType), [], false, none⟩
private def mappingBinder : TypedBinder := ⟨⟨owner, 1⟩, "m", .mono mapType, [], false, none⟩
private def pattern : TypedMatchPattern := {
  source := .group span (.group span (.tuple span 2)), type := tupleType
  resolution := .tuple [.binder functionBinder, .tuple 2, .wildcard, .binder mappingBinder] }
private def fallback : CertifiedPattern compilation.definitions := {
  pattern := ⟨.unit, [], [], .lambda .unit (.sum .unit .unit) (.inRight .unit .unit)⟩
  typed := .lambda .unit (.sum .unit .unit) (.inRight .unit .unit) }
private def compiled : CertifiedPattern compilation.definitions :=
  match compilePattern compilation 20 source [] site span tupleType pattern with
  | .ok result => result | .error _ => fallback
private theorem accepted : compilePattern compilation 20 source [] site span tupleType pattern = .ok compiled := by cbv
private theorem sourceMatches (function mappingValue : Dynamic.Value) :
    Dynamic.PatternMatches context pattern
      (.product function (.product (.proxy (.comptime .word)) mappingValue))
      [(functionBinder, function), (mappingBinder, mappingValue)] :=
  .intro (.group (.group .tuple))
    (.tuple (.cons (.singleton _)) rfl
      (.cons .binder (.cons (.tuple (.cons (.singleton _)) rfl (.cons .wildcard (.cons .binder .nil))) .nil)))

/-- Typed compiler receipts include both nested child trees, actual ambient
checking and the exact ordered binder pair. -/
example : CompatiblePatternCertificates.Certificate compilation source [] site span tupleType pattern compiled.pattern :=
  CompatiblePatternCertificates.certificate_of_compilePattern compilation 20 source [] site span tupleType pattern compiled accepted
example : compiled.pattern.bindings.map (·.1) = [functionBinder, mappingBinder] := by cbv

/-- Independent matching binds whole source functions and ordered mappings;
no child or matcher evaluation premise is present. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function mappingValue : Dynamic.Value} {native : Core.Value}
    (extended : SourceCoreRawMetadata.Extends values.registry registry)
    (represented : ValueRep checked registry functions mapping world tupleType
      (.product function (.product (.proxy (.comptime .word)) mappingValue)) native compiled.pattern.type)
    (environment : Environment) (store : Store) :
    ∃ bound, BindingsRep checked registry functions mapping world compiled.pattern.bindings
      [(functionBinder, function), (mappingBinder, mappingValue)] bound ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (native :: environment) store) =
          .done (.inRight .unit (packValues bound)) store) ∧
      (∀ fuel actual after, runStateful fuel
        (.initial (.apply compiled.pattern.matcher (.var 0)) (native :: environment) store) = .done actual after →
        actual = .inRight .unit (packValues bound) ∧ after = store) :=
  CompatiblePatternSuccess.compilePattern_success_run compilation 20 source [] site span tupleType pattern compiled accepted
    context rfl signatureValid extended represented (sourceMatches _ _) environment store

/-- Core completion alone reconstructs independent matching or non-matching,
including all nested bindings, with exactly the surrounding state. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceValue : Dynamic.Value} {native actual : Core.Value}
    (extended : SourceCoreRawMetadata.Extends values.registry registry)
    (represented : ValueRep checked registry functions mapping world tupleType sourceValue native compiled.pattern.type)
    {environment : Environment} {store after : Store}
    (completed : Evaluates (native :: environment) store (.apply compiled.pattern.matcher (.var 0)) actual after) :
    OutcomeRep checked registry functions mapping world context pattern compiled.pattern sourceValue actual ∧ after = store :=
  compilePattern_reflects compilation 20 source [] site span tupleType pattern compiled accepted context valid signatureValid
    extended represented completed

/-- Source runtime views decide tuple shape despite native function products.
A singleton unpack keeps the full native function carrier. -/
example {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked registry functions mapping world functionType function native type) :
    ∃ sources natives types, ValuesRep checked registry functions mapping world [functionType] sources natives types ∧
      Dynamic.ValuesPack sources function ∧ native = packValues natives ∧ type = SourceCoreCompatibleCatalog.packTypes types :=
  CompatiblePatternValues.unpack (count := 1) rfl represented

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function nested(marker: Word, m: mapping(Word => Word)) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, (0, m))) { case (f, (0, bound)) { let ignored: Word = f(bound[7]); return f(bound[9]); } default { return 99; } } }",
    "function miss(marker: Word, m: mapping(Word => Word)) returns (Word) { match ((lam(x: Word) -> Word { marker = marker + x; return marker; }, (1, m))) { case (f, (0, bound)) { return f(bound[7]); } default { return marker; } } }",
    "function constructed(marker: Word, m: mapping(Word => Word)) returns (Word) { match (Box((lam(x: Word) -> Word { marker = marker + x; return marker; }, m))) { case .Box((f, bound)) { let ignored: Word = f(bound[7]); return f(bound[9]); } } }"]}] }

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "general composite pattern source"
    (checkProgram workspace)
  let w := Word.ofNatModulo
  let mapping : SourceCoreExecution.Value := .mapping .word .word
    [(.word (w 7), .word (w 13)), (.word (w 7), .word (w 900)), (.word (w 9), .word (w 29))]
  for (name, expected) in [("nested", 52), ("constructed", 52), ("miss", 10)] do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    let inputs : List SourceCoreExecution.Value := [.word (w 10), mapping]
    SourceCompilerFeatureSupport.require ((← entry.run inputs) == .word (w expected))
      "nested function/mapping matcher changed ordered bindings or shared captures"
    for budget in [0, 7, 43] do entry.checkResume inputs (.word (w expected)) budget
  IO.println "compatible composite patterns: recursive typed receipts, general payloads, raw guards and finite source/Core correspondence GREEN"
end Tests.SourceCoreCompatibleCompositePatterns
