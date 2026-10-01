import Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameterIndexed
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.SourceSemantics.CoreLowering.CompatibleNamedParameters.Entry.mk
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Real marked parameter prefixes retain source-order cells, raw metadata and
function payloads, then enter the fixed-context body. Each invocation below
uses cached common compiler code and genuine native checkpoint resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleNamedParameters
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleNamedParameters CallableIndexedParameterCertificates CallableIndexedParameterMeaning

/-- The zero-input case remains the actual parameter compiler's empty tree. -/
example (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (type : Ty) (body : Expr) :
    Tree layouts owner [] layout globals onError source 0 type body [] 0 [] body :=
  CallableIndexedParameterCertificates.of_accepted (bindings := []) onError rfl

/-- Packing two equal closure payloads preserves their native aliasing. The
representation premise is typed, with no first-order payload restriction. -/
example {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
    {registry : SourceCoreRawMetadata.Registry} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    (left right : TypedBinder) (type : Ty) (sourceValue : Dynamic.Value) (value : Value)
    (first : CompatiblePayload.ValueRep values.checked registry functions mapping world left.scheme.body sourceValue value type)
    (second : CompatiblePayload.ValueRep values.checked registry functions mapping world right.scheme.body sourceValue value type) :
    RuntimeValueHasType world (.pair value value) (.product type type) ambient.definitions := by
  have represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world [(left, type), (right, type)] [sourceValue, sourceValue] [value, value] := .cons first (.cons second .nil)
  exact CallableIndexedParameters.Arguments.pack_typed represented

private def content : String := String.intercalate "\n" [
  "function unitAfterTwo(flag: Bool, value: Word) { }",
  "function readSecond(flag: Bool, value: Word) returns (Word) { flag; return value; }",
  "function paired(value: Word, flag: Bool) returns ((Word, Bool)) { return (value, flag); }",
  "function early(value: Word, flag: Bool) returns (Word) { return value; flag; }",
  "function identity(value: Word) returns (Word) { return value; }",
  "function keepFunction(f: function(Word) returns (Word), flag: Bool) returns (function(Word) returns (Word)) { flag; return f; }",
  "function keepMap(values: mapping(Word => Word)) returns (mapping(Word => Word)) { return values; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (expected : SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 19, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
    let result ← SourceCoreUnifiedCorpusSupport.get "parameter body resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
    match result.observation with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"named parameter result changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (final.heap.length == initial.heap.length + arguments.length)
        s!"parameter cell count changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
        s!"inert source prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (reprStr ((final.heap.drop initial.heap.length).map (·.value)) == reprStr (arguments.map some))
        s!"parameter order, payload or sharing changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue
        (final.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
        s!"parameter heap is not deeply safe {name}"
    | other => throw (IO.userError s!"named parameter body failed {name}: {reprStr other}")

def run : IO Unit := do
  let names := ["unitAfterTwo", "readSecond", "paired", "early", "identity", "keepFunction", "keepMap"]
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "certified named parameters" content names
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩,
    ⟨.word, some (.word (SourceCoreUnifiedCorpusSupport.word 777))⟩]}
  let value : SourceTypedRuntime.Value := .word (SourceCoreUnifiedCorpusSupport.word 42)
  check compiled "unitAfterTwo" [.bool false, value] .unit initial
  check compiled "readSecond" [.bool false, value] value initial
  check compiled "paired" [value, .bool false] (.product value (.bool false)) initial
  check compiled "early" [value, .bool false] value initial
  check compiled "identity" [value] value initial
  let identity ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let callable : SourceTypedRuntime.Value := .global identity []
  check compiled "keepFunction" [callable, .bool false] callable initial
  let mapping : SourceTypedRuntime.Value := .mapping (.comptime .word) .word
    [(.word (SourceCoreUnifiedCorpusSupport.word 3), value),
     (.word (SourceCoreUnifiedCorpusSupport.word 3), .word (SourceCoreUnifiedCorpusSupport.word 9))]
  check compiled "keepMap" [mapping] mapping initial
  IO.println "compatible named parameters: Unit, ordered cells, raw mapping, callable payload, prefix and resume GREEN"

end Tests.SourceCoreCompatibleNamedParameters
