import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.LeafDecoded.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.decodeWithRaw

/-! Function-leaf delegation traverses actual native tuples, nominal payloads
and ordered mappings. Failure paths and the ordinary named/builtin receipt are
retained. This unit does not reconstruct anonymous source closures. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleOutputLeaves
open Solcore Solcore.Frontend SourceInference
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(Word, function(Word) returns (Word)) }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function plain() returns (Word, Bool) { return (7, true); }",
    "function tuple() returns (function(Word) returns (Word), function(Word) returns (integer)) { return (inc, wordToInteger); }",
    "function nominal() returns (Holder) { return .Hold(7, inc); }",
    "function mappingReturn(value: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return value; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩
  | none => throw (IO.userError s!"leaf traversal function missing: {name}")

private structure Projected (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"leaf traversal source rejected: {reprStr error}")
  let requests := program.signatures.functions.map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 200 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"leaf traversal plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"leaf traversal base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"leaf traversal compiler failed: {reprStr error}")
  let recipe ← match SourceCoreCompatibleOutputs.prepareAncestry prepared with
    | .ok recipe => pure recipe
    | .error error => throw (IO.userError s!"leaf traversal recipe failed: {reprStr error}")
  let inc ← key program "inc"
  let mapping : SourceValue := .mapping .word (.comptime (.function .word .word))
    [(.word (Core.Word.ofNatModulo 4), .global inc []), (.word (Core.Word.ofNatModulo 4), .global inc [])]
  let fixtures : List (String × List SourceValue × Option (List SourceCoreCompatibleOutputs.PathStep)) :=
    [("plain", [], none), ("tuple", [], some [.productLeft]),
     ("nominal", [], some [.constructorPayload 1]),
     ("mappingReturn", [mapping], some [.mappingValue 0])]
  for (name, arguments, expectedFailure) in fixtures do
    for budget in [0, 29, 100000] do
      let completion ← match prepared.runSource (← key program name) arguments budget with
        | .ok completion => pure (completion.resume 100000)
        | .error error => throw (IO.userError s!"leaf traversal native call failed: {reprStr error}")
      let projected ← match same : automatic.checked.catalog.project completion.entry.sourceResultType with
        | .error error => throw (IO.userError s!"leaf traversal projection failed: {reprStr error}")
        | .ok type =>
          if equal : type = completion.entry.native.resultType then
            pure (show Projected automatic.checked completion.entry.sourceResultType
              completion.entry.native.resultType from ⟨by simpa [equal] using same⟩)
          else throw (IO.userError "leaf traversal result native type changed")
      let ordinary ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType projected.eq completion.result.native with
        | .ok ordinary => pure ordinary
        | .error error => throw (IO.userError s!"leaf traversal ordinary decoder failed: {reprStr error}")
      let delegated ← match SourceCoreCompatibleOutputs.decodeWithLeaves
          (SourceCoreCompatibleOutputs.decodeCallable recipe) recipe ordinary.snapshot completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType ordinary.core ordinary.decoded.type
          ordinary.decoded.projected ordinary.decoded.typed with
        | .ok delegated => pure delegated
        | .error error => throw (IO.userError s!"leaf traversal delegated decoder failed: {reprStr error}")
      assertTrue (reprStr delegated.source == reprStr ordinary.decoded.source)
        "delegating callable leaves changed deep raw source data"
      assertTrue (reprStr delegated.default.source == reprStr ordinary.decoded.source)
        "delegating callable leaves lost the original decoder receipt"
      let rejecting : SourceCoreCompatibleOutputs.LeafDecoder :=
        fun _ _ => .error ⟨[], .callablePayloadMismatch⟩
      match SourceCoreCompatibleOutputs.decodeWithLeaves rejecting recipe ordinary.snapshot completion.result.context
          completion.result.contextOwner completion.entry.sourceResultType ordinary.core ordinary.decoded.type
          ordinary.decoded.projected ordinary.decoded.typed with
      | .ok value =>
        assertTrue expectedFailure.isNone "structural decoder skipped a function leaf"
        assertTrue (reprStr value.source == reprStr ordinary.decoded.source)
          "data-only traversal depended on the function-leaf policy"
      | .error error =>
        let leafFailure := match error.code with | .callablePayloadMismatch => true | _ => false
        assertTrue (expectedFailure == some error.path && leafFailure)
          s!"structural function-leaf failure path changed: {reprStr error}"
  IO.println "actual output traversal, callable-leaf delegation and deep failure paths GREEN"

end Tests.SourceCoreCompatibleOutputLeaves
