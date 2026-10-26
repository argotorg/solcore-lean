import Solcore.Synthesis.Source.ScalarRenderer

/-! Deterministic source emission for the initial differential-testing subset.
The input is checker-sealed Core. Source rendering is tested against the pinned
Rust frontend. `ScalarMeaning.emit_source_meaning` relates the emitted text to
the original Core result under an independent source semantics. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source

open Solcore.Synthesis.Core (CheckedWordProgram)

def emitterVersion : String := "solcore-source-g0-v1"
def wrapperVersion : String := "solcore-word-contract-v1"
def contractName : String := "SynthesizedG0"
def methodName : String := "run"
def methodSignature : String := "run()"
def deployPath : List String := ["SynthesizedG0Deploy"]
def runtimePath : List String := ["SynthesizedG0Deploy", "SynthesizedG0"]

/-- Emit a single zero-argument ABI method. Its uint256 wrapper exposes the
original Word as exactly 32 return bytes. Unsupported operations are errors,
including operations in a branch that is known to be untaken. -/
def emit (program : CheckedWordProgram) : Except EmitError EmittedProgram := do
  let body ← ScalarRenderer.render .word [] 8 0 program.program.body
  let lines := ["import * from std;", "import * from std.dispatch;", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "() public returns (uint256) {"] ++ body.lines ++
    ["        return uint256(" ++ body.value ++ ");", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source
