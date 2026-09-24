import Solcore.Profile

set_option autoImplicit false

namespace Solcore

inductive BaselineRole where
  | upstreamEvidence
  | comparisonImplementation
  | compatibilitySnapshot
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive SolverMode where
  | legacy
  | tabled
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ImplementationSettings where
  solver : SolverMode
  generatedDispatch : Bool
  primitiveSurface : EvmRevision
  bytecodeRuntime : EvmRevision
  nativeBackendTarget : Option EvmRevision
  externalYulCompilerTarget : Option EvmRevision
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ImplementationBaseline where
  implementation : String
  repository : String
  revision : String
  role : BaselineRole
  nativeSettings : ImplementationSettings
  notes : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

def haskellBaseline : ImplementationBaseline := {
  implementation := "solcore-haskell"
  repository := "https://github.com/argotorg/solcore"
  revision := "1d490d8bb5f374356f06e0720655496482eb1fb4"
  role := .upstreamEvidence
  nativeSettings := {
    solver := .legacy
    generatedDispatch := true
    primitiveSurface := .osaka
    bytecodeRuntime := .prague
    nativeBackendTarget := none
    externalYulCompilerTarget := none
  }
  notes := "Defaults are evidence only. The external Yul compiler target is not pinned."
}

def rustBaseline : ImplementationBaseline := {
  implementation := "solcore-rs"
  repository := "https://github.com/argotorg/solcore-rs"
  revision := "38f4778ea461edfe59106bdb1f9f08c3307b0fc0"
  role := .comparisonImplementation
  nativeSettings := {
    solver := .tabled
    generatedDispatch := true
    primitiveSurface := .osaka
    bytecodeRuntime := .osaka
    nativeBackendTarget := some .osaka
    externalYulCompilerTarget := none
  }
  notes := "The external Yul compiler target is not pinned."
}

def implementationBaselines : Array ImplementationBaseline :=
  #[haskellBaseline, rustBaseline]

end Solcore
