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
  standardLibraryBundle : String
  nativeSettings : ImplementationSettings
  notes : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

def haskellBaseline : ImplementationBaseline := {
  implementation := "solcore-haskell"
  repository := "https://github.com/argotorg/solcore"
  revision := "1d490d8bb5f374356f06e0720655496482eb1fb4"
  role := .upstreamEvidence
  standardLibraryBundle := "canonical-haskell-1d490d8"
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
  standardLibraryBundle := "rust-compatibility-ac6f8957"
  nativeSettings := {
    solver := .tabled
    generatedDispatch := true
    primitiveSurface := .osaka
    bytecodeRuntime := .osaka
    nativeBackendTarget := some .osaka
    externalYulCompilerTarget := none
  }
  notes := "The vendored std is older, and the external Yul compiler target is not pinned."
}

def rustStdCompatibilitySnapshot : StdBundle := {
  sourceRevision := "ac6f8957a78dc53248dbe053f1ddbc2a2201b81f"
  manifestAlgorithm := "solcore-fileset-sha256-v1"
  manifestSha256 := "c23c43897bb3f9e8d55abc5369dc9bb1ae984e9da1ef9457440aee642923f430"
  files := #[
    {
      path := "ABIGeneric.solc"
      byteSize := 4945
      sha256 := "e1c7ad2e46de60c0c185d6476c8463aafa9652bc968abeebdd65c9b0f06bf347"
    },
    {
      path := "Generic.solc"
      byteSize := 445
      sha256 := "913a02e32829e0230e31db6512151c36e019f5630e3dbd0be9d033a9019194d7"
    },
    {
      path := "dispatch.solc"
      byteSize := 10016
      sha256 := "94db411afe24ca0d109a894e4f0fd9057220e7797c4597f4155c4fd4fe0c1860"
    },
    {
      path := "opcodes.solc"
      byteSize := 10377
      sha256 := "a6a08beed16ccdf722f65c60af835dcfd0eaec61f34f041082bbc0fca1e69bab"
    },
    {
      path := "std.solc"
      byteSize := 62719
      sha256 := "5ac06de3325625a1e88aa92e668d87b5b91c087a1f68603a04f220bb2e6824b6"
    }
  ]
}

def implementationBaselines : Array ImplementationBaseline :=
  #[haskellBaseline, rustBaseline]

end Solcore
