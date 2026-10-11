import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! The actual named compiler recipe supplies the callback and body used by
selected recursive caller support. The remaining inputs concern the original
Source, its static policy and the actual reached calls. The chosen recipe and
terminal packet remain fixed throughout certificate construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerFactories
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories
  (OriginalConditions NamedAuthority NamedReady)
open CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes (Recipe)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}

/-- The actual compiler supplies a recipe for this exact terminal packet. -/
theorem recipe (packet : Terminal header) : Nonempty (Recipe header packet) :=
  CallableIndexedOwnedPreparedStagedSelectedNamedCompilerRecipes.of_terminal packet

/-- Source admission remains independent of compilation. Every actual
selected child retains its own registry scope, evidence and parameter context. -/
structure Conditions {packet : Terminal header} (recipe : Recipe header packet)
    (stages : Staging.Recursive.Registry)
    (semanticFaults : FunctionCalls.FaultRep) where
  readFuel : Nat
  profile : PolicyFor recipe.policy
    (CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named) readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    header.reasonAt
  tree : Syntax header.function.source packet.expression
  original : ∀ child, stages.Closure header.function child →
    OriginalConditions compiled recipe.policy
      (CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named) readFuel
      header.context child header.reasonAt
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) semanticFaults

variable {packet : Terminal header} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}
  (selected : Recipe header packet)

/-- The actual compiler, its real child fuel and its cached specialization
construct all callback fields. No compiler-action equality is an input. -/
def authority (conditions : Conditions selected stages semanticFaults) :
    NamedAuthority header packet (stages := stages) (semanticFaults := semanticFaults) :=
  { policy := selected.policy
    body := selected.body
    compilation := CallableIndexedNamedGeneration.context compiled.indexed packet.prepared.named
    compilerFuel := packet.receipt.childFuel
    readFuel := conditions.readFuel
    native := compiled.indexed.base.callableContext
    active := []
    callables := selected.callables
    callback := selected.callback
    profile := conditions.profile
    tree := conditions.tree
    conditions := conditions.original }

/-- Call readiness refers to the certificate issued from this same compiler
recipe, rather than a freely chosen certificate or a body execution law. -/
def Ready (conditions : Conditions selected stages semanticFaults) : Prop :=
  NamedReady (authority selected conditions)

/-- Original typing and the actual accepted compiler action produce each
selected root internally, with the complete reached-call authority retained. -/
def support (conditions : Conditions selected stages semanticFaults)
    (ready : Ready selected conditions) :
    CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport header stages
      (CallableIndexedOwnedPreparedStagedSelectedTerminalCertificates.named header packet)
      semanticFaults :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.named_support
    (authority selected conditions) ready

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedNamedCompilerFactories
