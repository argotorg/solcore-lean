import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation

/-! Genuine map/world extensions carry the complete selected association from
the callee post to the argument post. Native payload, Code, binder/result row,
Support, SourceOrigin, captured Globals and body Syntax remain the same.
This static transport supplies no current caller rows or Source heap typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Only real map/world extensions change the representation indices.
The full same captured provenance is retained beside its unchanged payload. -/
theorem Association.extend
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Association headers keys registry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex typed escaped syntaxTree =>
    exact .ordinary owner (captured.extend maps worlds) code history support sourceOrigin
      prefixContext observed referenceIndex (typed.weaken worlds) escaped syntaxTree
  | principal owner captured code history support sourceOrigin observed leading referenceIndex typed escaped syntaxTree =>
    exact .principal owner (captured.extend maps worlds) code history support sourceOrigin
      observed leading referenceIndex (typed.weaken worlds) escaped syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
