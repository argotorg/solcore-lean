import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
import Solcore.Test.SourceCompilerFeatureSupport
import Solcore.Frontend.ProgramChecking

/-! The checker and specialization factory keep distinct ordered ledgers.
The actual two-parameter reference fixture requires the retained record, while
its compiler selection still matches the complete specialization metadata. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableNamedCanonicalOrder
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering TypeSystem
open CallableNamedCanonicalOrder

/-- Actual factory success and exact selector receipts suffice; no full metadata
equality or identical domain-order assumption is supplied by this consumer. -/
theorem retained_of_selected {signature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    (produced : SourceSpecialization.specializeFunction signature function supplied = .ok specialized)
    (unique : signature.scheme.parameters.Nodup) (next : Nat) (final : Substitution) (caller : ParameterSubstitution)
    (selected : SourceCompilationPlan.exactInstantiationKey plan (inferredInstantiation signature next final caller) = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized) :
    inferredInstantiation signature next final caller = retainedInstantiation specialized :=
  (CallableNamedMetadata.matches_of_exact selected record).retained_of_specialization produced unique next final caller

/-- The actual fresh allocator reverses two distinct declared parameters. -/
theorem two_parameter_order (scheme : ConstrainedDeclarationScheme) (first second : TypeParameterId)
    (parameters : scheme.parameters = [first, second]) (different : first ≠ second) (next : Nat) :
    (scheme.instantiate next).parameterSubstitution.map Prod.fst = [second, first] := by
  have unique : scheme.parameters.Nodup := by rw [parameters]; simp [different]
  simpa only [parameters, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using
    ConstrainedDeclarationScheme.instantiate_parameterSubstitution_domain_reverse scheme next unique

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
    "function pairRef() returns (function(Word, Bool) returns (Word)) { return pair; }",
    "function callPair(a: Word, b: Bool) returns (Word) { return pair(a, b); }"]}]}

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "retained order checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "pair") with
    | some signature => pure signature | none => throw (IO.userError "missing generic pair signature")
  let referenceSignature ← match program.signatures.functions.find? (·.name == "pairRef") with
    | some signature => pure signature | none => throw (IO.userError "missing pair reference signature")
  let checked ← match program.functions.find? (fun function => function.declaration == referenceSignature.id) with
    | some function => pure function | none => throw (IO.userError "missing checked pair reference")
  let metadata ← match checked.typedBody.nodes.findSome? fun
    | .expression {form := .reference _ (.declaration metadata), ..} =>
        if metadata.declaration == signature.id then some metadata else none
    | _ => none with
    | some metadata => pure metadata | none => throw (IO.userError "missing retained generic reference")
  let entry ← SourceCompilerFeatureSupport.compileNamed program "pairRef"
  let selected ← SourceCompilerFeatureSupport.get "actual retained target" (SourceCompilationPlan.exactInstantiationKey entry.compiled.plan metadata)
  let record ← SourceCompilerFeatureSupport.get "actual specialization record" (SourceCompilationPlan.exactSpecialization entry.compiled.plan selected)
  SourceCompilerFeatureSupport.require (signature.scheme.parameters.length == 2) "fixture lost two declared parameters"
  SourceCompilerFeatureSupport.require (decide (metadata.parameterSubstitution.map Prod.fst = signature.scheme.parameters.reverse))
    "inference did not retain reverse declaration order"
  SourceCompilerFeatureSupport.require (decide (record.parameterSubstitution.map Prod.fst = signature.scheme.parameters))
    "specialization did not record declaration order"
  SourceCompilerFeatureSupport.require (decide (metadata = retainedInstantiation record))
    "retained record changed a metadata field beyond the authenticated ledger order"
  SourceCompilerFeatureSupport.require (decide (metadata ≠ CallableNamedMetadata.instantiation record))
    "source ledgers were silently identified by key selection"
  match ← entry.run [] with
  | .function _ => pure ()
  | _ => throw (IO.userError "retained reference did not return an owned function")
  let call ← SourceCompilerFeatureSupport.compileNamed program "callPair"
  let value : SourceCoreExecution.Value := .word (Word.ofNatModulo 37)
  SourceCompilerFeatureSupport.require ((← call.run [value, .bool true]) == value) "two-parameter direct call changed result"
  call.checkResume [value, .bool true] value
  IO.println "named canonical order: actual reverse source ledger, forward factory ledger and full metadata correspondence GREEN"
end Tests.SourceCoreCallableNamedCanonicalOrder
