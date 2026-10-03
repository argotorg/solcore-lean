import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Consumers construct the independent canonical body judgment from the
actual specialization. They retain static validity and real invocation facts.
The runtime audit checks complete rewritten bodies and ordered solved rows. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationBodyFacts
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open RecursiveNamedSpecializationBodyFacts

section Formal
variable {program : CheckedProgram} {signature : ProgramFunctionSignature}
  {generic : CheckedFunction} {supplied : ParameterSubstitution}
  {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_independent_body :
    specialized.function.typedBody = StructuralSubstitution.applyTypedSource
      specialized.parameterSubstitution generic.typedBody := body accepted

theorem actual_ordered_ledger :
    specialized.function.solvedRequirements = generic.solvedRequirements.map
      (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution) := ledger accepted

theorem actual_inputs :
    specialized.function.typedBody.inputs = generic.typedBody.inputs.map
      (StructuralSubstitution.applyBinder specialized.parameterSubstitution) := by
  rw [body accepted]
  rfl

theorem actual_roots : specialized.function.typedBody.roots = generic.typedBody.roots := by
  rw [body accepted]
  rfl

theorem canonical_instantiated
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized)) :
    Dynamic.FunctionInstantiates (Program.ofChecked program)
      (CallableNamedMetadata.instantiation specialized) (bodyInstance program specialized) :=
  instantiated signatureMember genericMember accepted valid

theorem canonical_source_frame {function : Dynamic.Closure}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized))
    (source : function.source = specialized.function.typedBody)
    (context : function.context = (bodyInstance program specialized).context)
    (parameters : function.parameters = specialized.function.typedBody.inputs)
    (result : function.resultType = specialized.function.inferredBodyType)
    (captured : function.captured = [])
    (roots : Dynamic.StatementRoots specialized.function.typedBody.roots function.body)
    (covers : function.evidence.Covers (bodyInstance program specialized).context) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (bodyInstance program specialized) function :=
  source_frame signatureMember genericMember accepted valid source context parameters result captured roots covers
end Formal

theorem residual_context (program : CheckedProgram) (specialized : SourceSpecialization.SpecializedFunction) :
    (bodyInstance program specialized).context.residualTypeVariables = true := rfl

theorem wrong_declaration_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.id ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (identities accepted).1

theorem wrong_raw_body_owner_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : generic.typedBody.owner ≠ generic.declaration) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (identities accepted).2.1

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function local<T>(value: T) returns (T) { let copied = value; return copied; }",
  "function calc(value: Word) returns (Word) { let first = value + 1; let second = first + 2; return second; }",
  "function wordRoot() returns (Word) { return choose(7, true); }",
  "function boolRoot() returns (Bool) { return choose(false, 9); }",
  "function localRoot() returns (Word) { return local(11); }",
  "function calcRoot() returns (Word) { return calc(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named specialization body facts" content
    ["wordRoot", "boolRoot", "localRoot", "calcRoot"]
  let mut genericRows := 0
  let mut solvedRows := 0
  let mut reversedRequests := 0
  for specialized in compiled.indexed.base.plan.specializations do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == specialized.declaration) with
      | some value => pure value
      | none => throw (IO.userError "specialization body signature missing")
    let generic ← match compiled.sourceProgram.functions.find? (·.declaration == specialized.declaration) with
      | some value => pure value
      | none => throw (IO.userError "specialization body original checked function missing")
    let actual ← get "actual accepted body specialization"
      (SourceSpecialization.specializeFunction signature generic specialized.parameterSubstitution.reverse)
    require (reprStr actual == reprStr specialized) "specialization body complete canonical record changed"
    require (specialized.declaration == generic.declaration && signature.id == generic.declaration &&
      generic.typedBody.owner == generic.declaration) "specialization body actual declaration/owner changed"
    require (reprStr specialized.function.typedBody == reprStr
      (StructuralSubstitution.applyTypedSource specialized.parameterSubstitution generic.typedBody))
      "specialization body full independent source substitution changed"
    require (reprStr specialized.function.solvedRequirements == reprStr
      (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution)))
      "specialization body full ordered solved ledger changed"
    require (specialized.function.inferredBodyType == specialized.parameterSubstitution.apply generic.inferredBodyType)
      "specialization body independent result substitution changed"
    require (specialized.parameterSubstitution.map Prod.fst == signature.scheme.parameters)
      "specialization body original complete canonical domain changed"
    let instantiatedBody := bodyInstance compiled.sourceProgram specialized
    require (instantiatedBody.context.residualTypeVariables && instantiatedBody.context.typeParameters.isEmpty)
      "specialization body declaration context flags changed"
    require (reprStr instantiatedBody.source == reprStr specialized.function.typedBody &&
      reprStr instantiatedBody.context == reprStr (declarationContext compiled.sourceProgram.signatures generic.declaration []
        (signature.scheme.predicates.map (ProgramPredicate.applyParameters specialized.parameterSubstitution))
        (generic.solvedRequirements.map (StructuralSubstitution.applySolvedRequirement specialized.parameterSubstitution))))
      "specialization body full independent context/source changed"
    if !specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if specialized.parameterSubstitution.length == 2 then
      require (specialized.parameterSubstitution != specialized.parameterSubstitution.reverse)
        "specialization body reverse request lost distinct full domain order"
      reversedRequests := reversedRequests + 1
    solvedRows := solvedRows + specialized.function.solvedRequirements.length
  require (genericRows == 3 && reversedRequests == 2 && solvedRows ≥ 2)
    s!"specialization body fixture coverage changed {genericRows}/{reversedRequests}/{solvedRows}"
  IO.println "named specialization bodies: actual pass, canonical independent instantiation, full bodies and ordered solved ledgers GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationBodyFacts
