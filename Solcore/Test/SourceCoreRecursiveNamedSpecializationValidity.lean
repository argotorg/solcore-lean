import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Canonical validity consumers retain independent formation of every raw
replacement. Accepted specialization supplies the domain and all redundant
metadata, including staging flags. Ground unused nominal rows remain a
separate catalog-formation boundary. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedSpecializationValidity
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering TypeSystem
open RecursiveNamedSpecializationValidity

section Formal
variable {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)

include accepted

theorem actual_guards : signature.scheme.body = generic.type ∧
    signature.parameterComptime = generic.typedBody.inputs.map (·.comptime) ∧
    signature.returnComptime = generic.returnComptime := guards accepted

theorem actual_exact (unique : signature.scheme.parameters.Nodup) :
    SourceSemantics.ParameterSubstitution.Exact specialized.parameterSubstitution signature.scheme.parameters :=
  exact accepted unique

theorem actual_valid {context : SourceSemantics.Context}
    (member : signature ∈ context.signatures.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed context specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid context (CallableNamedMetadata.instantiation specialized) :=
  canonical_valid accepted member unique range

theorem actual_program_valid {program : CheckedProgram}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (member : signature ∈ program.signatures.functions)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation specialized) :=
  valid_of_program wellFormed member accepted range

theorem actual_body {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  instantiated signatureMember genericMember accepted unique range

theorem actual_retained_body {program : CheckedProgram}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (unique : signature.scheme.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) specialized.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program specialized) :=
  retained_instantiated signatureMember genericMember accepted unique range
end Formal

section Prepared
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {named : SourceCoreGeneralFunctions.Function}
  {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
  (signatureMember : signature ∈ program.signatures.functions)
  (genericMember : generic ∈ program.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
  (unique : signature.scheme.parameters.Nodup)
  (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (Context.ofSignatures program.signatures) named.specialized.parameterSubstitution)
  (closed : named.specialized.assumptions = [])
  (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

include signatureMember genericMember accepted unique range closed inputs compiled

theorem actual_prepared_frame :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  of_compilation signatureMember genericMember accepted unique range closed inputs compiled

theorem actual_prepared_retained_frame :
    CompatibleNamedBody.NamedAgreement named
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance program named.specialized)
      (RecursiveNamedPreparedSourceFrames.view program named compiled.statements) :=
  retained_of_compilation signatureMember genericMember accepted unique range closed inputs compiled
end Prepared

theorem wrong_type_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.scheme.body ≠ generic.type) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).1

theorem wrong_parameter_flags_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.parameterComptime ≠ generic.typedBody.inputs.map (·.comptime)) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).2.1

theorem wrong_return_flag_rejected {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
    (different : signature.returnComptime ≠ generic.returnComptime) :
    SourceSpecialization.specializeFunction signature generic supplied ≠ .ok specialized := by
  intro accepted
  exact different (guards accepted).2.2

/-- A raw unused replacement is ground and does not change Word, yet its
missing nominal declaration prevents formation of the complete range. -/
theorem unused_nominal_boundary (owner : Resolved.DeclarationId) (parameter : TypeParameterId) :
    SourceSpecialization.firstNonConcrete (.constructor (.declaration owner)) = none ∧
      TypeSystem.ParameterSubstitution.apply [(parameter, .constructor (.declaration owner))] .word = .word ∧
      ¬ SourceSemantics.ParameterSubstitution.RangeWellFormed
        (Context.ofSignatures ⟨[], [], [], [], [], []⟩) [(parameter, .constructor (.declaration owner))] := by
  refine ⟨rfl, rfl, ?_⟩
  intro range
  have scopeProof := (range parameter (.constructor (.declaration owner)) (by simp)).typeWellScoped
  generalize typeEq : Ty.constructor (TypeConstructorId.declaration owner) = type at scopeProof
  cases scopeProof <;> simp_all [Context.ofSignatures]

private def content : String := String.intercalate "\n" [
  "function choose<A, B>(first: A, second: B) returns (A) { let saved = first; return saved; }",
  "function staged<T>(comptime value: T) returns (comptime<T>) { return value; }",
  "function unused<T>() returns (Word) { let value: Word = 3; return value; }",
  "function wordRoot() returns (Word) { return choose(9, false); }",
  "function boolRoot() returns (Bool) { return choose(true, 8); }",
  "function stagedRoot() returns (comptime<Word>) { return staged(5); }"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named specialization validity" content
    ["wordRoot", "boolRoot", "stagedRoot"]
  let mut rows := 0
  let mut genericRows := 0
  let mut stagedRows := 0
  for specialized in compiled.indexed.base.plan.specializations do
    let signature ← match compiled.sourceProgram.signatures.functions.find? (·.id == specialized.declaration) with
      | some signature => pure signature
      | none => throw (IO.userError "specialization validity signature missing")
    let original ← match compiled.sourceProgram.functions.find? (·.declaration == specialized.declaration) with
      | some original => pure original
      | none => throw (IO.userError "specialization validity checked body missing")
    let actual ← get "specialization validity actual reversed request"
      (SourceSpecialization.specializeFunction signature original specialized.parameterSubstitution.reverse)
    require (reprStr actual == reprStr specialized) "specialization validity full actual result changed"
    let instantiation := CallableNamedMetadata.instantiation specialized
    require (signature.scheme.body == original.type &&
      signature.parameterComptime == original.typedBody.inputs.map (·.comptime) &&
      signature.returnComptime == original.returnComptime) "specialization validity guard outputs changed"
    require (instantiation.declaration == signature.id &&
      instantiation.parameterSubstitution.map Prod.fst == signature.scheme.parameters &&
      decide signature.scheme.parameters.Nodup) "specialization validity complete canonical domain changed"
    require (instantiation.type == specialized.parameterSubstitution.apply signature.scheme.body &&
      reprStr instantiation.predicates == reprStr (signature.scheme.predicates.map
        (ProgramPredicate.applyParameters specialized.parameterSubstitution)) &&
      instantiation.parameterComptime == signature.parameterComptime &&
      instantiation.returnComptime == signature.returnComptime) "specialization validity full raw metadata changed"
    if !specialized.parameterSubstitution.isEmpty then genericRows := genericRows + 1
    if instantiation.returnComptime then stagedRows := stagedRows + 1
    rows := rows + 1
  require (rows == 6 && genericRows == 3 && stagedRows == 2)
    s!"specialization validity coverage changed {rows}/{genericRows}/{stagedRows}"
  let signature ← match compiled.sourceProgram.signatures.functions.find? (·.name == "unused") with
    | some signature => pure signature
    | none => throw (IO.userError "unused specialization signature missing")
  let original ← match compiled.sourceProgram.functions.find? (·.declaration == signature.id) with
    | some original => pure original
    | none => throw (IO.userError "unused specialization body missing")
  let parameter ← match signature.scheme.parameters with
    | [parameter] => pure parameter
    | _ => throw (IO.userError "unused specialization parameter coverage changed")
  let foreign := {signature.id with declarationIndex := 1000000}
  require (!(compiled.sourceProgram.signatures.dataTypes.any (·.id == foreign)) &&
    !(compiled.sourceProgram.signatures.contracts.any (·.id == foreign))) "unused nominal unexpectedly cataloged"
  let raw : TypeSystem.Ty := .constructor (.declaration foreign)
  require (SourceSpecialization.firstNonConcrete raw == none) "unused nominal should be syntactically ground"
  let phantom ← get "actual accepted unused foreign nominal specialization"
    (SourceSpecialization.specializeFunction signature original [(parameter, raw)])
  require (phantom.parameterSubstitution == [(parameter, raw)] && phantom.function.type == original.type &&
    reprStr phantom.function.typedBody == reprStr original.typedBody &&
    reprStr phantom.function.solvedRequirements == reprStr original.solvedRequirements)
    "unused full raw range was dropped or unexpectedly changed the source body"
  match SourceSpecialization.specializeFunction
      {signature with scheme := {signature.scheme with body := .bool}} original [(parameter, raw)] with
    | .error (.signatureTypeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong original signature type passed specialization")
  match SourceSpecialization.specializeFunction
      {signature with parameters := [⟨"extra", .word, true⟩]} original [(parameter, raw)] with
    | .error (.parameterComptimeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong parameter staging flags passed specialization")
  match SourceSpecialization.specializeFunction
      {signature with returnComptime := !signature.returnComptime} original [(parameter, raw)] with
    | .error (.returnComptimeMismatch _ _) => pure ()
    | _ => throw (IO.userError "wrong result staging flag passed specialization")
  IO.println "named specialization validity: actual guards/full canonical metadata, staging, unused foreign nominal boundary GREEN"

end Tests.SourceCoreRecursiveNamedSpecializationValidity
