import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedRetainedSubstitutionFacts

/-! Ordinary named invocation views come from actual compiled roots and input
preparation. Their empty lexical capture and dictionary are defined at source
entry; source instantiation still requires independent full metadata validity.
No native execution or runtime authority is used to construct the view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
open Frontend SourceInference TypeSystem
open RecursiveNamedSpecializationBodyFacts

private theorem roots_of_map {source : TypedSource} {statements : List StatementId}
    (accepted : source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
      | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)) = .ok statements) :
    Dynamic.StatementRoots source.roots statements := by
  generalize source.roots = roots at accepted ⊢
  induction roots generalizing statements with
  | nil => cases accepted; exact .nil
  | cons head rest ih =>
    cases head with
    | expression id => cases accepted
    | statement id =>
      simp only [List.mapM_cons, pure, Except.pure, bind, Except.bind] at accepted
      cases lowered : List.mapM (fun x => match x with
        | .statement id => Except.ok id
        | .expression id => throw (SourceCoreGeneralFunctions.Error.expectedStatementRoot id)) rest with
      | error error => simp only [lowered] at accepted; cases accepted
      | ok tail =>
        simp only [lowered] at accepted
        cases accepted
        exact .cons (ih lowered)

/-- The proof view starts a global body from its actual source declaration,
full solved ledger, empty lexical capture and empty ordinary dictionary. -/
def view (program : CheckedProgram) (named : SourceCoreGeneralFunctions.Function)
    (statements : List StatementId) : Dynamic.Closure where
  parameters := named.specialized.function.typedBody.inputs
  resultType := named.specialized.function.inferredBodyType
  body := statements
  source := named.specialized.function.typedBody
  captured := []
  context := (bodyInstance program named.specialized).context
  evidence := []

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}

theorem compiled_roots
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    Dynamic.StatementRoots named.specialized.function.typedBody.roots compiled.statements :=
  roots_of_map compiled.roots

private theorem roots_eq {roots : List NodeId} {statements : List StatementId}
    (extracted : Dynamic.StatementRoots roots statements) : roots = statements.map NodeId.statement := by
  induction extracted with
  | nil => rfl
  | cons _ ih => exact congrArg (List.cons _) ih

theorem compiled_roots_eq
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    named.specialized.function.typedBody.roots = compiled.statements.map NodeId.statement := by
  exact roots_eq (compiled_roots compiled)

theorem empty_covers {program : CheckedProgram}
    (closed : named.specialized.assumptions = []) :
    Dynamic.EvidenceEnvironment.Covers (bodyInstance program named.specialized).context [] := by
  constructor
  · intro goal evidence found
    cases found
  · intro predicate member
    change predicate ∈ named.specialized.assumptions at member
    rw [closed] at member
    cases member

/-- Preparation supplies the complete ordered input binders, while the real
second compiler pass supplies the exact source statement roots. -/
theorem agreement {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction}
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) := by
  obtain ⟨same, binders, _⟩ := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs inputs
  refine ⟨rfl, compiled_roots_eq compiled, ?_, rfl⟩
  change named.specialized.function.typedBody.inputs = named.inputs.map Prod.fst
  rw [same]
  exact binders.symm

/-- Accepted specialization, independent canonical validity and real compiled
roots construct the source frame. There is no source body trace premise. -/
theorem canonical_frame {program : CheckedProgram} {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨instantiated signatureMember genericMember accepted valid,
    rfl, rfl, rfl, rfl, rfl, compiled_roots compiled, empty_covers closed⟩

/-- The actual first and second compiler passes supply both source agreement
and the independent ordinary invocation frame. -/
theorem of_compilation {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedMetadata.instantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨agreement inputs compiled, canonical_frame signatureMember genericMember accepted valid closed compiled⟩

/-- Source inference's full reversed metadata invokes the same independently
instantiated body and ordinary source view. Domain uniqueness comes from Valid. -/
theorem retained_frame {program : CheckedProgram} {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) := by
  have canonical := canonical_frame signatureMember genericMember accepted valid closed compiled
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates canonical.instantiated,
    canonical.source, canonical.context, canonical.parameters, canonical.result,
    canonical.captured, canonical.roots, canonical.covers⟩

theorem retained_of_compilation {program : CheckedProgram}
    {representation : SourceCoreGeneralFunctions.Representation}
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {specialized : SourceSpecialization.SpecializedFunction}
    (signatureMember : signature ∈ program.signatures.functions)
    (genericMember : generic ∈ program.functions)
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized)
    (valid : DeclarationInstantiation.Valid (Context.ofSignatures program.signatures)
      (CallableNamedMetadata.instantiation named.specialized))
    (closed : named.specialized.assumptions = [])
    (inputs : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named)
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :
    CompatibleNamedBody.NamedAgreement named (view program named compiled.statements) ∧
    NamedCalls.SourceFrame (Program.ofChecked program) (CallableNamedCanonicalOrder.retainedInstantiation named.specialized)
      (bodyInstance program named.specialized) (view program named compiled.statements) :=
  ⟨agreement inputs compiled, retained_frame signatureMember genericMember accepted valid closed compiled⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedSourceFrames
