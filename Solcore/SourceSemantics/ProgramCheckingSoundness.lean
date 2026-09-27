import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.Program

/-!
Conditional bridge from executable whole-program checking results to the
declarative source-program carrier.

The conversions in this module only forget algorithmic bookkeeping.  They do
not claim that checker success alone proves the declarative judgments.  The
aggregation theorem therefore requires the signature-catalog invariant, exact
body/catalog identity alignment, and semantic validity of every converted
body explicitly.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

namespace FunctionDefinition

/-- Forget algorithmic bookkeeping from one checked top-level function. -/
def ofChecked (function : CheckedFunction) : FunctionDefinition := {
  body := BodyDefinition.ofChecked function
}

end FunctionDefinition

namespace MethodDefinition

/-- Forget algorithmic bookkeeping from one checked implementation method
while retaining the stable method identity absent from `CheckedFunction`. -/
def ofChecked (method : CheckedImplementationMethod) : MethodDefinition := {
  id := method.id
  body := BodyDefinition.ofChecked method.checked
}

end MethodDefinition

namespace Program

/-- Project a frontend checked-program carrier into the declarative source
program carrier.  Validity remains a separate proposition. -/
def ofChecked (checked : CheckedProgram) : Program := {
  signatures := checked.signatures
  functions := checked.functions.map FunctionDefinition.ofChecked
  methods := checked.methods.map MethodDefinition.ofChecked
}

end Program

/-- Raw-workspace checker success discharges the cross-category declaration
identity component of semantic signature-catalog well-formedness. -/
theorem signatureDeclarationIds_nodup_ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = .ok checked) :
    (signatureDeclarationIds checked.signatures).Nodup := by
  simpa [signatureDeclarationIds] using
    Frontend.checkProgram_success_signature_declaration_ids_nodup success

/-- The remaining proof obligations for promoting a forgeable checked-program
carrier to a declaratively well-formed source program.  Exact ID alignment
rules out missing and extra bodies; semantic body validity is deliberately an
explicit premise rather than being identified with checker success. -/
structure CheckedProgramWellFormedConditions
    (checked : CheckedProgram) : Prop where
  signatures : SignatureCatalogWellFormed checked.signatures
  function_ids : checked.functions.map (fun function => function.declaration) =
    checked.signatures.functions.map (fun signature => signature.id)
  method_ids : checked.methods.map (fun method => method.id) =
    (checked.signatures.implementations.flatMap fun implementation =>
      implementation.methods.map fun method => method.id)
  functions_valid : ∀ function, function ∈ checked.functions →
    FunctionDefinition.Valid checked.signatures
      (FunctionDefinition.ofChecked function)
  methods_valid : ∀ method, method ∈ checked.methods →
    MethodDefinition.Valid checked.signatures
      (MethodDefinition.ofChecked method)

namespace CheckedProgramWellFormedConditions

/-- Successful executable checking discharges the exact function/method
identity alignment obligations.  The catalog invariant and semantic validity
of each body remain explicit because they are not yet consequences of checker
success. -/
theorem ofCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ :=
    Frontend.checkLoadedProgram_success_ids success
  exact {
    signatures
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Successful checking from a raw workspace likewise discharges exact body
identity alignment; callers retain only the semantic catalog/body premises. -/
theorem ofCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    CheckedProgramWellFormedConditions checked := by
  obtain ⟨functionIds, methodIds⟩ := Frontend.checkProgram_success_ids success
  exact {
    signatures
    function_ids := functionIds
    method_ids := methodIds
    functions_valid := functionsValid
    methods_valid := methodsValid
  }

/-- Assemble whole-program declarative well-formedness from the explicit
checker-to-semantics bridge obligations. -/
theorem programWellFormed
    {checked : CheckedProgram}
    (conditions : CheckedProgramWellFormedConditions checked) :
    ProgramWellFormed (Program.ofChecked checked) := by
  constructor
  · exact conditions.signatures
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [conditions.function_ids]
    exact conditions.signatures.function_ids
  · simp only [Program.ofChecked, List.map_map, Function.comp_def,
      MethodDefinition.ofChecked]
    rw [conditions.method_ids]
    exact conditions.signatures.implementation_method_ids
  · intro definition definitionMem
    simp only [Program.ofChecked, List.mem_map] at definitionMem
    rcases definitionMem with ⟨function, functionMem, rfl⟩
    exact conditions.functions_valid function functionMem
  · intro definition definitionMem
    simp only [Program.ofChecked, List.mem_map] at definitionMem
    rcases definitionMem with ⟨method, methodMem, rfl⟩
    exact conditions.methods_valid method methodMem
  · intro signature signatureMem
    have signatureIdMem : signature.id ∈
        checked.signatures.functions.map (fun candidate => candidate.id) :=
      List.mem_map.mpr ⟨signature, signatureMem, rfl⟩
    rw [← conditions.function_ids] at signatureIdMem
    rcases List.mem_map.mp signatureIdMem with
      ⟨function, functionMem, declarationEq⟩
    refine ⟨FunctionDefinition.ofChecked function, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨function, functionMem, rfl⟩
    · simpa [FunctionDefinition.ofChecked, BodyDefinition.ofChecked] using
        declarationEq
  · intro implementation implementationMem method methodMem
    have methodIdMem : method.id ∈
        (checked.signatures.implementations.flatMap fun candidate =>
          candidate.methods.map fun candidateMethod => candidateMethod.id) := by
      apply List.mem_flatMap.mpr
      exact ⟨implementation, implementationMem,
        List.mem_map.mpr ⟨method, methodMem, rfl⟩⟩
    rw [← conditions.method_ids] at methodIdMem
    rcases List.mem_map.mp methodIdMem with
      ⟨checkedMethod, checkedMethodMem, idEq⟩
    refine ⟨MethodDefinition.ofChecked checkedMethod, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨checkedMethod, checkedMethodMem, rfl⟩
    · simpa [MethodDefinition.ofChecked] using idEq

/-- Promote a successful loaded-program check directly to declarative
whole-program well-formedness once the remaining semantic premises are
supplied.  Function and method identity alignment is recovered from checker
success rather than repeated by callers. -/
theorem programWellFormedOfCheckLoadedProgram
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkLoadedProgram loaded fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckLoadedProgram success signatures
    functionsValid methodsValid).programWellFormed

/-- Promote raw-workspace checker success directly to declarative
whole-program well-formedness once the remaining semantic premises are
supplied. -/
theorem programWellFormedOfCheckProgram
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : Frontend.checkProgram raw fuel = Except.ok checked)
    (signatures : SignatureCatalogWellFormed checked.signatures)
    (functionsValid : ∀ function, function ∈ checked.functions →
      FunctionDefinition.Valid checked.signatures
        (FunctionDefinition.ofChecked function))
    (methodsValid : ∀ method, method ∈ checked.methods →
      MethodDefinition.Valid checked.signatures
        (MethodDefinition.ofChecked method)) :
    ProgramWellFormed (Program.ofChecked checked) :=
  (CheckedProgramWellFormedConditions.ofCheckProgram success signatures
    functionsValid methodsValid).programWellFormed

end CheckedProgramWellFormedConditions

end Solcore.SourceSemantics
