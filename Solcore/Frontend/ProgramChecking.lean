import Solcore.Frontend.ProgramSignaturesProperties
import Solcore.Frontend.ProgramSignatureFormation
import Solcore.Frontend.SourceInference

/-!
The executable whole-program source-checking entry point.

This layer keeps validation/parsing, signature construction, ordinary body
inference, failed trait search, and inconclusive trait search observably
separate.  It also retains the resolved declarations and signatures alongside
the inferred function summaries so downstream consumers do not need to repeat
the front-end pipeline.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One implementation method paired with its stable catalog identity.  The
ordinary checked-function carrier records only the owning implementation
declaration, so it cannot distinguish sibling methods by itself. -/
structure CheckedImplementationMethod where
  id : ProgramImplMethodId
  checked : SourceInference.CheckedFunction
  deriving Repr

/-- A complete successful result from the first executable source type checker. -/
structure CheckedProgram where
  environment : ProgramEnvironment
  signatures : ProgramSignatures
  functions : List SourceInference.CheckedFunction
  methods : List CheckedImplementationMethod := []
  deriving Repr

/-- Stage-preserving failures from validation through trait-constrained body
inference.  `noSolution` and `inconclusive` remain distinct because the latter
must not be treated as a negative trait answer. -/
inductive ProgramCheckError where
  | loading (error : ProgramLoadError)
  | signature (error : ProgramSignatureError)
  | signatureFormation (error : ProgramSignatureFormationError)
  | inference (error : SourceInference.FunctionError)
  | noSolution
      (declaration : Resolved.DeclarationId)
      (predicate : ProgramPredicate)
  | inconclusive
      (declaration : Resolved.DeclarationId)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId TypeSystem.Ty ProgramImplId)
  | methodInference
      (method : ProgramImplMethodId)
      (error : SourceInference.Error)
  | methodNoSolution
      (method : ProgramImplMethodId)
      (predicate : ProgramPredicate)
  | methodInconclusive
      (method : ProgramImplMethodId)
      (reason : TraitResolution.InconclusiveReason
        ProgramTraitId TypeSystem.Ty ProgramImplId)
  deriving Repr

/-- The observable result of checking one raw workspace. -/
abbrev ProgramCheckResult := Except (List ProgramCheckError) CheckedProgram

private def classifyFunctionError
    (failure : SourceInference.FunctionError) : ProgramCheckError :=
  match failure.error with
  | .noTraitImplementation predicate =>
      .noSolution failure.declaration predicate
  | .inconclusiveTrait reason =>
      .inconclusive failure.declaration reason
  | _ => .inference failure

private def classifyMethodError (method : ProgramImplMethodId) :
    SourceInference.Error → ProgramCheckError
  | .noTraitImplementation predicate => .methodNoSolution method predicate
  | .inconclusiveTrait reason => .methodInconclusive method reason
  | error => .methodInference method error

/-- One implementation/method pair selected in whole-program catalog order
for independent body checking. -/
structure ImplementationMethodCheckTarget where
  implementation : ProgramImplementationSignature
  method : ProgramImplMethodSignature

/-- Flatten the implementation-method catalog into its body-checking order. -/
def implementationMethodCheckTargets
    (signatures : ProgramSignatures) : List ImplementationMethodCheckTarget :=
  signatures.implementations.flatMap fun implementation =>
    implementation.methods.map fun method => { implementation, method }

private def checkImplementationMethodBody
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (context : ImplementationMethodCheckTarget)
    (fuel : Nat) : Except ProgramCheckError CheckedImplementationMethod := do
  let traitId := context.method.traitMethod.trait
  let trait ← match signatures.trait? traitId with
    | some trait => pure trait
    | none => throw (.signature (.traitCatalogUnavailable
        context.implementation.id traitId))
  let synthetic := context.implementation.functionSignatureOfMethodWithTrait
    trait context.method
  match SourceInference.checkFunctionBody environment signatures synthetic fuel with
  | .ok checked => .ok { id := context.method.id, checked }
  | .error error => .error (classifyMethodError context.method.id error)

private def checkImplementationMethodBodiesAux
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    List ImplementationMethodCheckTarget → List CheckedImplementationMethod →
      List ProgramCheckError →
      List CheckedImplementationMethod × List ProgramCheckError
  | [], checked, errors => (checked, errors)
  | context :: rest, checked, errors =>
      match checkImplementationMethodBody environment signatures context fuel with
      | .ok result =>
          checkImplementationMethodBodiesAux environment signatures fuel rest
            (checked ++ [result]) errors
      | .error error =>
          checkImplementationMethodBodiesAux environment signatures fuel rest
            checked (errors ++ [error])

private theorem checkImplementationMethodBody_success_id
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {context : ImplementationMethodCheckTarget}
    {fuel : Nat}
    {checked : CheckedImplementationMethod}
    (success : checkImplementationMethodBody environment signatures context fuel =
      .ok checked) :
    checked.id = context.method.id := by
  unfold checkImplementationMethodBody at success
  cases traitResult : signatures.trait? context.method.traitMethod.trait with
  | none => simp [traitResult, bind, Except.bind] at success
  | some trait =>
      cases bodyResult : SourceInference.checkFunctionBody environment signatures
          (context.implementation.functionSignatureOfMethodWithTrait trait
            context.method) fuel with
      | error error => simp [traitResult, bodyResult] at success
      | ok function =>
          simp [traitResult, bodyResult] at success
          subst checked
          rfl

/-- Exact executable provenance for one successfully checked implementation
method, including the selected trait catalog entry and synthetic signature. -/
inductive ImplementationMethodBodyChecked
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat)
    (target : ImplementationMethodCheckTarget)
    (checked : CheckedImplementationMethod) : Prop where
  | intro
      {trait : ProgramTraitSignature}
      (id_eq : checked.id = target.method.id)
      (trait_lookup : signatures.trait? target.method.traitMethod.trait =
        some trait)
      (body_success : SourceInference.checkFunctionBody environment signatures
        (target.implementation.functionSignatureOfMethodWithTrait trait
          target.method) fuel = .ok checked.checked) :
      ImplementationMethodBodyChecked environment signatures fuel target
        checked

private theorem checkImplementationMethodBody_success_provenance
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {target : ImplementationMethodCheckTarget}
    {fuel : Nat}
    {checked : CheckedImplementationMethod}
    (success : checkImplementationMethodBody environment signatures target fuel =
      .ok checked) :
    ImplementationMethodBodyChecked environment signatures fuel target
      checked := by
  unfold checkImplementationMethodBody at success
  cases traitResult : signatures.trait? target.method.traitMethod.trait with
  | none => simp [traitResult, bind, Except.bind] at success
  | some trait =>
      cases bodyResult : SourceInference.checkFunctionBody environment signatures
          (target.implementation.functionSignatureOfMethodWithTrait trait
            target.method) fuel with
      | error error => simp [traitResult, bodyResult] at success
      | ok function =>
          simp [traitResult, bodyResult] at success
          subst checked
          exact .intro rfl traitResult bodyResult

/-- Source-ordered provenance for every implementation method accepted by the
whole-program checker. -/
inductive ImplementationMethodBodiesChecked
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    List ImplementationMethodCheckTarget →
      List CheckedImplementationMethod → Prop where
  | nil : ImplementationMethodBodiesChecked environment signatures fuel [] []
  | cons
      {target : ImplementationMethodCheckTarget}
      {remaining : List ImplementationMethodCheckTarget}
      {method : CheckedImplementationMethod}
      {methods : List CheckedImplementationMethod}
      (head : ImplementationMethodBodyChecked environment signatures fuel
        target method)
      (tail : ImplementationMethodBodiesChecked environment signatures fuel
        remaining methods) :
      ImplementationMethodBodiesChecked environment signatures fuel
        (target :: remaining) (method :: methods)

namespace ImplementationMethodBodiesChecked

/-- Every retained checked method comes from one exact target in the flattened
implementation-method checking order. -/
theorem exists_target_of_method_mem
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {targets : List ImplementationMethodCheckTarget}
    {methods : List CheckedImplementationMethod}
    (checked : ImplementationMethodBodiesChecked environment signatures fuel
      targets methods)
    {method : CheckedImplementationMethod}
    (member : method ∈ methods) :
    ∃ target, target ∈ targets ∧
      ImplementationMethodBodyChecked environment signatures fuel target
        method := by
  induction checked with
  | nil => simp at member
  | @cons target remaining headMethod tailMethods head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨target, by simp, head⟩
      · obtain ⟨found, foundMember, foundChecked⟩ := induction member
        exact ⟨found, by simp [foundMember], foundChecked⟩

end ImplementationMethodBodiesChecked

private theorem checkImplementationMethodBodiesAux_success_ids
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    ∀ contexts checked errors finalChecked,
      checkImplementationMethodBodiesAux environment signatures fuel contexts
          checked errors = (finalChecked, []) →
        errors = [] ∧
          finalChecked.map (fun method => method.id) =
            checked.map (fun method => method.id) ++
              contexts.map (fun context => context.method.id) := by
  intro contexts
  induction contexts with
  | nil =>
      intro checked errors finalChecked success
      have checkedEq := congrArg Prod.fst success
      have errorsEq := congrArg Prod.snd success
      simp only [checkImplementationMethodBodiesAux] at checkedEq errorsEq
      subst finalChecked
      exact ⟨errorsEq, by simp⟩
  | cons context rest induction =>
      intro checked errors finalChecked success
      cases bodyResult :
          checkImplementationMethodBody environment signatures context fuel with
      | error error =>
          have tail := induction checked (errors ++ [error]) finalChecked (by
            simpa [checkImplementationMethodBodiesAux, bodyResult] using success)
          simp at tail
      | ok result =>
          have tail := induction (checked ++ [result]) errors finalChecked (by
            simpa [checkImplementationMethodBodiesAux, bodyResult] using success)
          refine ⟨tail.1, ?_⟩
          have resultId := checkImplementationMethodBody_success_id bodyResult
          simpa [List.map_append, resultId, List.append_assoc] using tail.2

/-- Successful accumulation preserves exact method-check provenance after the
input result prefix. -/
private theorem checkImplementationMethodBodiesAux_success_corresponds
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat) :
    ∀ targets checked errors finalChecked,
      checkImplementationMethodBodiesAux environment signatures fuel targets
          checked errors = (finalChecked, []) →
        errors = [] ∧
          ∃ produced,
            finalChecked = checked ++ produced ∧
              ImplementationMethodBodiesChecked environment signatures fuel
                targets produced := by
  intro targets
  induction targets with
  | nil =>
      intro checked errors finalChecked success
      have checkedEq := congrArg Prod.fst success
      have errorsEq := congrArg Prod.snd success
      simp only [checkImplementationMethodBodiesAux] at checkedEq errorsEq
      subst finalChecked
      exact ⟨errorsEq, [], by simp, .nil⟩
  | cons target rest induction =>
      intro checked errors finalChecked success
      cases bodyResult :
          checkImplementationMethodBody environment signatures target fuel with
      | error error =>
          have tail := induction checked (errors ++ [error]) finalChecked (by
            simpa [checkImplementationMethodBodiesAux, bodyResult] using success)
          simp at tail
      | ok result =>
          obtain ⟨errorsEq, produced, finalEq, corresponds⟩ :=
            induction (checked ++ [result]) errors finalChecked (by
              simpa [checkImplementationMethodBodiesAux, bodyResult] using success)
          refine ⟨errorsEq, result :: produced, ?_, ?_⟩
          · simpa [List.append_assoc] using finalEq
          · exact .cons
              (checkImplementationMethodBody_success_provenance bodyResult)
              corresponds

/-- Check every implementation method independently in implementation and
method source order, retaining all independent failures. -/
def checkImplementationMethodBodies
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedImplementationMethod) :=
  let (checked, errors) := checkImplementationMethodBodiesAux environment
    signatures fuel (implementationMethodCheckTargets signatures) [] []
  if errors.isEmpty then .ok checked else .error errors

/-- Successful implementation-method checking retains every cataloged method
identity exactly once and in implementation/method source order. -/
theorem checkImplementationMethodBodies_success_ids
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {methods : List CheckedImplementationMethod}
    (success : checkImplementationMethodBodies environment signatures fuel =
      .ok methods) :
    methods.map (fun method => method.id) =
      signatures.implementations.flatMap fun implementation =>
        implementation.methods.map (fun method => method.id) := by
  unfold checkImplementationMethodBodies at success
  cases resultEq :
      checkImplementationMethodBodiesAux environment signatures fuel
        (implementationMethodCheckTargets signatures) [] [] with
  | mk checked errors =>
      rw [resultEq] at success
      change (if errors.isEmpty then Except.ok checked else Except.error errors) =
        Except.ok methods at success
      by_cases errorsEmpty : errors.isEmpty = true
      · simp only [errorsEmpty, if_true, Except.ok.injEq] at success
        have errorsEq : errors = [] := List.isEmpty_iff.mp errorsEmpty
        subst checked
        subst errors
        have ids := (checkImplementationMethodBodiesAux_success_ids environment
          signatures fuel (implementationMethodCheckTargets signatures) [] [] methods
          resultEq).2
        simpa [implementationMethodCheckTargets, List.map_flatMap,
          Function.comp_def] using ids
      · simp [errorsEmpty] at success

/-- Successful implementation-method checking retains exact executable
provenance for every catalog method in implementation/method source order. -/
theorem checkImplementationMethodBodies_success_corresponds
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {methods : List CheckedImplementationMethod}
    (success : checkImplementationMethodBodies environment signatures fuel =
      .ok methods) :
    ImplementationMethodBodiesChecked environment signatures fuel
      (implementationMethodCheckTargets signatures) methods := by
  unfold checkImplementationMethodBodies at success
  cases resultEq :
      checkImplementationMethodBodiesAux environment signatures fuel
        (implementationMethodCheckTargets signatures) [] [] with
  | mk checked errors =>
      rw [resultEq] at success
      change (if errors.isEmpty then Except.ok checked else Except.error errors) =
        Except.ok methods at success
      by_cases errorsEmpty : errors.isEmpty = true
      · simp only [errorsEmpty, if_true, Except.ok.injEq] at success
        have errorsEq : errors = [] := List.isEmpty_iff.mp errorsEmpty
        subst checked
        subst errors
        obtain ⟨_, produced, methodsEq, corresponds⟩ :=
          checkImplementationMethodBodiesAux_success_corresponds environment
            signatures fuel (implementationMethodCheckTargets signatures) [] []
              methods resultEq
        simpa using methodsEq ▸ corresponds
      · simp [errorsEmpty] at success

/-- Every successfully retained method exposes its catalog membership, trait
lookup, stable identity, and exact synthetic-signature body-check equation. -/
theorem checkImplementationMethodBodies_success_member
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {fuel : Nat}
    {methods : List CheckedImplementationMethod}
    (success : checkImplementationMethodBodies environment signatures fuel =
      .ok methods)
    {checked : CheckedImplementationMethod}
    (member : checked ∈ methods) :
    ∃ implementation method trait,
      implementation ∈ signatures.implementations ∧
        method ∈ implementation.methods ∧
          signatures.trait? method.traitMethod.trait = some trait ∧
            checked.id = method.id ∧
              SourceInference.checkFunctionBody environment signatures
                (implementation.functionSignatureOfMethodWithTrait trait method)
                  fuel = .ok checked.checked := by
  obtain ⟨target, targetMember, targetChecked⟩ :=
    (checkImplementationMethodBodies_success_corresponds success)
      |>.exists_target_of_method_mem member
  rcases target with ⟨implementation, method⟩
  have catalogMember : implementation ∈ signatures.implementations ∧
      method ∈ implementation.methods := by
    simpa [implementationMethodCheckTargets] using targetMember
  cases targetChecked with
  | @intro trait idEq traitLookup bodySuccess =>
      exact ⟨implementation, method, trait, catalogMember.1,
        catalogMember.2, traitLookup, idEq, bodySuccess⟩

/-- Check an already loaded program while retaining its environment and the
resolved signature/implementation catalog in the successful result. -/
def checkLoadedProgram (loaded : LoadedProgram) (fuel : Nat := 1024) :
    ProgramCheckResult :=
  match buildProgramSignatures loaded.environment with
  | .error errors => .error (errors.map ProgramCheckError.signature)
  | .ok signatures =>
      match validateProgramSignatureFormation signatures with
      | .error errors =>
          .error (errors.map ProgramCheckError.signatureFormation)
      | .ok () =>
          let functions := SourceInference.checkFunctionBodies loaded.environment
            signatures fuel
          let methods := checkImplementationMethodBodies loaded.environment
            signatures fuel
          match functions, methods with
          | .ok functions, .ok methods => .ok {
              environment := loaded.environment
              signatures
              functions
              methods
            }
          | .error functionErrors, .ok _ =>
              .error (functionErrors.map classifyFunctionError)
          | .ok _, .error methodErrors => .error methodErrors
          | .error functionErrors, .error methodErrors =>
              .error (functionErrors.map classifyFunctionError ++ methodErrors)

private theorem checkLoadedProgram_success_components
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    ∃ signatures functions methods,
      buildProgramSignatures loaded.environment = .ok signatures ∧
        validateProgramSignatureFormation signatures = .ok () ∧
        SourceInference.checkFunctionBodies loaded.environment signatures fuel =
          .ok functions ∧
        checkImplementationMethodBodies loaded.environment signatures fuel =
          .ok methods ∧
        checked = {
          environment := loaded.environment
          signatures
          functions
          methods
        } := by
  cases signaturesResult : buildProgramSignatures loaded.environment with
  | error signatureErrors =>
      simp [checkLoadedProgram, signaturesResult] at success
  | ok signatures =>
      cases formationResult : validateProgramSignatureFormation signatures with
      | error formationErrors =>
          simp [checkLoadedProgram, signaturesResult, formationResult] at success
      | ok formationUnit =>
          cases formationUnit
          cases functionsResult : SourceInference.checkFunctionBodies
              loaded.environment signatures fuel with
          | error functionErrors =>
              cases methodsResult : checkImplementationMethodBodies
                  loaded.environment signatures fuel with
              | error methodErrors =>
                  simp [checkLoadedProgram, signaturesResult, formationResult,
                    functionsResult, methodsResult] at success
              | ok methods =>
                  simp [checkLoadedProgram, signaturesResult, formationResult,
                    functionsResult, methodsResult] at success
          | ok functions =>
              cases methodsResult : checkImplementationMethodBodies
                  loaded.environment signatures fuel with
              | error methodErrors =>
                  simp [checkLoadedProgram, signaturesResult, formationResult,
                    functionsResult, methodsResult] at success
              | ok methods =>
                  simp [checkLoadedProgram, signaturesResult, formationResult,
                    functionsResult, methodsResult] at success
                  subst checked
                  exact ⟨signatures, functions, methods, rfl, formationResult,
                    functionsResult, methodsResult, rfl⟩

/-- A successful loaded-program check retains the exact environment supplied
by the loader. -/
theorem checkLoadedProgram_success_environment
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    checked.environment = loaded.environment := by
  obtain ⟨_, _, _, _, _, _, _, checked_eq⟩ :=
    checkLoadedProgram_success_components success
  rw [checked_eq]

/-- A successful loaded-program check retains the exact signature-builder
result used by body checking. -/
theorem checkLoadedProgram_success_signatures
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    buildProgramSignatures loaded.environment = .ok checked.signatures := by
  obtain ⟨_, _, _, signaturesResult, _, _, _, checked_eq⟩ :=
    checkLoadedProgram_success_components success
  rw [checked_eq]
  exact signaturesResult

/-- A successful loaded-program check has executable formation evidence for
every directly resolved signature type and predicate. -/
theorem checkLoadedProgram_success_signature_formation
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    ProgramSignatureFormationValidated checked.signatures := by
  obtain ⟨_, _, _, _, formationResult, _, _, checked_eq⟩ :=
    checkLoadedProgram_success_components success
  rw [checked_eq]
  exact validateProgramSignatureFormation_success formationResult

/-- A successful loaded-program check carries the signature builder's
canonical generic-parameter allocation guarantees into the checked artifact. -/
theorem checkLoadedProgram_success_signature_parameters_wellFormed
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    ProgramSignatureParametersWellFormed checked.signatures :=
  buildProgramSignatures_success_parameters_wellFormed
    (checkLoadedProgram_success_signatures success)

/-- A successful loaded-program check retains the function signature shape
guarantees established by signature collection. -/
theorem checkLoadedProgram_success_function_signature_shape
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ checked.signatures.functions) :
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) :=
  buildProgramSignatures_success_function_shape
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check retains each data signature's
duplicate-free constructor names and declaration-owned source-order IDs. -/
theorem checkLoadedProgram_success_data_signature_structure
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramDataSignature}
    (member : signature ∈ checked.signatures.dataTypes) :
    DataSignatureStructuralWellFormed signature :=
  buildProgramSignatures_success_data_structure
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check retains each trait signature's
duplicate-free method names, declaration-owned source-order IDs, and
duplicate-free method parameter names. -/
theorem checkLoadedProgram_success_trait_signature_structure
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramTraitSignature}
    (member : signature ∈ checked.signatures.traits) :
    TraitSignatureStructuralWellFormed signature :=
  buildProgramSignatures_success_trait_structure
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check retains each implementation signature's
duplicate-free method names, declaration-owned source-order IDs, and
duplicate-free method parameter names. -/
theorem checkLoadedProgram_success_implementation_signature_structure
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureStructuralWellFormed signature :=
  buildProgramSignatures_success_implementation_structure
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check retains the selected trait entry and
the containment checks performed for every implementation head. -/
theorem checkLoadedProgram_success_implementation_head_validated
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureHeadValidated checked.signatures.traits signature :=
  buildProgramSignatures_success_implementation_head_validated
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check retains exact method correspondence and
completeness for each implementation's selected trait. -/
theorem checkLoadedProgram_success_implementation_method_catalog_validated
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureMethodCatalogValidated checked.signatures.traits
      signature :=
  buildProgramSignatures_success_implementation_method_catalog_validated
    (checkLoadedProgram_success_signatures success) member

/-- A successful loaded-program check preserves the exact function and method
identity order of the resolved signature catalog. -/
theorem checkLoadedProgram_success_ids
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    checked.functions.map (fun function => function.declaration) =
        checked.signatures.functions.map (fun signature => signature.id) ∧
      checked.methods.map (fun method => method.id) =
        checked.signatures.implementations.flatMap fun implementation =>
          implementation.methods.map (fun method => method.id) := by
  obtain ⟨_, _, _, _, _, functionsResult, methodsResult, checked_eq⟩ :=
    checkLoadedProgram_success_components success
  rw [checked_eq]
  exact ⟨
    SourceInference.checkFunctionBodies_success_declaration_ids functionsResult,
    checkImplementationMethodBodies_success_ids methodsResult
  ⟩

/-- A successful loaded-program check retains the exact executable body-check
provenance for every top-level function and implementation method. -/
theorem checkLoadedProgram_success_body_checks
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    SourceInference.FunctionBodiesChecked checked.environment
        checked.signatures fuel checked.signatures.functions checked.functions ∧
      ImplementationMethodBodiesChecked checked.environment checked.signatures
        fuel (implementationMethodCheckTargets checked.signatures)
          checked.methods := by
  obtain ⟨_, _, _, _, _, functionsResult, methodsResult, checkedEq⟩ :=
    checkLoadedProgram_success_components success
  subst checked
  exact ⟨
    SourceInference.checkFunctionBodies_success_corresponds functionsResult,
    checkImplementationMethodBodies_success_corresponds methodsResult
  ⟩

/-- Recover the exact catalog signature and body-check equation for any
function retained by successful loaded-program checking. -/
theorem checkLoadedProgram_success_function_body
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {function : SourceInference.CheckedFunction}
    (member : function ∈ checked.functions) :
    ∃ signature, signature ∈ checked.signatures.functions ∧
      SourceInference.checkFunctionBody checked.environment checked.signatures
        signature fuel = .ok function := by
  exact (checkLoadedProgram_success_body_checks success).1
    |>.exists_signature_of_function_mem member

/-- Recover the exact implementation, method, selected trait, and synthetic
body-check equation for any method retained by successful loaded checking. -/
theorem checkLoadedProgram_success_method_body
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked)
    {checkedMethod : CheckedImplementationMethod}
    (member : checkedMethod ∈ checked.methods) :
    ∃ implementation method trait,
      implementation ∈ checked.signatures.implementations ∧
        method ∈ implementation.methods ∧
          checked.signatures.trait? method.traitMethod.trait = some trait ∧
            checkedMethod.id = method.id ∧
              SourceInference.checkFunctionBody checked.environment
                checked.signatures
                (implementation.functionSignatureOfMethodWithTrait trait method)
                  fuel = .ok checkedMethod.checked := by
  obtain ⟨_, _, _, _, _, functionsResult, methodsResult, checkedEq⟩ :=
    checkLoadedProgram_success_components success
  subst checked
  exact checkImplementationMethodBodies_success_member methodsResult member

/-- Validate, parse, catalog, resolve, and check every top-level function and
implementation-method body in canonical declaration order. -/
def checkProgram (raw : Workspace.RawWorkspace) (fuel : Nat := 1024) :
    ProgramCheckResult :=
  match loadProgram raw with
  | .error errors => .error (errors.map ProgramCheckError.loading)
  | .ok loaded => checkLoadedProgram loaded fuel

/-- Decompose raw checker success into the successful loader result and the
corresponding successful loaded-program check. -/
theorem checkProgram_success_load
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ∃ loaded,
      loadProgram raw = .ok loaded ∧
        checkLoadedProgram loaded fuel = .ok checked := by
  cases loadedResult : loadProgram raw with
  | error errors => simp [checkProgram, loadedResult] at success
  | ok loaded =>
      exact ⟨loaded, rfl, by
        simpa [checkProgram, loadedResult] using success⟩

/-- End-to-end checker success exposes executable formation evidence for its
completed signature catalog. -/
theorem checkProgram_success_signature_formation
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ProgramSignatureFormationValidated checked.signatures := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_signature_formation checkedSuccess

/-- A successful raw-workspace check preserves the exact function and method
identity order of the resolved signature catalog. -/
theorem checkProgram_success_ids
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    checked.functions.map (fun function => function.declaration) =
        checked.signatures.functions.map (fun signature => signature.id) ∧
      checked.methods.map (fun method => method.id) =
        checked.signatures.implementations.flatMap fun implementation =>
          implementation.methods.map (fun method => method.id) := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_ids checkedSuccess

/-- End-to-end checker success preserves exact per-body executable
provenance for both functions and implementation methods. -/
theorem checkProgram_success_body_checks
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    SourceInference.FunctionBodiesChecked checked.environment
        checked.signatures fuel checked.signatures.functions checked.functions ∧
      ImplementationMethodBodiesChecked checked.environment checked.signatures
        fuel (implementationMethodCheckTargets checked.signatures)
          checked.methods := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_body_checks checkedSuccess

/-- Raw checker success exposes one exact catalog signature and body-check
equation for every retained top-level function. -/
theorem checkProgram_success_function_body
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {function : SourceInference.CheckedFunction}
    (member : function ∈ checked.functions) :
    ∃ signature, signature ∈ checked.signatures.functions ∧
      SourceInference.checkFunctionBody checked.environment checked.signatures
        signature fuel = .ok function := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_function_body checkedSuccess member

/-- Raw checker success exposes the complete synthetic-signature provenance
for every retained implementation method. -/
theorem checkProgram_success_method_body
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {checkedMethod : CheckedImplementationMethod}
    (member : checkedMethod ∈ checked.methods) :
    ∃ implementation method trait,
      implementation ∈ checked.signatures.implementations ∧
        method ∈ implementation.methods ∧
          checked.signatures.trait? method.traitMethod.trait = some trait ∧
            checkedMethod.id = method.id ∧
              SourceInference.checkFunctionBody checked.environment
                checked.signatures
                (implementation.functionSignatureOfMethodWithTrait trait method)
                  fuel = .ok checkedMethod.checked := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_method_body checkedSuccess member

/-- A successfully checked raw workspace retains pairwise distinct declaration
identities in its checked environment. -/
theorem checkProgram_success_declarations_nodup
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    (checked.environment.declarations.map (·.id)).Nodup := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    checkProgram_success_load success
  rw [checkLoadedProgram_success_environment checkedSuccess]
  exact loadProgram_success_declarations_nodup loadedSuccess

/-- A successfully checked raw workspace retains pairwise distinct identities
across every declaration category represented by its signature catalog. -/
theorem checkProgram_success_signature_declaration_ids_nodup
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ((checked.signatures.functions.map fun signature => signature.id) ++
      (checked.signatures.dataTypes.map fun signature => signature.id) ++
      (checked.signatures.traits.map fun signature => signature.id) ++
      (checked.signatures.implementations.map fun signature => signature.id) ++
      (checked.signatures.contracts.map fun signature => signature.id)).Nodup := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    checkProgram_success_load success
  exact buildProgramSignatures_success_declaration_ids_nodup
    (loadProgram_success_declarations_nodup loadedSuccess)
    (checkLoadedProgram_success_signatures checkedSuccess)

/-- End-to-end checker success guarantees canonical declaration ownership and
source-order numbering for every collected rigid generic parameter. -/
theorem checkProgram_success_signature_parameters_wellFormed
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    ProgramSignatureParametersWellFormed checked.signatures := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_signature_parameters_wellFormed checkedSuccess

/-- End-to-end checker success guarantees duplicate-free function parameter
names and the canonical constrained-scheme body for every collected function. -/
theorem checkProgram_success_function_signature_shape
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ checked.signatures.functions) :
    signature.parameterNames.Nodup ∧
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes) := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_function_signature_shape checkedSuccess member

/-- End-to-end checker success retains each data signature's structural
constructor guarantees. -/
theorem checkProgram_success_data_signature_structure
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramDataSignature}
    (member : signature ∈ checked.signatures.dataTypes) :
    DataSignatureStructuralWellFormed signature := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_data_signature_structure checkedSuccess member

/-- End-to-end checker success retains each trait signature's structural
method guarantees. -/
theorem checkProgram_success_trait_signature_structure
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramTraitSignature}
    (member : signature ∈ checked.signatures.traits) :
    TraitSignatureStructuralWellFormed signature := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_trait_signature_structure checkedSuccess member

/-- End-to-end checker success retains each implementation signature's
structural method guarantees. -/
theorem checkProgram_success_implementation_signature_structure
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureStructuralWellFormed signature := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_implementation_signature_structure
    checkedSuccess member

/-- End-to-end checker success retains the selected trait entry and the
containment checks performed for every implementation head. -/
theorem checkProgram_success_implementation_head_validated
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureHeadValidated checked.signatures.traits signature := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_implementation_head_validated
    checkedSuccess member

/-- End-to-end checker success establishes exact trait-method correspondence
and selected-trait method completeness for every implementation. -/
theorem checkProgram_success_implementation_method_catalog_validated
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked)
    {signature : ProgramImplementationSignature}
    (member : signature ∈ checked.signatures.implementations) :
    ImplementationSignatureMethodCatalogValidated checked.signatures.traits
      signature := by
  obtain ⟨_, _, checkedSuccess⟩ := checkProgram_success_load success
  exact checkLoadedProgram_success_implementation_method_catalog_validated
    checkedSuccess member

/-- End-to-end checker success assigns globally unique constructor identities
across every collected data declaration. -/
theorem checkProgram_success_constructor_ids_nodup
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    (checked.signatures.dataTypes.flatMap fun signature =>
      signature.constructors.map fun constructor => constructor.id).Nodup := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    checkProgram_success_load success
  exact buildProgramSignatures_success_constructor_ids_nodup
    (loadProgram_success_declarations_nodup loadedSuccess)
    (checkLoadedProgram_success_signatures checkedSuccess)

/-- End-to-end checker success assigns globally unique trait-method
identities across every collected trait declaration. -/
theorem checkProgram_success_trait_method_ids_nodup
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    (checked.signatures.traits.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    checkProgram_success_load success
  exact buildProgramSignatures_success_trait_method_ids_nodup
    (loadProgram_success_declarations_nodup loadedSuccess)
    (checkLoadedProgram_success_signatures checkedSuccess)

/-- End-to-end checker success assigns globally unique implementation-method
identities across every collected implementation declaration. -/
theorem checkProgram_success_implementation_method_ids_nodup
    {raw : Workspace.RawWorkspace}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkProgram raw fuel = .ok checked) :
    (checked.signatures.implementations.flatMap fun signature =>
      signature.methods.map fun method => method.id).Nodup := by
  obtain ⟨loaded, loadedSuccess, checkedSuccess⟩ :=
    checkProgram_success_load success
  exact buildProgramSignatures_success_implementation_method_ids_nodup
    (loadProgram_success_declarations_nodup loadedSuccess)
    (checkLoadedProgram_success_signatures checkedSuccess)

end Solcore.Frontend
