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

private structure ImplementationMethodContext where
  implementation : ProgramImplementationSignature
  method : ProgramImplMethodSignature

private def implementationMethodContexts
    (signatures : ProgramSignatures) : List ImplementationMethodContext :=
  signatures.implementations.flatMap fun implementation =>
    implementation.methods.map fun method => { implementation, method }

private def checkImplementationMethodBody
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (context : ImplementationMethodContext)
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
    List ImplementationMethodContext → List CheckedImplementationMethod →
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
    {context : ImplementationMethodContext}
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

/-- Check every implementation method independently in implementation and
method source order, retaining all independent failures. -/
def checkImplementationMethodBodies
    (environment : ProgramEnvironment)
    (signatures : ProgramSignatures)
    (fuel : Nat := 1024) :
    Except (List ProgramCheckError) (List CheckedImplementationMethod) :=
  let (checked, errors) := checkImplementationMethodBodiesAux environment
    signatures fuel (implementationMethodContexts signatures) [] []
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
        (implementationMethodContexts signatures) [] [] with
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
          signatures fuel (implementationMethodContexts signatures) [] [] methods
          resultEq).2
        simpa [implementationMethodContexts, List.map_flatMap,
          Function.comp_def] using ids
      · simp [errorsEmpty] at success

/-- Check an already loaded program while retaining its environment and the
resolved signature/implementation catalog in the successful result. -/
def checkLoadedProgram (loaded : LoadedProgram) (fuel : Nat := 1024) :
    ProgramCheckResult :=
  match buildProgramSignatures loaded.environment with
  | .error errors => .error (errors.map ProgramCheckError.signature)
  | .ok signatures =>
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

/-- A successful loaded-program check retains the exact environment supplied
by the loader. -/
theorem checkLoadedProgram_success_environment
    {loaded : LoadedProgram}
    {fuel : Nat}
    {checked : CheckedProgram}
    (success : checkLoadedProgram loaded fuel = .ok checked) :
    checked.environment = loaded.environment := by
  cases signaturesResult : buildProgramSignatures loaded.environment with
  | error signatureErrors =>
      simp [checkLoadedProgram, signaturesResult] at success
  | ok signatures =>
      cases functionsResult : SourceInference.checkFunctionBodies
          loaded.environment signatures fuel with
      | error functionErrors =>
          cases methodsResult : checkImplementationMethodBodies
              loaded.environment signatures fuel with
          | error methodErrors =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
          | ok methods =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
      | ok functions =>
          cases methodsResult : checkImplementationMethodBodies
              loaded.environment signatures fuel with
          | error methodErrors =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
          | ok methods =>
              simp only [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult, Except.ok.injEq] at success
              subst checked
              rfl

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
  cases signaturesResult : buildProgramSignatures loaded.environment with
  | error signatureErrors =>
      simp [checkLoadedProgram, signaturesResult] at success
  | ok signatures =>
      cases functionsResult : SourceInference.checkFunctionBodies
          loaded.environment signatures fuel with
      | error functionErrors =>
          cases methodsResult : checkImplementationMethodBodies
              loaded.environment signatures fuel with
          | error methodErrors =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
          | ok methods =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
      | ok functions =>
          cases methodsResult : checkImplementationMethodBodies
              loaded.environment signatures fuel with
          | error methodErrors =>
              simp [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult] at success
          | ok methods =>
              simp only [checkLoadedProgram, signaturesResult, functionsResult,
                methodsResult, Except.ok.injEq] at success
              subst checked
              exact ⟨
                SourceInference.checkFunctionBodies_success_declaration_ids
                  functionsResult,
                checkImplementationMethodBodies_success_ids methodsResult
              ⟩

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

end Solcore.Frontend
