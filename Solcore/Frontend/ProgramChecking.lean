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

/-- A complete successful result from the first executable source type checker. -/
structure CheckedProgram where
  environment : ProgramEnvironment
  signatures : ProgramSignatures
  functions : List SourceInference.CheckedFunction
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
        Resolved.DeclarationId TypeSystem.Ty Resolved.DeclarationId)
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

/-- Check an already loaded program while retaining its environment and the
resolved signature/implementation catalog in the successful result. -/
def checkLoadedProgram (loaded : LoadedProgram) (fuel : Nat := 1024) :
    ProgramCheckResult :=
  match buildProgramSignatures loaded.environment with
  | .error errors => .error (errors.map ProgramCheckError.signature)
  | .ok signatures =>
      match SourceInference.checkFunctionBodies loaded.environment signatures fuel with
      | .error errors => .error (errors.map classifyFunctionError)
      | .ok functions => .ok {
          environment := loaded.environment
          signatures
          functions
        }

/-- Validate, parse, catalog, resolve, and check every top-level function body
in canonical declaration order. -/
def checkProgram (raw : Workspace.RawWorkspace) (fuel : Nat := 1024) :
    ProgramCheckResult :=
  match loadProgram raw with
  | .error errors => .error (errors.map ProgramCheckError.loading)
  | .ok loaded => checkLoadedProgram loaded fuel

end Solcore.Frontend
