import Solcore.Surface.Multi.CertifiedFrontendCore
import Solcore.Surface.Multi.ExactTokenRuleClosed

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Parse one source file and return either a nonempty first-failing-phase
diagnostic list or a module carrying the frontend's machine-checked
certificates. -/
def parseModule (file : WorkspaceFile) :
    Except (NonemptyList SurfaceDiagnostic) CertifiedParsedModule :=
  parseModuleWithRootSound rootActionTokenPlanSound file

/-- Lexical failure is reported before parsing or structural validation. -/
theorem parseModule_eq_of_lexicalDiagnostic
    {file : WorkspaceFile} {diagnostic : LexicalDiagnostic}
    (lexing : lexModule file = .error diagnostic) :
    parseModule file =
      .error (singletonSurfaceDiagnostic (.lexical diagnostic)) := by
  simpa only [parseModule] using
    parseModuleWithRootSound_eq_of_lexicalDiagnostic
      rootActionTokenPlanSound lexing

/-- A parser diagnostic is preserved as the unique reported surface
diagnostic. -/
theorem parseModule_eq_of_parseDiagnostic
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {diagnostic : ParseDiagnostic}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .error diagnostic) :
    parseModule file =
      .error (singletonSurfaceDiagnostic (.parse diagnostic)) := by
  simpa only [parseModule] using
    parseModuleWithRootSound_eq_of_parseDiagnostic
      rootActionTokenPlanSound lexing parsing

/-- Structural diagnostics are reported only after lexing and parsing
succeed. -/
theorem parseModule_eq_of_structuralDiagnostics
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {module : ParsedModuleV1}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .ok module)
    {diagnostics : NonemptyList StructuralDiagnostic}
    (structural : validateStructure module = .error diagnostics) :
    parseModule file =
      .error (structuralSurfaceDiagnostics diagnostics) := by
  simpa only [parseModule] using
    parseModuleWithRootSound_eq_of_structuralDiagnostics
      rootActionTokenPlanSound lexing parsing structural

/-- Successful phases produce a certificate with the exact selected file,
tokens, comments, and module. -/
theorem parseModule_success
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {module : ParsedModuleV1}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .ok module)
    (structural : validateStructure module = .ok ()) :
    ∃ certified : CertifiedParsedModule,
      parseModule file = .ok certified ∧
        certified.file = file ∧
        certified.tokens = lexed.tokens ∧
        certified.comments = lexed.comments ∧
        certified.module = module := by
  simpa only [parseModule] using
    parseModuleWithRootSound_success rootActionTokenPlanSound
      lexing parsing structural

/-- Executable success is equivalent to success of all three frontend
phases. -/
theorem parseModule_success_iff (file : WorkspaceFile) :
    (∃ certified, parseModule file = .ok certified) ↔
      ∃ (lexed : LexedModule)
          (lexing : lexModule file = .ok lexed)
          (module : ParsedModuleV1)
          (_parsing : executeObservedContextualParse file lexed.tokens
            (lexer_tokensOwnedBy lexing) = .ok module),
        validateStructure module = .ok () := by
  simpa only [parseModule] using
    parseModuleWithRootSound_success_iff rootActionTokenPlanSound file

/-- Every failure is exactly lexical, parser, or structural, in phase order. -/
theorem parseModule_failure_iff
    (file : WorkspaceFile) (reported : NonemptyList SurfaceDiagnostic) :
    parseModule file = .error reported ↔
      (∃ diagnostic,
        lexModule file = .error diagnostic ∧
          reported = singletonSurfaceDiagnostic (.lexical diagnostic)) ∨
      (∃ (lexed : LexedModule)
          (lexing : lexModule file = .ok lexed)
          (diagnostic : ParseDiagnostic),
        executeObservedContextualParse file lexed.tokens
            (lexer_tokensOwnedBy lexing) = .error diagnostic ∧
          reported = singletonSurfaceDiagnostic (.parse diagnostic)) ∨
      ∃ (lexed : LexedModule)
          (lexing : lexModule file = .ok lexed)
          (module : ParsedModuleV1)
          (_parsing : executeObservedContextualParse file lexed.tokens
            (lexer_tokensOwnedBy lexing) = .ok module)
          (diagnostics : NonemptyList StructuralDiagnostic),
        validateStructure module = .error diagnostics ∧
          reported = structuralSurfaceDiagnostics diagnostics := by
  simpa only [parseModule] using
    parseModuleWithRootSound_failure_iff
      rootActionTokenPlanSound file reported

/-- The certified frontend returns a unique successful certificate. -/
theorem parseModule_deterministic
    {file : WorkspaceFile} {first second : CertifiedParsedModule}
    (firstResult : parseModule file = .ok first)
    (secondResult : parseModule file = .ok second) :
    first = second := by
  exact parseModuleWithRootSound_deterministic rootActionTokenPlanSound
    firstResult secondResult

/-- Every input is either accepted with certificates or diagnosed. -/
theorem parseModule_accepted_or_diagnosed (file : WorkspaceFile) :
    (∃ certified, parseModule file = .ok certified) ∨
      ∃ reported, parseModule file = .error reported := by
  simpa only [parseModule] using
    parseModuleWithRootSound_accepted_or_diagnosed
      rootActionTokenPlanSound file

/-- A successful result cannot coexist with diagnostics for the same file. -/
theorem parseModule_success_not_diagnosed
    {file : WorkspaceFile} {certified : CertifiedParsedModule}
    (success : parseModule file = .ok certified) :
    ∀ reported, parseModule file ≠ .error reported := by
  simpa only [parseModule] using
    parseModuleWithRootSound_success_not_diagnosed
      rootActionTokenPlanSound success

end Solcore.Surface.Multi
