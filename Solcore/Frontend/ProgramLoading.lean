import Solcore.Workspace
import Solcore.Syntax.Parser
import Solcore.Frontend.ProgramEnvironment

/-! Validation and parsing at the executable whole-program boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- One validated workspace together with every diagnostic-free parsed source. -/
structure LoadedProgram where
  workspace : Workspace.ValidatedUserWorkspace
  sources : List Syntax.ParsedFile
  environment : ProgramEnvironment
  deriving Repr

/-- Failures before source type checking begins. -/
inductive ProgramLoadError where
  | workspace (error : Workspace.ValidationError)
  | syntaxInvariant
      (source : Workspace.SourceId)
      (error : Syntax.SyntaxInvariantError)
  | sourceDiagnostics
      (source : Workspace.SourceId)
      (lexical : List Syntax.LexicalDiagnostic)
      (parsing : List Syntax.ParseDiagnostic)
  | environment (error : ProgramEnvironmentError)
  deriving Repr

/-- Convert a canonical workspace library into its parser-visible owner. -/
def syntaxOriginOfWorkspaceLibrary :
    Workspace.LibraryId → Syntax.SourceOrigin
  | .main => .main
  | .standard => .standard
  | .external name => .external name.render

/-- Preserve a validated identity at the parser boundary. -/
def syntaxSourceIdOfWorkspaceSource
    (source : Workspace.SourceId) : Syntax.SourceId := {
  origin := syntaxOriginOfWorkspaceLibrary source.library
  path := source.path.render
}

/-- Present a validated source to the canonical parser. -/
def syntaxSourceFileOfWorkspaceFile
    (file : Workspace.WorkspaceFile) : Syntax.SourceFile := {
  id := syntaxSourceIdOfWorkspaceSource file.id
  content := file.content
}

private def parseWorkspaceFile
    (file : Workspace.WorkspaceFile) :
    Except ProgramLoadError Syntax.ParsedFile :=
  let source := syntaxSourceFileOfWorkspaceFile file
  match Syntax.Parser.parse source with
  | .error error => .error (.syntaxInvariant file.id error)
  | .ok output =>
      if output.lexicalDiagnostics.isEmpty &&
          output.parseDiagnostics.isEmpty then
        .ok output.parsed
      else
        .error (.sourceDiagnostics file.id output.lexicalDiagnostics
          output.parseDiagnostics)

private def parseWorkspaceFiles :
    List Workspace.WorkspaceFile →
      List ProgramLoadError × List Syntax.ParsedFile
  | [] => ([], [])
  | file :: rest =>
      let (restErrors, restSources) := parseWorkspaceFiles rest
      match parseWorkspaceFile file with
      | .ok source => (restErrors, source :: restSources)
      | .error error => (error :: restErrors, restSources)

/-- Parse and catalog an already validated workspace. -/
def loadValidatedProgram
    (workspace : Workspace.ValidatedUserWorkspace) :
    Except (List ProgramLoadError) LoadedProgram :=
  let (parseErrors, sources) := parseWorkspaceFiles workspace.files
  if parseErrors.isEmpty then
    match buildProgramEnvironment sources with
    | .ok environment => .ok { workspace, sources, environment }
    | .error errors => .error (errors.map ProgramLoadError.environment)
  else
    .error parseErrors

/-- Validate, parse and catalog one complete caller workspace. -/
def loadProgram (raw : Workspace.RawWorkspace) :
    Except (List ProgramLoadError) LoadedProgram :=
  match Workspace.validate raw with
  | .error errors => .error (errors.map ProgramLoadError.workspace)
  | .ok workspace => loadValidatedProgram workspace

end Solcore.Frontend
