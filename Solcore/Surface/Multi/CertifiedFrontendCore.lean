import Solcore.Surface.Multi.EndpointActionIntervalLocation
import Solcore.Surface.Multi.ExactTokenParseSoundness
import Solcore.Surface.Multi.StructureProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A parsed module carrying every proof required by the certified frontend
boundary. -/
structure CertifiedParsedModule where
  file : WorkspaceFile
  tokens : List Token
  comments : List Comment
  module : ParsedModuleV1
  lexes : Lexes file tokens comments
  parses : Parses file tokens module
  accepted : StructurallyAccepts module
  locations : EveryLocationValid file module
  corresponds : ExactTokenCorrespondence file tokens comments module

def singletonSurfaceDiagnostic
    (diagnostic : SurfaceDiagnostic) : NonemptyList SurfaceDiagnostic :=
  { head := diagnostic, tail := [] }

def structuralSurfaceDiagnostics
    (diagnostics : NonemptyList StructuralDiagnostic) :
    NonemptyList SurfaceDiagnostic :=
  diagnostics.map .structural

/-- Assemble the certified phase boundary once exact-token root soundness is
available. -/
def parseModuleWithRootSound
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (file : WorkspaceFile) :
    Except (NonemptyList SurfaceDiagnostic) CertifiedParsedModule :=
  match lexing : lexModule file with
  | .error diagnostic =>
      .error (singletonSurfaceDiagnostic (.lexical diagnostic))
  | .ok lexed =>
      let owned := lexer_tokensOwnedBy lexing
      match parsing : executeObservedContextualParse file lexed.tokens owned with
      | .error diagnostic =>
          .error (singletonSurfaceDiagnostic (.parse diagnostic))
      | .ok module =>
          match structural : validateStructure module with
          | .error diagnostics =>
              .error (structuralSurfaceDiagnostics diagnostics)
          | .ok () =>
              have lexical : Lexes file lexed.tokens lexed.comments :=
                (lexer_sound lexing).2
              have parsed : Parses file lexed.tokens module := by
                have sound := executeObservedContextualParse_sound
                  file lexed.tokens owned
                rw [parsing] at sound
                exact sound
              .ok {
                file := file
                tokens := lexed.tokens
                comments := lexed.comments
                module := module
                lexes := lexical
                parses := parsed
                accepted :=
                  (Structure.validateStructure_eq_ok_iff_structurallyAccepts
                    module).mp
                    structural
                locations := parsed.everyLocationValid lexical
                corresponds :=
                  parsed.exactTokenCorrespondence rootSound lexical
              }

/-- Lexical failure remains the unique first-phase report. -/
theorem parseModuleWithRootSound_eq_of_lexicalDiagnostic
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {diagnostic : LexicalDiagnostic}
    (lexing : lexModule file = .error diagnostic) :
    parseModuleWithRootSound rootSound file =
      .error (singletonSurfaceDiagnostic (.lexical diagnostic)) := by
  have requested := lexing
  unfold parseModuleWithRootSound
  split
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
    rfl
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted

/-- Successful lexing exposes exactly the parser and structural branches. -/
theorem parseModuleWithRootSound_eq_of_lexing
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed) :
    parseModuleWithRootSound rootSound file =
      let owned := lexer_tokensOwnedBy lexing
      match parsing : executeObservedContextualParse file lexed.tokens owned with
      | .error diagnostic =>
          .error (singletonSurfaceDiagnostic (.parse diagnostic))
      | .ok module =>
          match structural : validateStructure module with
          | .error diagnostics =>
              .error (structuralSurfaceDiagnostics diagnostics)
          | .ok () =>
              have lexical : Lexes file lexed.tokens lexed.comments :=
                (lexer_sound lexing).2
              have parsed : Parses file lexed.tokens module := by
                have sound := executeObservedContextualParse_sound
                  file lexed.tokens owned
                rw [parsing] at sound
                exact sound
              .ok {
                file := file
                tokens := lexed.tokens
                comments := lexed.comments
                module := module
                lexes := lexical
                parses := parsed
                accepted :=
                  (Structure.validateStructure_eq_ok_iff_structurallyAccepts
                    module).mp structural
                locations := parsed.everyLocationValid lexical
                corresponds :=
                  parsed.exactTokenCorrespondence rootSound lexical
              } := by
  have requested := lexing
  unfold parseModuleWithRootSound
  split
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
  · rename_i actual emitted
    rw [requested] at emitted
    cases emitted
    rfl

theorem parseModuleWithRootSound_eq_of_parseDiagnostic
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {diagnostic : ParseDiagnostic}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .error diagnostic) :
    parseModuleWithRootSound rootSound file =
      .error (singletonSurfaceDiagnostic (.parse diagnostic)) := by
  rw [parseModuleWithRootSound_eq_of_lexing rootSound lexing]
  dsimp only
  split
  · rename_i emitted selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .error emitted := by
      simpa only using selected
    rw [parsing] at selected'
    have same : emitted = diagnostic := by
      exact Except.error.inj selected'.symm
    subst emitted
    rfl
  · rename_i selectedModule selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .ok selectedModule := by
      simpa only using selected
    rw [parsing] at selected'
    contradiction

theorem parseModuleWithRootSound_eq_of_structuralDiagnostics
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {module : ParsedModuleV1}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .ok module)
    {diagnostics : NonemptyList StructuralDiagnostic}
    (structural : validateStructure module = .error diagnostics) :
    parseModuleWithRootSound rootSound file =
      .error (structuralSurfaceDiagnostics diagnostics) := by
  rw [parseModuleWithRootSound_eq_of_lexing rootSound lexing]
  dsimp only
  split
  · rename_i emitted selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .error emitted := by
      simpa only using selected
    rw [parsing] at selected'
    contradiction
  · rename_i selectedModule selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .ok selectedModule := by
      simpa only using selected
    rw [parsing] at selected'
    have moduleEq : selectedModule = module :=
      Except.ok.inj selected'.symm
    subst selectedModule
    split
    · rename_i emitted selectedStructure
      rw [structural] at selectedStructure
      have same : emitted = diagnostics :=
        Except.error.inj selectedStructure.symm
      subst emitted
      rfl
    · rename_i selectedStructure
      rw [structural] at selectedStructure
      contradiction

theorem parseModuleWithRootSound_success
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {lexed : LexedModule}
    (lexing : lexModule file = .ok lexed)
    {module : ParsedModuleV1}
    (parsing : executeObservedContextualParse file lexed.tokens
      (lexer_tokensOwnedBy lexing) = .ok module)
    (structural : validateStructure module = .ok ()) :
    ∃ certified : CertifiedParsedModule,
      parseModuleWithRootSound rootSound file = .ok certified ∧
        certified.file = file ∧
        certified.tokens = lexed.tokens ∧
        certified.comments = lexed.comments ∧
        certified.module = module := by
  rw [parseModuleWithRootSound_eq_of_lexing rootSound lexing]
  dsimp only
  split
  · rename_i emitted selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .error emitted := by
      simpa only using selected
    rw [parsing] at selected'
    contradiction
  · rename_i selectedModule selected
    have selected' : executeObservedContextualParse file lexed.tokens
        (lexer_tokensOwnedBy lexing) = .ok selectedModule := by
      simpa only using selected
    rw [parsing] at selected'
    have moduleEq : selectedModule = module :=
      Except.ok.inj selected'.symm
    subst selectedModule
    split
    · rename_i emitted selectedStructure
      rw [structural] at selectedStructure
      contradiction
    · rename_i selectedStructure
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem parseModuleWithRootSound_success_iff
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (file : WorkspaceFile) :
    (∃ certified, parseModuleWithRootSound rootSound file = .ok certified) ↔
      ∃ (lexed : LexedModule)
          (lexing : lexModule file = .ok lexed)
          (module : ParsedModuleV1)
          (_parsing : executeObservedContextualParse file lexed.tokens
            (lexer_tokensOwnedBy lexing) = .ok module),
        validateStructure module = .ok () := by
  constructor
  · rintro ⟨certified, success⟩
    unfold parseModuleWithRootSound at success
    split at success
    · contradiction
    · rename_i lexed lexing
      dsimp only at success
      split at success
      · contradiction
      · rename_i module parsing
        split at success
        · contradiction
        · rename_i structural
          exact ⟨lexed, lexing, module, parsing, structural⟩
  · rintro ⟨lexed, lexing, module, parsing, structural⟩
    rcases parseModuleWithRootSound_success rootSound lexing parsing
        structural with ⟨certified, success, _fields⟩
    exact ⟨certified, success⟩

theorem parseModuleWithRootSound_failure_iff
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (file : WorkspaceFile) (reported : NonemptyList SurfaceDiagnostic) :
    parseModuleWithRootSound rootSound file = .error reported ↔
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
  constructor
  · intro failure
    unfold parseModuleWithRootSound at failure
    split at failure
    · rename_i diagnostic lexing
      have reportedEq : reported =
          singletonSurfaceDiagnostic (.lexical diagnostic) :=
        Except.error.inj failure.symm
      exact Or.inl ⟨diagnostic, lexing, reportedEq⟩
    · rename_i lexed lexing
      dsimp only at failure
      split at failure
      · rename_i diagnostic parsing
        have reportedEq : reported =
            singletonSurfaceDiagnostic (.parse diagnostic) :=
          Except.error.inj failure.symm
        exact Or.inr (Or.inl
          ⟨lexed, lexing, diagnostic, parsing, reportedEq⟩)
      · rename_i module parsing
        split at failure
        · rename_i diagnostics structural
          have reportedEq : reported =
              structuralSurfaceDiagnostics diagnostics :=
            Except.error.inj failure.symm
          exact Or.inr (Or.inr
            ⟨lexed, lexing, module, parsing, diagnostics,
              structural, reportedEq⟩)
        · contradiction
  · intro phase
    rcases phase with lexical | parserOrStructural
    · rcases lexical with ⟨diagnostic, lexing, reportedEq⟩
      subst reported
      exact parseModuleWithRootSound_eq_of_lexicalDiagnostic
        rootSound lexing
    · rcases parserOrStructural with parser | structural
      · rcases parser with
          ⟨lexed, lexing, diagnostic, parsing, reportedEq⟩
        subst reported
        exact parseModuleWithRootSound_eq_of_parseDiagnostic
          rootSound lexing parsing
      · rcases structural with
          ⟨lexed, lexing, module, parsing, diagnostics,
            validation, reportedEq⟩
        subst reported
        exact parseModuleWithRootSound_eq_of_structuralDiagnostics
          rootSound lexing parsing validation

/-- Two successful evaluations with the same root-soundness certificate return
the same certified module. -/
theorem parseModuleWithRootSound_deterministic
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {first second : CertifiedParsedModule}
    (firstResult : parseModuleWithRootSound rootSound file = .ok first)
    (secondResult : parseModuleWithRootSound rootSound file = .ok second) :
    first = second := by
  rw [firstResult] at secondResult
  exact Except.ok.inj secondResult

/-- Every input either produces a fully certified module or reports a
nonempty diagnostic list. -/
theorem parseModuleWithRootSound_accepted_or_diagnosed
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    (file : WorkspaceFile) :
    (∃ certified, parseModuleWithRootSound rootSound file = .ok certified) ∨
      ∃ reported, parseModuleWithRootSound rootSound file = .error reported := by
  cases result : parseModuleWithRootSound rootSound file with
  | error reported => exact Or.inr ⟨reported, rfl⟩
  | ok certified => exact Or.inl ⟨certified, rfl⟩

/-- A successful certified result and a diagnostic result cannot coexist for
one file. -/
theorem parseModuleWithRootSound_success_not_diagnosed
    (rootSound : RootActionTokenPlanSound sourceRuleTokenPlanLayout)
    {file : WorkspaceFile} {certified : CertifiedParsedModule}
    (success : parseModuleWithRootSound rootSound file = .ok certified) :
    ∀ reported, parseModuleWithRootSound rootSound file ≠ .error reported := by
  intro reported failure
  rw [success] at failure
  contradiction


end Solcore.Surface.Multi
