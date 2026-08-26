import Solcore.Surface.Multi.ExactTokenDeclaration
import Solcore.Surface.Multi.ExactTokenProperties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The complete source-sensitive retained-token plan for a parsed module. -/
def parsedModuleTokenPlan? : ParsedModuleV1 → Option TokenPlan :=
  declarationModulePlan?

/-- Executable exact correspondence between one source file, its lexical
output, and one parsed module. Structurally impossible AST shapes are rejected
by `parsedModuleTokenPlan?` before token matching. -/
def exactTokenCorrespondence
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) : Bool :=
  exactTokenCorrespondenceWith parsedModuleTokenPlan?
    file tokens comments module

/-- Proposition exposed by the executable exact-correspondence check. -/
def ExactTokenCorrespondence
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) : Prop :=
  ExactTokenCorrespondenceWith parsedModuleTokenPlan?
    file tokens comments module

@[simp] theorem parsedModuleTokenPlan?_eq
    (module : ParsedModuleV1) :
    parsedModuleTokenPlan? module = declarationModulePlan? module := by
  rfl

@[simp] theorem exactTokenCorrespondence_eq_with
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) :
    exactTokenCorrespondence file tokens comments module =
      exactTokenCorrespondenceWith parsedModuleTokenPlan?
        file tokens comments module := by
  rfl

/-- Public logical view of the executable exact-correspondence check. This is
only the lexical, source-identity, plan-generation, anchoring, and retained-token
matching contract; it makes no claim relating this check to `Parses`. -/
@[simp] theorem exactTokenCorrespondence_eq_true_iff
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) :
    ExactTokenCorrespondence file tokens comments module ↔
      ExactLexicalOutput file tokens comments ∧
      module.span = SourceSpan.fullFile file ∧
      module.payload.source = file.id ∧
      ∃ plan, parsedModuleTokenPlan? module = some plan ∧
        plan.WellAnchored ∧ TokenSlot.ListMatches plan.slots tokens := by
  exact exactTokenCorrespondenceWith_eq_true_iff
    parsedModuleTokenPlan? file tokens comments module

end Solcore.Surface.Multi
