import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.Staging.Classification

/-!
Whole-program staging for the declarative source semantics.

`Classification` states the occurrence-level rules.  This module lifts those
rules from the legacy checked-function carrier to the forgeable semantic body
and program catalogs.  Static validity and stage validity remain separate
premises: neither judgment is defined by success of an executable frontend
pass.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging

open Frontend
open Frontend.SourceInference

/-- Independent stage classification of one semantic declaration body. -/
inductive BodyDefinitionHasStages (definition : BodyDefinition) : Prop where
  | intro
      {inputScope finalScope : StageScope}
      (sourceOwner : definition.source.owner = definition.owner)
      (graphClosed : OccurrenceGraphClosed definition.source)
      (localIdentities : LocalIdentityOwnership definition.source)
      (inputsStage : FunctionInputsStage definition.source
        definition.returnComptime definition.resultType inputScope)
      (rootsStage : RootsStage definition.source inputScope
        definition.source.roots finalScope) :
      BodyDefinitionHasStages definition

/-- The former checked-function staging carrier and the semantic body carrier
state exactly the same classification facts. -/
theorem bodyDefinitionOfChecked_iff (function : CheckedFunction) :
    BodyDefinitionHasStages (BodyDefinition.ofChecked function) ↔
      FunctionHasStages function := by
  constructor
  · intro staged
    cases staged with
    | intro sourceOwner graphClosed localIdentities inputsStage rootsStage =>
        exact .intro sourceOwner graphClosed localIdentities inputsStage rootsStage
  · intro staged
    cases staged with
    | intro sourceOwner graphClosed localIdentities inputsStage rootsStage =>
        exact .intro sourceOwner graphClosed localIdentities inputsStage rootsStage

/-- Every top-level function body has an independent staging derivation. -/
def FunctionDefinitionHasStages (definition : FunctionDefinition) : Prop :=
  BodyDefinitionHasStages definition.body

/-- Every implementation-method body has an independent staging derivation. -/
def MethodDefinitionHasStages (definition : MethodDefinition) : Prop :=
  BodyDefinitionHasStages definition.body

/-- Complete whole-program source admission: the declaration catalog and
bodies are statically valid, and every executable body is independently
classified for staging. -/
structure ProgramHasStages (program : Program) : Prop where
  staticallyValid : ProgramWellFormed program
  functions : ∀ definition, definition ∈ program.functions →
    FunctionDefinitionHasStages definition
  methods : ∀ definition, definition ∈ program.methods →
    MethodDefinitionHasStages definition

end Solcore.SourceSemantics.Staging
