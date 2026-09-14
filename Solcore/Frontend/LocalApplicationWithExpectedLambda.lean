import Solcore.Frontend.ExpectedLambdaArgumentApplication

/-!
One opt-in singleton-application entry selects direct expected-lambda checking
or unchanged ordinary recursive checking solely from the original source shape.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Recognize exactly a singleton call whose sole argument is a direct lambda. -/
def isDirectExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [⟨_, .lambda _ _ _ _⟩]⟩⟩ => true
  | _ => false

/-- Source-disjoint evidence for the expected-lambda and ordinary application
paths. Both constructors retain the complete original singleton call. -/
inductive LocalApplicationWithExpectedLambdaElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | expected {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
      (boundary : isDirectExpectedLambdaArgumentApplication source = true)
      (elaboration : ExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type) :
      LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type
  | ordinary {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {core : Core.Expr} {type : Core.Ty}
      (boundary : isDirectExpectedLambdaArgumentApplication
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = false)
      (elaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ core type) :
      LocalApplicationWithExpectedLambdaElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ core type

/-- Dispatch before checking. Failure in the recognized lambda branch never
falls through to the ordinary recursive checker. -/
def elaborateLocalApplicationWithExpectedLambda?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call _ ⟨_, [_]⟩⟩ =>
      if isDirectExpectedLambdaArgumentApplication source then
        elaborateExpectedLambdaArgumentApplication? types owner inputs source
      else elaborateRecursiveLocalComputation? inputs.names inputs.context source
  | _ => none

/-- Exact correspondence for source-only disjoint dispatch. -/
theorem elaborateLocalApplicationWithExpectedLambda?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = some (core, type) ↔
      LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;> try { simp [elaborateLocalApplicationWithExpectedLambda?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateLocalApplicationWithExpectedLambda?] at accepted
          | cons argument tail =>
            cases tail with
            | cons second rest => simp [elaborateLocalApplicationWithExpectedLambda?] at accepted
            | nil =>
              simp only [elaborateLocalApplicationWithExpectedLambda?] at accepted
              split at accepted
              · rename_i boundary
                exact .expected boundary
                  (elaborateExpectedLambdaArgumentApplication?_iff.mp accepted)
              · rename_i boundary
                have boundaryFalse : isDirectExpectedLambdaArgumentApplication
                    ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ = false := by
                  cases equality : isDirectExpectedLambdaArgumentApplication
                      ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ <;> simp_all
                exact .ordinary boundaryFalse
                  (elaborateRecursiveLocalComputation?_iff.mp accepted)
  · intro elaboration
    cases elaboration with
    | expected boundary elaboration =>
        cases elaboration with
        | application calleeElaboration argumentElaboration =>
          simp [elaborateLocalApplicationWithExpectedLambda?, boundary,
            elaborateExpectedLambdaArgumentApplication?_iff.mpr
              (.application calleeElaboration argumentElaboration)]
    | ordinary boundary elaboration =>
        simp [elaborateLocalApplicationWithExpectedLambda?, boundary,
          elaborateRecursiveLocalComputation?_iff.mpr elaboration]

/-- Rejection is exact absence of both source-disjoint application paths. -/
theorem elaborateLocalApplicationWithExpectedLambda?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateLocalApplicationWithExpectedLambda? types owner inputs source = none ↔
      ¬ ∃ core type,
        LocalApplicationWithExpectedLambdaElaborates types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateLocalApplicationWithExpectedLambda?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted : elaborateLocalApplicationWithExpectedLambda? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateLocalApplicationWithExpectedLambda?_iff.mp accepted⟩)

/-- Either selected path preserves the exact inferred Core type. -/
theorem LocalApplicationWithExpectedLambdaElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithExpectedLambdaElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | expected boundary child => exact child.core_hasType
  | ordinary boundary child => exact child.core_hasType

/-- Inversion exposes the classifier result and the complete selected child. -/
theorem LocalApplicationWithExpectedLambdaElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalApplicationWithExpectedLambdaElaborates
      types owner inputs source core type) :
    (isDirectExpectedLambdaArgumentApplication source = true ∧
      ExpectedLambdaArgumentApplicationElaborates types owner inputs source core type) ∨
    (isDirectExpectedLambdaArgumentApplication source = false ∧
      ∃ span argumentsSpan callee argument,
        source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ ∧
        RecursiveLocalComputationElaborates inputs.names inputs.context source core type) := by
  cases elaboration with
  | expected boundary child => exact .inl ⟨boundary, child⟩
  | ordinary boundary child => exact .inr ⟨boundary, _, _, _, _, rfl, child⟩

end Solcore.Frontend
