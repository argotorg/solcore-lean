import Solcore.Frontend.ExpectedLambdaArgumentApplication

/-!
This module recognizes a finite source-group spine around a direct computation
lambda.  The executable returns original subtrees and never constructs a
replacement source expression.
-/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A maximal group spine ending at the original direct lambda.  The span list
is ordered from the outermost group to the innermost group. -/
inductive DirectLambdaGroupSpine :
    Syntax.Expr → List Syntax.SourceSpan → Syntax.Expr → Prop where
  | lambda {span keyword : Syntax.SourceSpan}
      {parameters : Syntax.DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} {body : Syntax.Block} :
      DirectLambdaGroupSpine
        ⟨span, .lambda keyword parameters returnType body⟩ []
        ⟨span, .lambda keyword parameters returnType body⟩
  | group {span : Syntax.SourceSpan} {inner terminal : Syntax.Expr}
      {spans : List Syntax.SourceSpan}
      (child : DirectLambdaGroupSpine inner spans terminal) :
      DirectLambdaGroupSpine ⟨span, .group inner⟩ (span :: spans) terminal

/-- Collect every original group span and return the original terminal lambda. -/
private def peelDirectLambdaGroupSpine?
    : (source : Syntax.Expr) → Option (List Syntax.SourceSpan × Syntax.Expr) :=
  WellFounded.fix (measure sizeOf).wf fun source recurse =>
    match source with
    | terminal@⟨_, .lambda _ _ _ _⟩ => some ([], terminal)
    | ⟨span, .group inner⟩ => do
        let (spans, terminal) ← recurse inner (by decreasing_tactic)
        some (span :: spans, terminal)
    | _ => none

@[simp] private theorem peelDirectLambdaGroupSpine?_lambda
    (span keyword : Syntax.SourceSpan)
    (parameters : Syntax.DelimitedList Syntax.LambdaParameter)
    (returnType : Option Syntax.TypeExpr) (body : Syntax.Block) :
    peelDirectLambdaGroupSpine?
      ⟨span, .lambda keyword parameters returnType body⟩ =
        some ([], ⟨span, .lambda keyword parameters returnType body⟩) := by
  rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq]

@[simp] private theorem peelDirectLambdaGroupSpine?_group
    (span : Syntax.SourceSpan) (inner : Syntax.Expr) :
    peelDirectLambdaGroupSpine? ⟨span, .group inner⟩ = (do
      let (spans, terminal) ← peelDirectLambdaGroupSpine? inner
      some (span :: spans, terminal)) := by
  rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq]

private theorem peelDirectLambdaGroupSpine?_sound
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (accepted : peelDirectLambdaGroupSpine? source = some (spans, terminal)) :
    DirectLambdaGroupSpine source spans terminal := by
  revert spans terminal
  apply (measure sizeOf).wf.induction source
  intro source ih spans terminal accepted
  cases source with
  | mk span kind =>
    cases kind <;>
      try { rw [peelDirectLambdaGroupSpine?, WellFounded.fix_eq] at accepted; cases accepted }
    case lambda keyword parameters returnType body =>
      simp only [peelDirectLambdaGroupSpine?_lambda, Option.some.injEq,
        Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .lambda
    case group inner =>
      cases checked : peelDirectLambdaGroupSpine? inner with
      | none => simp [peelDirectLambdaGroupSpine?_group, checked] at accepted
      | some result =>
        rcases result with ⟨innerSpans, argument⟩
        simp [peelDirectLambdaGroupSpine?_group, checked] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .group (ih inner (by simp_wf; omega) checked)

private theorem peelDirectLambdaGroupSpine?_complete
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan}
    (spine : DirectLambdaGroupSpine source spans terminal) :
    peelDirectLambdaGroupSpine? source = some (spans, terminal) := by
  induction spine with
  | lambda => simp only [peelDirectLambdaGroupSpine?_lambda]
  | group child ih => simp [peelDirectLambdaGroupSpine?_group, ih]

private theorem peelDirectLambdaGroupSpine?_iff
    {source terminal : Syntax.Expr} {spans : List Syntax.SourceSpan} :
    peelDirectLambdaGroupSpine? source = some (spans, terminal) ↔
      DirectLambdaGroupSpine source spans terminal :=
  ⟨peelDirectLambdaGroupSpine?_sound, peelDirectLambdaGroupSpine?_complete⟩

/-- Recognize a singleton call whose argument has at least three groups and ends
at a direct lambda.  Header and body validity are deliberately not inspected. -/
def isThreeOrMoreGroupedExpectedLambdaArgumentApplication : Syntax.Expr → Bool
  | ⟨_, .call _ ⟨_, [grouped]⟩⟩ =>
      match peelDirectLambdaGroupSpine? grouped with
      | some (_ :: _ :: _ :: _, _) => true
      | _ => false
  | _ => false

/-- Exact source evidence for three-or-more transparent groups around the expected
lambda.  All group spans remain in the spine evidence. -/
inductive ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) :
    Syntax.Expr → Core.Expr → Core.Ty → Prop where
  | application {span argumentsSpan first second third : Syntax.SourceSpan}
      {rest : List Syntax.SourceSpan} {callee grouped argument : Syntax.Expr}
      {functionCore argumentCore : Core.Expr} {parameterType resultType : Core.Ty}
      (spine : DirectLambdaGroupSpine grouped (first :: second :: third :: rest) argument)
      (calleeElaboration : RecursiveLocalComputationElaborates inputs.names inputs.context
        callee functionCore (.function parameterType resultType))
      (argumentElaboration : ExpectedComputationLambdaElaborates
        RecursiveLocalComputationElaborates types owner inputs argument argumentCore parameterType) :
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates types owner inputs
        ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩
        (.apply functionCore argumentCore) resultType

/-- Unwrap the finite spine, require at least three groups, infer the original
callee, and check the original terminal lambda at its parameter type. -/
def elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?
    (types : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  match source with
  | ⟨_, .call callee ⟨_, [grouped]⟩⟩ => do
      let (spans, argument) ← peelDirectLambdaGroupSpine? grouped
      match spans with
      | _ :: _ :: _ :: _ =>
          let (functionCore, functionType) ←
            elaborateRecursiveLocalComputation? inputs.names inputs.context callee
          match functionType with
          | .function parameterType resultType => do
              let argumentCore ← elaborateExpectedComputationLambda?
                elaborateRecursiveLocalComputation? types owner inputs argument parameterType
              some (.apply functionCore argumentCore, resultType)
          | _ => none
      | _ => none
  | _ => none

/-- The executable accepts exactly the independent finite-spine evidence. -/
theorem elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source =
        some (core, type) ↔
      ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro accepted
    cases source with
    | mk span kind =>
      cases kind <;>
        try { simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted }
      case call callee arguments =>
        cases arguments with
        | mk argumentsSpan elements =>
          cases elements with
          | nil => simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted
          | cons grouped tail =>
            cases tail with
            | cons secondArgument restArguments =>
                simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?] at accepted
            | nil =>
              cases spineChecked : peelDirectLambdaGroupSpine? grouped with
              | none =>
                  simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                    at accepted
              | some result =>
                rcases result with ⟨spans, argument⟩
                cases spans with
                | nil =>
                    simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                      at accepted
                | cons first tailSpans =>
                  cases tailSpans with
                  | nil =>
                      simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                        at accepted
                  | cons second rest =>
                    cases rest with
                    | nil =>
                        simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?, spineChecked]
                          at accepted
                    | cons third tail =>
                      have spine := peelDirectLambdaGroupSpine?_iff.mp spineChecked
                      cases calleeChecked : elaborateRecursiveLocalComputation?
                          inputs.names inputs.context callee with
                      | none =>
                          simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                            spineChecked, calleeChecked] at accepted
                      | some calleeResult =>
                        rcases calleeResult with ⟨functionCore, functionType⟩
                        have calleeElaboration :=
                          elaborateRecursiveLocalComputation?_iff.mp calleeChecked
                        cases functionType <;>
                          try { simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                            spineChecked, calleeChecked] at accepted }
                        case function parameterType resultType =>
                          cases argumentChecked : elaborateExpectedComputationLambda?
                              elaborateRecursiveLocalComputation? types owner inputs argument
                                parameterType with
                          | none =>
                              simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                                spineChecked, calleeChecked, argumentChecked] at accepted
                          | some argumentCore =>
                            have argumentElaboration :=
                              (elaborateExpectedComputationLambda?_iff
                                (@elaborateRecursiveLocalComputation?_iff)).mp argumentChecked
                            simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
                              spineChecked, calleeChecked, argumentChecked] at accepted
                            rcases accepted with ⟨rfl, rfl⟩
                            exact .application spine calleeElaboration argumentElaboration
  · intro elaboration
    cases elaboration with
    | application spine calleeElaboration argumentElaboration =>
      simp [elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?,
        peelDirectLambdaGroupSpine?_iff.mpr spine,
        elaborateRecursiveLocalComputation?_iff.mpr calleeElaboration,
        (elaborateExpectedComputationLambda?_iff
          (@elaborateRecursiveLocalComputation?_iff)).mpr argumentElaboration]

/-- Executable failure is exactly absence of finite-spine application evidence. -/
theorem elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} :
    elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source = none ↔
      ¬ ∃ core type, ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
        types owner inputs source core type := by
  constructor
  · intro rejected ⟨core, type, elaboration⟩
    have accepted := elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mpr elaboration
    rw [rejected] at accepted
    cases accepted
  · intro absent
    cases accepted :
        elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication? types owner inputs source with
    | none => rfl
    | some result =>
        rcases result with ⟨core, type⟩
        exact False.elim (absent ⟨core, type,
          elaborateThreeOrMoreGroupedExpectedLambdaArgumentApplication?_iff.mp accepted⟩)

/-- Every finite-spine elaboration has the inferred Core result type. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    Core.HasType inputs.context.values core type := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      exact .apply calleeElaboration.core_hasType
        (argumentElaboration.core_hasType
          (@RecursiveLocalComputationElaborates.core_hasType))

/-- Successful evidence retains every source span and both child derivations. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.provenance
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    ∃ span argumentsSpan first second third rest callee grouped argument
        functionCore argumentCore parameterType,
      source = ⟨span, .call callee ⟨argumentsSpan, [grouped]⟩⟩ ∧
      DirectLambdaGroupSpine grouped (first :: second :: third :: rest) argument ∧
      RecursiveLocalComputationElaborates inputs.names inputs.context callee functionCore
        (.function parameterType type) ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates
        types owner inputs argument argumentCore parameterType ∧
      core = .apply functionCore argumentCore := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, spine,
        calleeElaboration, argumentElaboration, rfl⟩

/-- Every successful finite-spine elaboration is selected by the classifier. -/
theorem ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates.classified
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ThreeOrMoreGroupedExpectedLambdaArgumentApplicationElaborates
      types owner inputs source core type) :
    isThreeOrMoreGroupedExpectedLambdaArgumentApplication source = true := by
  cases elaboration with
  | application spine calleeElaboration argumentElaboration =>
      simp [isThreeOrMoreGroupedExpectedLambdaArgumentApplication,
        peelDirectLambdaGroupSpine?_complete spine]

end Solcore.Frontend
