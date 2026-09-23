import Solcore.Syntax.Parser.Function
import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties
import Solcore.Syntax.DeclarativeImplDefaultMarkerExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.DeclarativeImplHeadArgumentsExactnessProperties
import Solcore.Syntax.DeclarativeImplMethodExactnessProperties
import Solcore.Syntax.Parser.FunctionDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.DeclarativeImplBodyOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.DeclarativeImplBodyExactnessProperties
import Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeImplDeclarationExactnessProperties
import Solcore.Syntax.Parser.FunctionProperties
import Solcore.Syntax.CallableDeclarationValidity
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.GenericParametersTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.Parser.WhereClauseTotalityProperties
import Solcore.Syntax.Parser.FunctionDeclSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/- Proof-visible implementation-body parser components. -/
namespace ImplInternals

/-- Require at least one implementation head argument. -/
def requireImplArguments (values : DelimitedList TypeExpr) :
    Parser (NonemptyDelimitedList TypeExpr) :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse one function member of an implementation body. -/
def implMethod : Parser ImplMethod := do
  let declaration ← functionDecl .module
  pure {
    span := declaration.span
    value := { leadingComments := [], declaration }
  }

/-- The brace range and methods accumulated by implementation-body parsing. -/
structure ImplBody where
  span : SourceSpan
  methods : List ImplMethod

/-- Close an implementation body and restore source order. -/
def closeImplBody (opening : Token)
    (methodsRev : List ImplMethod) : Parser ImplBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    methods := methodsRev.reverse
  }

/-- Parse implementation methods with explicit fuel and progress checks. -/
def implMethods (opening : Token) :
    Nat → List ImplMethod → State → Reply ImplBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, methodsRev, state =>
      if isSymbol state .rightBrace then
        closeImplBody opening methodsRev state
      else if isKeyword state .functionKw then
        let before := state.cursor
        match implMethod state with
        | .ok value next =>
            if next.cursor > before then
              implMethods opening fuel (value :: methodsRev) next
            else
              .invariant (.noProgress .topLevel next.currentSpan)
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        rejectAt state {
          head := .keyword .functionKw
          tail := [.symbol .rightBrace]
        } .topItem

/-- Parse a complete brace-delimited implementation body. -/
def implBody : Parser ImplBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      implMethods opening (next.remainingCount + 1) [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/-- Parse an optional leading `default` marker. -/
def implDefaultMarker : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state .defaultKw then
    pure (some (← keyword .defaultKw .topItem).span)
  else
    pure none

/-- Parse the declaration suffix following its optional default marker. -/
def implDeclAfterDefault (defaultMarker : Option SourceSpan) :
    Parser ImplDecl := do
  let marker ← contextual .impl .topItem
  let genericParameters ← optionalGenericParameters
  let traitName ← identifier .topItem
  let arguments ← delimited .less .greater false typeExpr
    .typeExpr .topLevel
  let headArguments ← requireImplArguments arguments
  let whereClause ← whereClause
  let body ← implBody
  let startSpan := defaultMarker.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      defaultMarker
      genericParameters
      traitName
      headArguments
      whereClause
      bodySpan := body.span
      methods := body.methods
    }
  }

end ImplInternals

open ImplInternals

/-- Parse a canonical optional-default trait implementation. -/
def implDecl : Parser ImplDecl := do
  let defaultMarker ← implDefaultMarker
  implDeclAfterDefault defaultMarker

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplHeadArgumentsOrdinaryRejectionSoundnessProperties`
-/

/-! Exact ordinary rejection for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- The nonempty refinement is pure or invariant and never rejects. -/
theorem requireImplArguments_ne_reject
    (values : DelimitedList TypeExpr) (input rejected : State)
    (failure : Failure) :
    requireImplArguments values input ≠ .reject failure rejected := by
  unfold requireImplArguments
  cases values.elements <;> simp [pure]

/-- Every executable head-list rejection comes from the committed delimited
stage and retains its exact rejected remainder. -/
theorem implHeadArguments_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject failure rejected) :
    DeclarativeGrammar.ImplHeadArgumentsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  exact delimited_reject_sound .less .greater false typeExpr
    DeclarativeGrammar.TypeExprOrdinaryParses
    DeclarativeGrammar.TypeExprRejects .typeExpr .topLevel
    typeExpr_ordinaryOutcome_sound.1 typeExpr_ordinaryOutcome_sound.2 result

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplHeadSoundnessProperties`
-/

/-! Parser-independent soundness for implementation declaration head leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/-- Optional `default` parsing cannot erase an incoming diagnostic. -/
theorem implDefaultMarker_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .topItem)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Optional `default` success preserves keyword priority and exact state. -/
theorem implDefaultMarker_success_sound {input next : State}
    {marker : Option SourceSpan}
    (result : implDefaultMarker input = .ok marker next) :
    DeclarativeGrammar.OptionalImplDefaultMarkerParses
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold implDefaultMarker getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    cases markerResult : keyword .defaultKw .topItem input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses .defaultKw .topItem markerResult)
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false .defaultKw absent)

/-- Requiring head arguments cannot erase diagnostics on a successful branch. -/
theorem requireImplArguments_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList TypeExpr) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireImplArguments values) := by
  unfold requireImplArguments
  cases values.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Requiring nonempty head arguments preserves state, span, and source order. -/
theorem requireImplArguments_success_shape
    {values : DelimitedList TypeExpr} {input next : State}
    {arguments : NonemptyDelimitedList TypeExpr}
    (result : requireImplArguments values input = .ok arguments next) :
    next = input ∧ arguments.span = values.span ∧
      arguments.elements.toList = values.elements := by
  unfold requireImplArguments at result
  cases elements : values.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- The delimited and nonempty stages yield exact implementation arguments. -/
theorem implHeadArguments_success_sound
    {input afterValues next : State} {values : DelimitedList TypeExpr}
    {arguments : NonemptyDelimitedList TypeExpr}
    (valuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok values afterValues)
    (argumentsResult : requireImplArguments values afterValues =
      .ok arguments next) :
    DeclarativeGrammar.ImplHeadArgumentsParses input.declarativeRemainder
      arguments next.declarativeRemainder := by
  have valuesGrammar := delimited_nonempty_trailing_success_sound
    .less .greater typeExpr DeclarativeGrammar.TypeExprParses
    .typeExpr .topLevel typeExpr_success_sound typeExpr_preservesTokenWindow
    valuesResult
  have shape := requireImplArguments_success_shape argumentsResult
  unfold DeclarativeGrammar.ImplHeadArgumentsParses
  rw [shape.1]
  simpa only [shape.2.1, shape.2.2] using valuesGrammar

end ImplInternals

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDefaultMarkerOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for the optional `default` marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Every optional-default success follows its exact prioritized grammar. -/
theorem implDefaultMarker_success_ordinaryOutcome_sound
    {input output : State} {marker : Option SourceSpan}
    (result : implDefaultMarker input = .ok marker output) :
    DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      input.declarativeRemainder marker output.declarativeRemainder :=
  implDefaultMarker_success_sound result

/-- The guarded optional-default parser cannot reject. -/
theorem implDefaultMarker_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implDefaultMarker input = .reject failure rejected) :
    DeclarativeGrammar.OptionalImplDefaultMarkerRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold implDefaultMarker getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .defaultKw .topItem present with
      ⟨marker, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input .defaultKw = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package optional-default success and impossible rejection. -/
theorem implDefaultMarker_ordinaryOutcome_sound :
    (∀ {input output : State} {marker : Option SourceSpan},
      implDefaultMarker input = .ok marker output →
        DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
          input.declarativeRemainder marker output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implDefaultMarker input = .reject failure rejected →
        DeclarativeGrammar.OptionalImplDefaultMarkerRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implDefaultMarker_success_ordinaryOutcome_sound,
    implDefaultMarker_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional-default outcomes. -/
theorem implDefaultMarker_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      DeclarativeGrammar.OptionalImplDefaultMarkerRejects :=
  DeclarativeGrammar.optionalImplDefaultMarkerDeterministicOutcomeSpec

/-- Re-export exact optional-default values and rejection endpoints. -/
theorem implDefaultMarker_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
      DeclarativeGrammar.OptionalImplDefaultMarkerRejects :=
  DeclarativeGrammar.optionalImplDefaultMarkerExactOutcomeSpec

/-- Two successful optional-default parses have the same marker and final
declarative remainder. -/
theorem implDefaultMarker_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option SourceSpan}
    (leftResult : implDefaultMarker input = .ok left leftOutput)
    (rightResult : implDefaultMarker input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses.result_unique
    (implDefaultMarker_success_ordinaryOutcome_sound leftResult)
    (implDefaultMarker_success_ordinaryOutcome_sound rightResult)

/-- Two impossible optional-default rejections have the same declarative
endpoint. -/
theorem implDefaultMarker_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDefaultMarker input = .reject leftFailure leftOutput)
    (rightResult : implDefaultMarker input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalImplDefaultMarkerRejects.output_unique
    (implDefaultMarker_reject_ordinaryOutcome_sound leftResult)
    (implDefaultMarker_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplHeadArgumentsOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- The executable delimited stage followed by its pure nonempty refinement
has the exact broad implementation-head argument grammar. -/
theorem implHeadArguments_success_ordinaryOutcome_sound
    {input afterValues output : State}
    {values : DelimitedList TypeExpr}
    {arguments : NonemptyDelimitedList TypeExpr}
    (valuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok values afterValues)
    (argumentsResult : requireImplArguments values afterValues =
      .ok arguments output) :
    DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      input.declarativeRemainder arguments output.declarativeRemainder := by
  have valuesParsed := delimited_nonempty_trailing_success_sound
    .less .greater typeExpr DeclarativeGrammar.TypeExprOrdinaryParses
    .typeExpr .topLevel typeExpr_ordinaryOutcome_sound.1
      typeExpr_preservesTokenWindow valuesResult
  have shape := requireImplArguments_success_shape argumentsResult
  unfold DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
  rw [shape.1]
  simpa only [shape.2.1, shape.2.2] using valuesParsed

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplHeadArgumentsOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete broad ordinary outcomes for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package the executable delimited/refinement success and the only ordinary
rejection stage. -/
theorem implHeadArguments_ordinaryOutcome_sound :
    (∀ {input afterValues output : State}
      {values : DelimitedList TypeExpr}
      {arguments : NonemptyDelimitedList TypeExpr},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .ok values afterValues →
        requireImplArguments values afterValues = .ok arguments output →
          DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
            input.declarativeRemainder arguments
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      delimited .less .greater false typeExpr .typeExpr .topLevel input =
          .reject failure rejected →
        DeclarativeGrammar.ImplHeadArgumentsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implHeadArguments_success_ordinaryOutcome_sound,
    implHeadArguments_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation head argument
outcomes. -/
theorem implHeadArguments_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      DeclarativeGrammar.ImplHeadArgumentsRejects :=
  DeclarativeGrammar.implHeadArgumentsDeterministicOutcomeSpec

/-- Re-export exact implementation head-argument values and rejection
endpoints. -/
theorem implHeadArguments_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      DeclarativeGrammar.ImplHeadArgumentsRejects :=
  DeclarativeGrammar.implHeadArgumentsExactOutcomeSpec

/-- Two successful executable head-argument pipelines have the same refined
arguments and final declarative remainder. -/
theorem implHeadArguments_success_result_unique
    {input leftAfterValues rightAfterValues leftOutput rightOutput : State}
    {leftValues rightValues : DelimitedList TypeExpr}
    {left right : NonemptyDelimitedList TypeExpr}
    (leftValuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok leftValues leftAfterValues)
    (leftArgumentsResult : requireImplArguments leftValues leftAfterValues =
      .ok left leftOutput)
    (rightValuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok rightValues rightAfterValues)
    (rightArgumentsResult :
      requireImplArguments rightValues rightAfterValues =
        .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses.result_unique
    (implHeadArguments_success_ordinaryOutcome_sound leftValuesResult
      leftArgumentsResult)
    (implHeadArguments_success_ordinaryOutcome_sound rightValuesResult
      rightArgumentsResult)

/-- Two rejected executable head-argument parses have the same declarative
endpoint. -/
theorem implHeadArguments_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject leftFailure leftOutput)
    (rightResult : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplHeadArgumentsRejects.output_unique
    (implHeadArguments_reject_ordinaryOutcome_sound leftResult)
    (implHeadArguments_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplMethodOrdinaryOutcomeSoundnessProperties`
-/

/-! Executable ordinary outcomes for one implementation method wrapper. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ImplInternals

private theorem implMethodOrdinaryOutcome_bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every successful method is an ordinary module-position function wrapped
with its exact span and empty parser-time leading comments. -/
theorem implMethod_success_ordinaryOutcome_sound
    {input output : State} {method : ImplMethod}
    (result : implMethod input = .ok method output) :
    DeclarativeGrammar.ImplMethodOrdinaryParses
      input.declarativeRemainder method output.declarativeRemainder := by
  unfold implMethod at result
  rcases implMethodOrdinaryOutcome_bind_ok_components result with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  exact .parsed
    (functionDecl_success_ordinaryOutcome_sound .module declarationResult)

/-- Every method rejection is exactly its nested module-position function
declaration rejection; the pure wrapper cannot reject. -/
theorem implMethod_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implMethod input = .reject failure rejected) :
    DeclarativeGrammar.ImplMethodRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold implMethod at result
  cases declarationResult : functionDecl .module input with
  | invariant error => simp [bind, declarationResult] at result
  | ok declaration afterDeclaration =>
      simp [bind, declarationResult, pure] at result
  | reject declarationFailure declarationRejected =>
      simp only [bind, declarationResult] at result
      cases result
      exact .declarationRejected
        (functionDecl_reject_ordinaryOutcome_sound .module declarationResult)

/-- Package exact executable implementation-method success and rejection. -/
theorem implMethod_ordinaryOutcome_sound :
    (∀ {input output : State} {method : ImplMethod},
      implMethod input = .ok method output →
        DeclarativeGrammar.ImplMethodOrdinaryParses
          input.declarativeRemainder method output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implMethod input = .reject failure rejected →
        DeclarativeGrammar.ImplMethodRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨implMethod_success_ordinaryOutcome_sound,
    implMethod_reject_ordinaryOutcome_sound⟩

/-- Re-export the deterministic parser-independent method contract. -/
theorem implMethod_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodDeterministicOutcomeSpec

/-- Re-export exact implementation-method outcomes from an exact isolated
function body. -/
theorem implMethod_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-method contract. -/
theorem implMethod_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects :=
  DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- With an exact isolated body, two executable implementation methods have
the same AST and final declarative remainder. -/
theorem implMethod_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplMethod}
    (leftResult : implMethod input = .ok left leftOutput)
    (rightResult : implMethod input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplMethodOrdinaryParses.result_unique_of_exact_body
    bodyOutcomes (implMethod_success_ordinaryOutcome_sound leftResult)
    (implMethod_success_ordinaryOutcome_sound rightResult)

/-- With an exact isolated body, two implementation-method rejections have
the same declarative endpoint. -/
theorem implMethod_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implMethod input = .reject leftFailure leftOutput)
    (rightResult : implMethod input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplMethodRejects.output_unique_of_exact_body
    bodyOutcomes (implMethod_reject_ordinaryOutcome_sound leftResult)
    (implMethod_reject_ordinaryOutcome_sound rightResult)

end ImplInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplBodyOrdinaryRejectionSoundnessProperties`
-/

/-! Exact broad ordinary rejection for the custom implementation-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem implBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
    {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.ImplMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem implMethods_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel methodsRev input failure rejected,
      implMethods opening fuel methodsRev input = .reject failure rejected →
      DeclarativeGrammar.ImplMethodTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input failure rejected result
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input failure rejected result
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
              closingPresent with ⟨closing, closingResult⟩
          unfold closeImplBody at result
          simp [bind, closingResult, pure] at result
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false =>
              simp only [functionPresent, Bool.false_eq_true, if_false]
                at result
              unfold rejectAt at result
              cases result
              exact .unexpected
                (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                  closingPresent)
                (keywordAbsentAt_of_isKeyword_eq_false .functionKw
                  functionPresent)
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject methodFailure methodRejected =>
                  simp only [methodResult] at result
                  cases result
                  exact .methodRejected
                    (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                      closingPresent)
                    (implBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
                      functionPresent)
                    (implMethod_reject_ordinaryOutcome_sound methodResult)
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterRejected
                      (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                        closingPresent)
                      (implBodyOrdinaryRejection_functionPresent_of_isKeyword_eq_true
                        functionPresent)
                      (implMethod_success_ordinaryOutcome_sound methodResult)
                      progress
                      (inductionHypothesis (method :: methodsRev) afterMethod
                        failure rejected result)
                  · simp [progress] at result

/-- Every executable implementation-body rejection records opening failure or
the exact first rejection of its prioritized broad method tail. -/
theorem implBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implBody input = .reject failure rejected) :
    DeclarativeGrammar.ImplBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have rejectedEq := symbol_reject_state_eq .leftBrace .topItem
        openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .tailRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        (implMethods_reject_ordinaryOutcome_sound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
            result)

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplBodyOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for the custom implementation-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem implBodyOrdinarySuccess_bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

private theorem implBodyOrdinarySuccess_functionPresent_of_isKeyword_eq_true
    {input : State}
    (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.ImplMethodStartAt input.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .functionKw .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses .functionKw .topItem result).1⟩

private theorem closeImplBody_success_ordinary_sound (opening : Token)
    (methodsRev : List ImplMethod) {input output : State} {body : ImplBody}
    (result : closeImplBody opening methodsRev input = .ok body output) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan output.declarativeRemainder := by
  unfold closeImplBody at result
  rcases implBodyOrdinarySuccess_bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

private theorem implMethods_success_ordinary_sound_strong
    (opening : Token) :
    ∀ fuel methodsRev input body output,
      implMethods opening fuel methodsRev input = .ok body output →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.ImplMethodTailOrdinaryParses
          input.declarativeRemainder methods closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body output result
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body output result
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeImplBody_success_ordinary_sound opening methodsRev
              result with ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases functionPresent : isKeyword input .functionKw with
          | false => simp [functionPresent, rejectAt] at result
          | true =>
              simp only [functionPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body output result with
                      ⟨methods, closingSpan, bodyEq, tailParsed⟩
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        (implBodyOrdinarySuccess_functionPresent_of_isKeyword_eq_true
                          functionPresent)
                        (implMethod_success_ordinaryOutcome_sound methodResult)
                        progress tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp [progress] at result

/-- Every executable implementation-body success records the exact brace span,
forward ordinary methods, and final remainder without a diagnostic premise. -/
theorem implBody_success_ordinaryOutcome_sound
    {input output : State} {body : ImplBody}
    (result : implBody input = .ok body output) :
    DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      input.declarativeRemainder (body.span, body.methods)
        output.declarativeRemainder := by
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases implMethods_success_ordinary_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
        with ⟨methods, closingSpan, bodyEq, methodsParsed⟩
      rw [bodyEq]
      exact .parsed opening.span closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        methodsParsed

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplBodyOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for implementation bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- Package executable implementation-body success and exact rejection. -/
theorem implBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : ImplBody},
      implBody input = .ok body output →
        DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.methods)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implBody input = .reject failure rejected →
        DeclarativeGrammar.ImplBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implBody_success_ordinaryOutcome_sound,
    implBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive implementation-body outcomes. -/
theorem implBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyDeterministicOutcomeSpec

/-- Re-export exact implementation-body outcomes from exact method
outcomes. -/
theorem implBody_exactOutcomeSpec_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfMethod methodOutcomes

/-- Re-export exact implementation-body outcomes from an exact isolated
method body. -/
theorem implBody_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-body contract. -/
theorem implBody_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects :=
  DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- Exact method outcomes make two successful executable implementation
bodies agree on their parser value and final declarative remainder. -/
theorem implBody_success_result_unique_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects)
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases (implBody_exactOutcomeSpec_of_method methodOutcomes)
      |>.successResultUnique
        (implBody_success_ordinaryOutcome_sound leftResult)
        (implBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Exact method outcomes make two executable implementation-body
rejections agree on their declarative endpoint. -/
theorem implBody_reject_output_unique_of_method
    (methodOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplMethodOrdinaryParses
      DeclarativeGrammar.ImplMethodRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (implBody_exactOutcomeSpec_of_method methodOutcomes).rejectOutputUnique
    (implBody_reject_ordinaryOutcome_sound leftResult)
    (implBody_reject_ordinaryOutcome_sound rightResult)

/-- An exact isolated method body makes two successful executable
implementation bodies agree. -/
theorem implBody_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_success_result_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- An exact isolated method body makes two executable implementation-body
rejections agree. -/
theorem implBody_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_reject_output_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two successful executable
implementation bodies agree. -/
theorem implBody_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State} {left right : ImplBody}
    (leftResult : implBody input = .ok left leftOutput)
    (rightResult : implBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_success_result_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two executable
implementation-body rejections agree. -/
theorem implBody_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implBody input = .reject leftFailure leftOutput)
    (rightResult : implBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implBody_reject_output_unique_of_method
    (DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDeclarationOrdinaryRejectionSoundnessProperties`
-/

/-! Exact broad ordinary rejection for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every executable implementation rejection occurs after its infallible
default prefix at the first of marker, generics, name, arguments, where, or
broad body. -/
theorem implDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implDecl input = .reject failure rejected) :
    DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold implDecl at result
  cases defaultResult : ImplInternals.implDefaultMarker input with
  | invariant error => simp [bind, defaultResult] at result
  | reject defaultFailure defaultRejected =>
      exact False.elim
        (ImplInternals.implDefaultMarker_reject_ordinaryOutcome_sound
          defaultResult)
  | ok defaultMarker afterDefault =>
      simp only [bind, defaultResult] at result
      have defaultParsed :=
        ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
          defaultResult
      unfold ImplInternals.implDeclAfterDefault at result
      cases markerResult : contextual .impl .topItem afterDefault with
      | invariant error => simp [bind, markerResult] at result
      | reject markerFailure markerRejected =>
          have markerRejectedEq := contextual_reject_state_eq .impl .topItem
            markerResult
          subst markerRejected
          simp only [bind, markerResult] at result
          cases result
          exact .markerMissing defaultParsed
            (contextual_reject_tokenKindAbsentAt .impl .topItem markerResult)
      | ok marker afterMarker =>
          simp only [bind, markerResult] at result
          have markerParsed := contextual_success_exactTokenParses .impl
            .topItem markerResult
          cases genericsResult : optionalGenericParameters afterMarker with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected defaultParsed marker.span markerParsed
                (optionalGenericParameters_ordinaryOutcome_sound.2
                  genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases nameResult : identifier .topItem afterGenerics with
              | invariant error => simp [nameResult] at result
              | reject nameFailure nameRejected =>
                  simp only [nameResult] at result
                  cases result
                  exact .nameRejected defaultParsed marker.span markerParsed
                    genericsParsed
                    (identifier_reject_sound .topItem nameResult)
              | ok traitName afterName =>
                  simp only [nameResult] at result
                  have nameParsed := identifier_success_sound .topItem
                    nameResult
                  cases valuesResult : delimited .less .greater false typeExpr
                      .typeExpr .topLevel afterName with
                  | invariant error => simp [valuesResult] at result
                  | reject valuesFailure valuesRejected =>
                      simp only [valuesResult] at result
                      cases result
                      exact .argumentsRejected defaultParsed marker.span
                        markerParsed genericsParsed nameParsed
                        (ImplInternals.implHeadArguments_reject_ordinaryOutcome_sound
                            valuesResult)
                  | ok values afterValues =>
                      simp only [valuesResult] at result
                      cases argumentsResult :
                          ImplInternals.requireImplArguments values afterValues
                          with
                      | invariant error => simp [argumentsResult] at result
                      | reject argumentsFailure argumentsRejected =>
                          exact False.elim
                            (ImplInternals.requireImplArguments_ne_reject
                              values afterValues argumentsRejected
                                argumentsFailure argumentsResult)
                      | ok headArguments afterArguments =>
                          simp only [argumentsResult] at result
                          have argumentsParsed :=
                            ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
                                valuesResult argumentsResult
                          cases whereResult : whereClause afterArguments with
                          | invariant error => simp [whereResult] at result
                          | reject whereFailure whereRejected =>
                              simp only [whereResult] at result
                              cases result
                              exact .whereRejected defaultParsed marker.span
                                markerParsed genericsParsed nameParsed
                                argumentsParsed
                                (whereClause_ordinaryOutcome_sound.2
                                  whereResult)
                          | ok parsedWhere afterWhere =>
                              simp only [whereResult] at result
                              have whereParsed :=
                                whereClause_ordinaryOutcome_sound.1 whereResult
                              cases bodyResult : ImplInternals.implBody
                                  afterWhere with
                              | invariant error => simp [bodyResult] at result
                              | reject bodyFailure bodyRejected =>
                                  simp only [bodyResult] at result
                                  cases result
                                  exact .bodyRejected defaultParsed marker.span
                                    markerParsed genericsParsed nameParsed
                                    argumentsParsed whereParsed
                                    (ImplInternals.implBody_reject_ordinaryOutcome_sound
                                        bodyResult)
                              | ok body output =>
                                  simp [bodyResult, pure] at result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDeclarationOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for complete implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem implDeclarationOrdinarySuccess_bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable implementation success records its exact optional
default marker, head stages, broad body, AST span, and final remainder without
a diagnostic-free premise. -/
theorem implDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ImplDecl}
    (result : implDecl input = .ok declaration output) :
    DeclarativeGrammar.ImplDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold implDecl at result
  rcases implDeclarationOrdinarySuccess_bind_ok_components result with
    ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
  unfold ImplInternals.implDeclAfterDefault at suffix
  rcases implDeclarationOrdinarySuccess_bind_ok_components suffix with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨headArguments, afterArguments, argumentsResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases implDeclarationOrdinarySuccess_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed
    (ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
      defaultResult)
    marker.span
    (contextual_success_exactTokenParses .impl .topItem markerResult)
    (optionalGenericParameters_ordinaryOutcome_sound.1 genericsResult)
    (identifier_success_sound .topItem nameResult)
    (ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
      valuesResult argumentsResult)
    (whereClause_ordinaryOutcome_sound.1 whereResult)
    (ImplInternals.implBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDeclarationOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable implementation success and exact six-stage rejection. -/
theorem implDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ImplDecl},
      implDecl input = .ok declaration output →
        DeclarativeGrammar.ImplDeclOrdinaryParses input.declarativeRemainder
          declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      implDecl input = .reject failure rejected →
        DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨implDecl_success_ordinaryOutcome_sound,
    implDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad implementation outcomes. -/
theorem implDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclDeterministicOutcomeSpec

/-- Re-export exact implementation-declaration outcomes from exact complete
implementation-body outcomes. -/
theorem implDecl_exactOutcomeSpec_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfImplBody bodyOutcomes

/-- Re-export exact implementation-declaration outcomes from an exact
isolated method body. -/
theorem implDecl_exactOutcomeSpec_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfBody bodyOutcomes

/-- Fixed-fuel Core statement exactness discharges the executable
implementation-declaration contract. -/
theorem implDecl_exactOutcomeSpec_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel)) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplDeclOrdinaryParses
      DeclarativeGrammar.ImplDeclRejects :=
  DeclarativeGrammar.implDeclExactOutcomeSpecOfStatementFuel
    statementOutcomes

/-- Exact complete implementation-body outcomes make two successful
executable implementation declarations agree. -/
theorem implDecl_success_result_unique_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects)
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplDeclOrdinaryParses.result_unique_of_impl_body
    bodyOutcomes (implDecl_success_ordinaryOutcome_sound leftResult)
    (implDecl_success_ordinaryOutcome_sound rightResult)

/-- Exact complete implementation-body outcomes make two executable
implementation-declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_implBody
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ImplBodyRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ImplDeclRejects.output_unique_of_impl_body bodyOutcomes
    (implDecl_reject_ordinaryOutcome_sound leftResult)
    (implDecl_reject_ordinaryOutcome_sound rightResult)

/-- An exact isolated method body makes two successful executable
implementation declarations agree. -/
theorem implDecl_success_result_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_success_result_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- An exact isolated method body makes two executable implementation
declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_body
    (bodyOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.IsolatedCoreBlockPublicOrdinaryParses .allow)
      (DeclarativeGrammar.IsolatedCoreBlockPublicRejects .allow))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_reject_output_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfBody bodyOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two successful executable
implementation declarations agree. -/
theorem implDecl_success_result_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State} {left right : ImplDecl}
    (leftResult : implDecl input = .ok left leftOutput)
    (rightResult : implDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_success_result_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

/-- Fixed-fuel Core statement exactness makes two executable implementation
declaration rejections agree. -/
theorem implDecl_reject_output_unique_of_statementFuel
    (statementOutcomes : ∀ fuel,
      DeclarativeGrammar.ExactDeterministicOutcomeSpec
        (DeclarativeGrammar.CoreStatementOrdinaryParsesWithFuel fuel)
        (DeclarativeGrammar.CoreStatementRejectsWithFuel fuel))
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : implDecl input = .reject leftFailure leftOutput)
    (rightResult : implDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  implDecl_reject_output_unique_of_implBody
    (DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
      statementOutcomes)
    leftResult rightResult

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplProperties`
-/

/-! State-shape contracts for canonical implementation parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/-- Requiring nonempty head arguments leaves the token window unchanged. -/
theorem requireImplArguments_preservesTokenWindow
    (values : DelimitedList TypeExpr) :
    Parser.PreservesTokenWindow (requireImplArguments values) := by
  intro input
  unfold requireImplArguments
  cases values.elements <;> trivial

/-- Requiring nonempty head arguments never rewinds on success. -/
theorem requireImplArguments_cursorMonotoneOnSuccess
    (values : DelimitedList TypeExpr) :
    Parser.CursorMonotoneOnSuccess (requireImplArguments values) := by
  intro input result next parsed
  unfold requireImplArguments at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail => simp [elements] at parsed; cases parsed; exact Nat.le_refl _

/-- An implementation method preserves windows when function bodies do. -/
theorem implMethod_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implMethod := by
  unfold implMethod
  apply Parser.bind_preservesTokenWindow
    (functionDecl_preservesTokenWindow_of_block .module bodyWindow)
  intro declaration
  exact Parser.pure_preservesTokenWindow _

private theorem closeImplBody_preservesTokenWindow (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.PreservesTokenWindow (closeImplBody opening methodsRev) := by
  unfold closeImplBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

/-- The fuel-bounded method loop preserves every ordinary token window. -/
theorem implMethods_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (opening : Token) : ∀ fuel methodsRev,
    Parser.PreservesTokenWindow (implMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input
      unfold implMethods
      split
      · exact closeImplBody_preservesTokenWindow opening methodsRev input
      · split
        · have methodShape :=
            implMethod_preservesTokenWindow_of_block bodyWindow input
          cases methodResult : implMethod input with
          | ok method next =>
              rw [methodResult] at methodShape
              change (if next.cursor > input.cursor then
                implMethods opening fuel (method :: methodsRev) next
                else .invariant (.noProgress .topLevel next.currentSpan)
                ).PreservesTokenWindow input
              split
              · exact (inductionHypothesis (method :: methodsRev) next).trans
                  methodShape
              · trivial
          | reject failure rejected =>
              rw [methodResult] at methodShape
              exact methodShape
          | invariant error => trivial
        · exact rejectAt_preservesTokenWindow input _ _

/-- Implementation bodies preserve windows when nested function bodies do. -/
theorem implBody_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implBody := by
  intro input
  unfold implBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (implMethods_preservesTokenWindow_of_block bodyWindow opening
        (next.remainingCount + 1) [] next).trans openingShape
  | reject failure rejected => rw [openingResult] at openingShape; exact openingShape
  | invariant error => trivial

private theorem closeImplBody_cursorMonotoneOnSuccess (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.CursorMonotoneOnSuccess (closeImplBody opening methodsRev) := by
  unfold closeImplBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The method loop's explicit progress guard makes success monotone. -/
theorem implMethods_cursorMonotoneOnSuccess (opening : Token) :
    ∀ fuel methodsRev,
      Parser.CursorMonotoneOnSuccess (implMethods opening fuel methodsRev) := by
  intro fuel
  induction fuel with
  | zero => intro methodsRev input body next parsed; contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next parsed
      unfold implMethods at parsed
      split at parsed
      · exact closeImplBody_cursorMonotoneOnSuccess opening methodsRev
          input body next parsed
      · split at parsed
        · cases methodResult : implMethod input with
          | ok method afterMethod =>
              simp only [methodResult] at parsed
              split at parsed
              · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                  (inductionHypothesis (method :: methodsRev) afterMethod
                    body next parsed)
              · contradiction
          | reject failure rejected => simp [methodResult] at parsed
          | invariant error => simp [methodResult] at parsed
        · unfold rejectAt at parsed
          contradiction

/-- Successful implementation-body parsing never rewinds its caller. -/
theorem implBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implBody := by
  intro input body final parsed
  unfold implBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | ok opening next =>
      simp only [openingResult] at parsed
      exact Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftBrace .topItem input opening next
          openingResult)
        (implMethods_cursorMonotoneOnSuccess opening
          (next.remainingCount + 1) [] next body final parsed)
  | reject failure rejected => simp [openingResult] at parsed
  | invariant error => simp [openingResult] at parsed

end ImplInternals

private theorem implBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

namespace ImplInternals

/-- Optional `default` parsing preserves every ordinary token window. -/
theorem implDefaultMarker_preservesTokenWindow :
    Parser.PreservesTokenWindow implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .defaultKw .topItem)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem implDefaultMarker_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess implDefaultMarker :=
  implDefaultMarker_preservesTokenWindow.preservesTokensOnSuccess

/-- The declaration suffix preserves windows when nested function bodies do. -/
theorem implDeclAfterDefault_preservesTokenWindow_of_block
    (defaultMarker : Option SourceSpan)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow (implDeclAfterDefault defaultMarker) := by
  unfold implDeclAfterDefault
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .impl .topItem)
  intro marker
  apply Parser.bind_preservesTokenWindow optionalGenericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow (identifier_preservesTokenWindow .topItem)
  intro traitName
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_preservesTokenWindow)
  intro arguments
  apply Parser.bind_preservesTokenWindow
    (requireImplArguments_preservesTokenWindow arguments)
  intro headArguments
  apply Parser.bind_preservesTokenWindow whereClause_preservesTokenWindow
  intro whereClause
  apply Parser.bind_preservesTokenWindow
    (implBody_preservesTokenWindow_of_block bodyWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem implDeclAfterDefault_preservesTokensOnSuccess_of_block
    (defaultMarker : Option SourceSpan)
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess (implDeclAfterDefault defaultMarker) :=
  (implDeclAfterDefault_preservesTokenWindow_of_block defaultMarker
    bodyWindow).preservesTokensOnSuccess

/-- Optional `default` parsing never rewinds its caller. -/
theorem implDefaultMarker_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .topItem)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A retained default marker starts at the caller's current token. -/
theorem implDefaultMarker_some_startsAtCurrentTokenOnSuccess
    {input final : State} {marker : SourceSpan}
    (parsed : implDefaultMarker input = .ok (some marker) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = marker.startByte := by
  unfold implDefaultMarker getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at parsed
    cases tokenResult : keyword .defaultKw .topItem input with
    | invariant error => simp [tokenResult] at parsed
    | reject failure rejected => simp [tokenResult] at parsed
    | ok defaultToken next =>
        simp only [tokenResult] at parsed
        have starts := acceptToken_startsAtCurrentTokenOnSuccess
          (.keyword .defaultKw) .topItem (· == .keyword .defaultKw)
          input defaultToken next tokenResult
        cases parsed
        exact starts
  · simp only [present, Bool.false_eq_true, if_false] at parsed
    change Reply.ok none input = Reply.ok (some marker) final at parsed
    cases parsed

/-- Every successful suffix consumes at least its contextual `impl` token. -/
theorem implDeclAfterDefault_cursor_lt_onSuccess
    (defaultMarker : Option SourceSpan) {input final : State}
    {declaration : ImplDecl}
    (parsed : implDeclAfterDefault defaultMarker input =
      .ok declaration final) : input.cursor < final.cursor := by
  unfold implDeclAfterDefault at parsed
  rcases implBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨headArguments, afterHead, headResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases implBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (acceptToken_cursor_lt_onSuccess (.contextual .impl) .topItem
      (·.isContextual .impl) markerResult)
    (Nat.le_trans
      (optionalGenericParameters_cursorMonotoneOnSuccess afterMarker
        genericParameters afterGenerics genericsResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
          afterGenerics traitName afterName nameResult)
        (Nat.le_trans (delimited_cursorMonotoneOnSuccess .less .greater false
            typeExpr .typeExpr .topLevel afterName arguments afterArguments
            argumentsResult)
          (Nat.le_trans (requireImplArguments_cursorMonotoneOnSuccess arguments
              afterArguments headArguments afterHead headResult)
            (Nat.le_trans (whereClause_cursorMonotoneOnSuccess afterHead
                whereClause afterWhere whereResult)
              (implBody_cursorMonotoneOnSuccess afterWhere body final
                bodyResult))))))

theorem implDeclAfterDefault_cursorMonotoneOnSuccess
    (defaultMarker : Option SourceSpan) :
    Parser.CursorMonotoneOnSuccess (implDeclAfterDefault defaultMarker) := by
  intro input declaration final parsed
  exact Nat.le_of_lt (implDeclAfterDefault_cursor_lt_onSuccess defaultMarker parsed)

end ImplInternals

open ImplInternals

/-- Complete implementation parsing preserves ordinary token windows. -/
theorem implDecl_preservesTokenWindow_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokenWindow implDecl := by
  unfold implDecl
  apply Parser.bind_preservesTokenWindow implDefaultMarker_preservesTokenWindow
  intro defaultMarker
  exact implDeclAfterDefault_preservesTokenWindow_of_block defaultMarker bodyWindow

/-- Successful implementation parsing retains the immutable token carrier. -/
theorem implDecl_preservesTokensOnSuccess_of_block
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    Parser.PreservesTokensOnSuccess implDecl :=
  (implDecl_preservesTokenWindow_of_block bodyWindow).preservesTokensOnSuccess

/-- Every successful implementation consumes at least its `impl` marker. -/
theorem implDecl_cursor_lt_onSuccess {input final : State}
    {declaration : ImplDecl} (parsed : implDecl input = .ok declaration final) :
    input.cursor < final.cursor := by
  unfold implDecl at parsed
  rcases implBind_ok_components parsed with
    ⟨defaultMarker, afterDefault, defaultResult, declarationResult⟩
  exact Nat.lt_of_le_of_lt
    (implDefaultMarker_cursorMonotoneOnSuccess input defaultMarker
      afterDefault defaultResult)
    (implDeclAfterDefault_cursor_lt_onSuccess defaultMarker declarationResult)

/-- Complete implementation parsing never rewinds on success. -/
theorem implDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess implDecl := by
  intro input declaration final parsed
  exact Nat.le_of_lt (implDecl_cursor_lt_onSuccess parsed)

/-- A suffix retains its contextual marker or the supplied earlier prefix. -/
theorem ImplInternals.implDeclAfterDefault_startOnSuccess
    (defaultMarker : Option SourceSpan) {input final : State}
    {declaration : ImplDecl}
    (parsed : implDeclAfterDefault defaultMarker input =
      .ok declaration final) :
    ∃ marker afterMarker,
      contextual .impl .topItem input = .ok marker afterMarker ∧
      declaration.span.startByte =
        (defaultMarker.getD marker.span).startByte := by
  unfold implDeclAfterDefault at parsed
  rcases implBind_ok_components parsed with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implBind_ok_components rest with ⟨generics, afterGenerics, _, rest⟩
  rcases implBind_ok_components rest with ⟨traitName, afterName, _, rest⟩
  rcases implBind_ok_components rest with ⟨arguments, afterArguments, _, rest⟩
  rcases implBind_ok_components rest with ⟨headArguments, afterHead, _, rest⟩
  rcases implBind_ok_components rest with ⟨whereClause, afterWhere, _, rest⟩
  rcases implBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  exact ⟨marker, afterMarker, markerResult, rfl⟩

/-- A complete implementation starts at `default`, when present, or `impl`. -/
theorem implDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess implDecl (·.span) := by
  intro input declaration final parsed
  unfold implDecl at parsed
  rcases implBind_ok_components parsed with
    ⟨defaultMarker, afterDefault, defaultResult, declarationResult⟩
  rcases implDeclAfterDefault_startOnSuccess defaultMarker declarationResult with
    ⟨marker, afterMarker, markerResult, declarationStart⟩
  unfold implDefaultMarker getState at defaultResult
  simp only [bind] at defaultResult
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at defaultResult
    cases tokenResult : keyword .defaultKw .topItem input with
    | invariant error => simp [tokenResult] at defaultResult
    | reject failure rejected => simp [tokenResult] at defaultResult
    | ok defaultToken next =>
        simp only [tokenResult] at defaultResult
        have starts := acceptToken_startsAtCurrentTokenOnSuccess
          (.keyword .defaultKw) .topItem (· == .keyword .defaultKw)
          input defaultToken next tokenResult
        cases defaultResult
        rcases starts with ⟨token, found, start⟩
        exact ⟨token, found, by simpa [declarationStart] using start⟩
  · simp only [present, Bool.false_eq_true, if_false] at defaultResult
    cases defaultResult
    rcases contextual_startsAtCurrentTokenOnSuccess .impl .topItem
        input marker afterMarker markerResult with ⟨token, found, start⟩
    exact ⟨token, found, by simpa [declarationStart] using start⟩

namespace ImplInternals

namespace ImplBody

/-- Every implementation-body range and retained method belongs to one source. -/
def ValidFor (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (body : ImplBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor (ImplMethod.ValidFor statementValid) file body.methods

end ImplBody

/-- Requiring nonempty head arguments preserves recursive type provenance. -/
theorem requireImplArguments_reply_validFor
    (values : DelimitedList TypeExpr) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : values.ValidFor TypeExpr.ValidFor input.file) :
    (requireImplArguments values input).ValidFor input
      (NonemptyDelimitedList.ValidFor TypeExpr.ValidFor) := by
  unfold requireImplArguments
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [Reply.ValidFor, NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, rfl⟩
      intro element member
      apply valuesValid.2 element
      simpa [NonemptyList.toList, elements] using member

/-- One implementation method retains its function and empty comment prefix. -/
theorem implMethod_validFor (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor
      (Block.ValidFor statementValid)) :
    implMethod.ValidFor (ImplMethod.ValidFor statementValid) := by
  unfold implMethod
  apply Parser.bind_validFor_of_value
    (functionDecl_validFor statementValid .module blockValid)
  intro declaration input inputValid declarationValid
  exact ⟨⟨declarationValid.1, by simp, declarationValid⟩,
    inputValid, rfl⟩

private theorem closeImplBody_validFor
    (statementValid : SourceFile → Statement → Prop) (opening : Token)
    (methodsRev : List ImplMethod) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (methodsValid : List.ValidFor (ImplMethod.ValidFor statementValid)
      input.file methodsRev) :
    (closeImplBody opening methodsRev input).ValidFor input
      (ImplBody.ValidFor statementValid) := by
  unfold closeImplBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp only [bind, closingResult]; trivial
  | reject failure rejected =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult]
      exact closingReply
  | ok closing next =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult, pure, Reply.ValidFor]
      have closingShape := symbol_ok_state_shape .rightBrace .topItem
        closingResult
      have closingAt := State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingReply.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        openingFound closingAt openingBefore
      have ordered : opening.span.startByte ≤ closing.span.endByte :=
        Nat.le_trans openingValid.2.1
          (Nat.le_trans separated closingValid.2.1)
      refine ⟨⟨SourceSpan.cover_validFor openingValid closingValid ordered, ?_⟩,
        closingReply.2.1, closingReply.2.2⟩
      intro method member
      exact methodsValid method (by simpa using member)

/-- The method loop retains every method and the complete body range. -/
theorem implMethods_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (opening : Token) : ∀ fuel methodsRev input openingIndex,
      input.ValidFor → input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor (ImplMethod.ValidFor statementValid) input.file methodsRev →
      (implMethods opening fuel methodsRev input).ValidFor input
        (ImplBody.ValidFor statementValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro methodsRev input openingIndex inputValid openingFound
        openingBefore methodsValid
      unfold implMethods
      split
      · exact closeImplBody_validFor statementValid opening methodsRev input
          openingIndex inputValid openingFound openingBefore methodsValid
      · split
        · have methodReply := implMethod_validFor statementValid blockValid
            input inputValid
          cases methodResult : implMethod input with
          | invariant error => trivial
          | reject failure rejected =>
              rw [methodResult] at methodReply
              exact methodReply
          | ok method next =>
              rw [methodResult] at methodReply
              simp only
              split
              · have methodTokens :=
                  (implMethod_preservesTokenWindow_of_block bodyWindow
                    ).preservesTokensOnSuccess
                have openingFoundNext : next.tokens[openingIndex]? =
                    some opening := by
                  simpa [methodTokens input method next methodResult] using
                    openingFound
                have accumulated : List.ValidFor
                    (ImplMethod.ValidFor statementValid) next.file
                    (method :: methodsRev) := by
                  intro retained member
                  rcases List.mem_cons.mp member with rfl | retainedMember
                  · simpa [methodReply.2.2] using methodReply.1
                  · simpa [methodReply.2.2] using
                      methodsValid retained retainedMember
                have progress : input.cursor < next.cursor := by omega
                exact (inductionHypothesis (method :: methodsRev) next
                  openingIndex methodReply.2.1 openingFoundNext
                  (Nat.lt_trans openingBefore progress) accumulated
                    ).of_file_eq methodReply.2.2
              · trivial
        · unfold rejectAt Reply.ValidFor
          exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

/-- A complete implementation body retains both braces and every method. -/
theorem implBody_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    implBody.ValidFor (ImplBody.ValidFor statementValid) := by
  intro input inputValid
  unfold implBody
  have openingReply := symbol_validFor .leftBrace .topItem input inputValid
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingReply
      exact openingReply
  | ok opening next =>
      rw [openingResult] at openingReply
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have openingAtInput :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have openingAtNext : next.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingAtInput
      exact (implMethods_validFor statementValid blockValid bodyWindow opening
        (next.remainingCount + 1) [] next input.cursor openingReply.2.1
        openingAtNext (by simp [openingShape.2])
        (by simp [List.ValidFor])).of_file_eq openingReply.2.2

private theorem implMethods_preservesOpeningStartOnSuccess
    (opening : Token) : ∀ fuel methodsRev input body final,
    implMethods opening fuel methodsRev input = .ok body final →
      body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro methodsRev input body final parsed
      unfold implMethods at parsed
      split at parsed
      · unfold closeImplBody at parsed
        rcases implBind_ok_components parsed with
          ⟨closing, afterClosing, closingResult, finished⟩
        cases finished
        rfl
      · split at parsed
        · cases methodResult : implMethod input with
          | invariant error => simp [methodResult] at parsed
          | reject failure rejected => simp [methodResult] at parsed
          | ok method next =>
              simp only [methodResult] at parsed
              split at parsed
              · exact inductionHypothesis (method :: methodsRev) next body
                  final parsed
              · contradiction
        · simp [rejectAt] at parsed

/-- A complete implementation body starts at its opening brace token. -/
theorem implBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess implBody (·.span) := by
  intro input body final parsed
  unfold implBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have retained := implMethods_preservesOpeningStartOnSuccess opening
        (next.remainingCount + 1) [] next body final parsed
      exact ⟨opening, openingShape.1, retained.symm⟩

/-- Optional default parsing retains only a valid marker when present. -/
theorem implDefaultMarker_validFor :
    implDefaultMarker.ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold implDefaultMarker
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (keyword_validFor .defaultKw .topItem)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

end ImplInternals

/-- Complete implementation declarations retain only source-valid syntax. -/
theorem implDecl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (blockValid : (block .allow).ValidFor
      (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow)) :
    implDecl.ValidFor (ImplDecl.ValidFor statementValid) := by
  intro input inputValid
  have weak : implDecl.ValidFor (fun _ _ => True) := by
    unfold implDecl
    apply Parser.bind_validFor ImplInternals.implDefaultMarker_validFor
    intro defaultMarker
    unfold ImplInternals.implDeclAfterDefault
    apply Parser.bind_validFor (contextual_validFor .impl .topItem)
    intro marker
    apply Parser.bind_validFor optionalGenericParameters_validFor
    intro genericParameters
    apply Parser.bind_validFor (identifier_validFor .topItem)
    intro traitName
    apply Parser.bind_validFor
      (delimited_validFor TypeExpr.ValidFor .less .greater false typeExpr
        .typeExpr .topLevel typeExpr_validFor
        typeExpr_preservesTokensOnSuccess)
    intro arguments
    have requireWeak : (ImplInternals.requireImplArguments arguments).ValidFor
        (fun _ _ => True) := by
      intro state stateValid
      unfold ImplInternals.requireImplArguments
      cases arguments.elements with
      | nil => trivial
      | cons head tail => exact ⟨trivial, stateValid, rfl⟩
    apply Parser.bind_validFor requireWeak
    intro headArguments
    apply Parser.bind_validFor whereClause_validFor
    intro parsedWhereClause
    apply Parser.bind_validFor
      (ImplInternals.implBody_validFor statementValid blockValid bodyWindow)
    intro body
    exact Parser.pure_validFor _ _ (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : implDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold implDecl at stages
      rcases implBind_ok_components stages with
        ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
      unfold ImplInternals.implDeclAfterDefault at suffix
      rcases implBind_ok_components suffix with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨genericParameters, afterGenerics, genericsResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨traitName, afterName, nameResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨headArguments, afterHead, headResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
      rcases implBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have defaultReply := ImplInternals.implDefaultMarker_validFor input
        inputValid
      rw [defaultResult] at defaultReply
      have markerReply := contextual_validFor .impl .topItem afterDefault
        defaultReply.2.1
      rw [markerResult] at markerReply
      have genericsReply := optionalGenericParameters_validFor afterMarker
        markerReply.2.1
      rw [genericsResult] at genericsReply
      have nameReply := identifier_validFor .topItem afterGenerics
        genericsReply.2.1
      rw [nameResult] at nameReply
      have argumentsReply := delimited_validFor TypeExpr.ValidFor .less
        .greater false typeExpr .typeExpr .topLevel typeExpr_validFor
        typeExpr_preservesTokensOnSuccess afterName nameReply.2.1
      rw [argumentsResult] at argumentsReply
      have argumentsValidAfter : DelimitedList.ValidFor TypeExpr.ValidFor
          afterArguments.file arguments := by
        simpa [argumentsReply.2.2] using argumentsReply.1
      have headReply := ImplInternals.requireImplArguments_reply_validFor
        arguments afterArguments argumentsReply.2.1 argumentsValidAfter
      rw [headResult] at headReply
      have whereReply := whereClause_validFor afterHead headReply.2.1
      rw [whereResult] at whereReply
      have bodyReply := ImplInternals.implBody_validFor statementValid
        blockValid bodyWindow afterWhere whereReply.2.1
      rw [bodyResult] at bodyReply
      have defaultValid : Option.ValidFor
          (fun file span => span.ValidFor file) input.file defaultMarker := by
        exact defaultReply.1
      have markerValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor, defaultReply.2.2] using markerReply.1
      have genericsValid : Option.ValidFor
          (NonemptyDelimitedList.ValidFor Located.ValidFor) input.file
          genericParameters := by
        simpa [markerReply.2.2, defaultReply.2.2] using genericsReply.1
      have nameValid : traitName.span.ValidFor input.file := by
        simpa only [Located.ValidFor, genericsReply.2.2,
          markerReply.2.2, defaultReply.2.2] using nameReply.1
      have headValid : NonemptyDelimitedList.ValidFor TypeExpr.ValidFor
          input.file headArguments := by
        simpa [headReply.2.2, argumentsReply.2.2, nameReply.2.2,
          genericsReply.2.2, markerReply.2.2, defaultReply.2.2] using
          headReply.1
      have whereValid : Option.ValidFor WhereClause.ValidFor input.file
          parsedWhereClause := by
        simpa [headReply.2.2, argumentsReply.2.2, nameReply.2.2,
          genericsReply.2.2, markerReply.2.2, defaultReply.2.2] using
          whereReply.1
      have bodyValid : ImplInternals.ImplBody.ValidFor statementValid
          input.file body := by
        simpa [whereReply.2.2, headReply.2.2, argumentsReply.2.2,
          nameReply.2.2, genericsReply.2.2, markerReply.2.2,
          defaultReply.2.2] using bodyReply.1
      rcases ImplInternals.implBody_startsAtCurrentTokenOnSuccess afterWhere
          body afterBody bodyResult with
        ⟨opening, openingFound, bodyStart⟩
      have openingAtAfter :=
        State.getElem?_eq_some_of_peek?_eq_some openingFound
      have defaultTokens :=
        ImplInternals.implDefaultMarker_preservesTokensOnSuccess input
          defaultMarker afterDefault defaultResult
      have markerTokens := contextual_preservesTokensOnSuccess .impl .topItem
        afterDefault marker afterMarker markerResult
      have genericsTokens := optionalGenericParameters_preservesTokensOnSuccess
        afterMarker genericParameters afterGenerics genericsResult
      have nameTokens := identifier_preservesTokensOnSuccess .topItem
        afterGenerics traitName afterName nameResult
      have argumentsTokens := delimited_preservesTokensOnSuccess .less .greater
        false typeExpr .typeExpr .topLevel typeExpr_preservesTokensOnSuccess
        afterName arguments afterArguments argumentsResult
      have headTokens :=
        (ImplInternals.requireImplArguments_preservesTokenWindow arguments
          ).preservesTokensOnSuccess afterArguments headArguments afterHead
            headResult
      have whereTokens := whereClause_preservesTokensOnSuccess afterHead
        parsedWhereClause afterWhere whereResult
      have openingAt : input.tokens[afterWhere.cursor]? = some opening := by
        simpa [whereTokens, headTokens, argumentsTokens, nameTokens,
          genericsTokens, markerTokens, defaultTokens] using openingAtAfter
      have progress : input.cursor < afterWhere.cursor :=
        Nat.lt_of_le_of_lt
          (ImplInternals.implDefaultMarker_cursorMonotoneOnSuccess input
            defaultMarker afterDefault defaultResult)
          (Nat.lt_of_lt_of_le
            (acceptToken_cursor_lt_onSuccess (.contextual .impl) .topItem
              (fun kind => kind.isContextual .impl) markerResult)
            (Nat.le_trans
              (optionalGenericParameters_cursorMonotoneOnSuccess afterMarker
                genericParameters afterGenerics genericsResult)
              (Nat.le_trans
                (identifier_cursorMonotoneOnSuccess .topItem afterGenerics
                  traitName afterName nameResult)
                (Nat.le_trans
                  (delimited_cursorMonotoneOnSuccess .less .greater false
                    typeExpr .typeExpr .topLevel afterName arguments
                    afterArguments argumentsResult)
                  (Nat.le_trans
                    (ImplInternals.requireImplArguments_cursorMonotoneOnSuccess
                      arguments afterArguments headArguments afterHead
                      headResult)
                    (whereClause_cursorMonotoneOnSuccess afterHead
                      parsedWhereClause afterWhere whereResult))))))
      rcases implDecl_startsAtCurrentTokenOnSuccess input declaration final
          parsed with ⟨startToken, startFound, declarationStart⟩
      cases finished
      have startAt := State.getElem?_eq_some_of_peek?_eq_some startFound
      have startTokenValid := inputValid.peek?_span_validFor startFound
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        startAt openingAt progress
      let startSpan := defaultMarker.getD marker.span
      have startValid : startSpan.ValidFor input.file := by
        cases defaultMarker with
        | none => simpa [startSpan] using markerValid
        | some retained =>
            simpa [startSpan, Option.ValidFor] using defaultValid
      have startTokenStart :
          startToken.span.startByte = startSpan.startByte := by
        simpa [startSpan, SourceSpan.cover] using declarationStart
      have ordered : startSpan.startByte ≤ body.span.endByte := by
        calc
          startSpan.startByte = startToken.span.startByte := startTokenStart.symm
          _ ≤ startToken.span.endByte := startTokenValid.2.1
          _ ≤ opening.span.startByte := separated
          _ = body.span.startByte := bodyStart
          _ ≤ body.span.endByte := bodyValid.1.2.1
      have outerValid := SourceSpan.cover_validFor startValid bodyValid.1 ordered
      refine ⟨⟨outerValid, ?_, ?_, ?_, nameValid, headValid.1,
        headValid.2, ?_, bodyValid.1, bodyValid.2⟩,
        weakResult.2.1, weakResult.2.2⟩
      · intro retained member
        cases defaultMarker with
        | none => simp at member
        | some marker =>
            have retainedEq : retained = marker := by simpa using member.symm
            subst retained
            simpa [Option.ValidFor] using defaultValid
      · intro retained member
        cases genericParameters with
        | none => simp at member
        | some parameters =>
            have retainedEq : retained = parameters := by simpa using member.symm
            subst retained
            simpa [Option.ValidFor] using genericsValid.1
      · intro retained member parameter parameterMember
        cases genericParameters with
        | none => simp at member
        | some parameters =>
            have retainedEq : retained = parameters := by simpa using member.symm
            subst retained
            exact genericsValid.2 parameter parameterMember
      · intro clause member
        cases parsedWhereClause with
        | none => simp at member
        | some retained =>
            simp at member
            subst clause
            simpa [Option.ValidFor] using whereValid

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplBodyTotalityProperties`
-/

/-! Valid-input totality for canonical implementation methods and bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem implBodyTotality_bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- An implementation method inherits totality from a module function. -/
theorem implMethod_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implMethod := by
  unfold implMethod
  apply Parser.bind_invariantFreeOnValid
    (functionDecl_validFor CoreStatement.ValidFor .module
      (block_canonical_validFor .allow))
    (functionDecl_invariantFreeOnValid .module)
  intro declaration
  exact Parser.pure_invariantFreeOnValid ({
    span := declaration.span
    value := { leadingComments := [], declaration }
  } : ImplMethod)

theorem implMethod_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ method next, implMethod input = .ok method next) ∨
      (∃ failure next, implMethod input = .reject failure next) :=
  implMethod_invariantFreeOnValid input inputValid

theorem implMethod_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implMethod input ≠ .invariant error :=
  implMethod_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful implementation method consumes its function signature. -/
theorem implMethod_cursor_lt_onSuccess {input final : State}
    {method : ImplMethod}
    (parsed : implMethod input = .ok method final) :
    input.cursor < final.cursor := by
  unfold implMethod at parsed
  rcases implBodyTotality_bind_ok_components parsed with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  unfold functionDecl at declarationResult
  rcases implBodyTotality_bind_ok_components declarationResult with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases implBodyTotality_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (FunctionInternals.functionSignature_cursor_lt_onSuccess .module
      signatureResult)
    (isolateBlock_cursorMonotoneOnSuccess (block .allow)
      (block_canonical_cursorMonotoneOnSuccess .allow)
      afterSignature body final bodyResult)

private theorem closeImplBody_ordinary (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.Ordinary (closeImplBody opening methodsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
      span := SourceSpan.cover opening.span closing.span
      methods := methodsRev.reverse
    }, next, by
      simp only [closeImplBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeImplBody, bind, closingResult]⟩

/-- Adequate loop fuel excludes both exhaustion and no-progress invariants. -/
theorem implMethods_ordinary_of_remainingCount_lt (opening : Token) :
    ∀ fuel methodsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        implMethods opening fuel methodsRev input = .ok body next) ∨
      (∃ failure next,
        implMethods opening fuel methodsRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro methodsRev input inputValid adequate
      unfold implMethods
      by_cases closes : isSymbol input .rightBrace
      · simpa only [closes, if_true] using
          closeImplBody_ordinary opening methodsRev input
      · by_cases methodPresent : isKeyword input .functionKw
        · rcases implMethod_ordinary input inputValid with
            ⟨method, next, methodResult⟩ |
            ⟨failure, rejected, methodResult⟩
          · have methodReply := implMethod_validFor CoreStatement.ValidFor
              (block_canonical_validFor .allow) input inputValid
            rw [methodResult] at methodReply
            have methodWindow := implMethod_preservesTokenWindow_of_block
              (block_canonical_preservesTokenWindow .allow) input
            rw [methodResult] at methodWindow
            have progress := implMethod_cursor_lt_onSuccess methodResult
            have nextAdequate : next.remainingCount < fuel :=
              remainingCount_lt_after_strict_progress methodReply.2.1
                methodWindow.2 progress adequate
            simpa only [closes, Bool.false_eq_true, if_false,
              methodPresent, if_true, methodResult, if_pos progress] using
                inductionHypothesis (method :: methodsRev) next
                  methodReply.2.1 nextAdequate
          · exact Or.inr ⟨failure, rejected, by
              simp only [closes, Bool.false_eq_true, if_false,
                methodPresent, if_true, methodResult]⟩
        · simpa only [closes, Bool.false_eq_true, if_false,
            methodPresent] using
              (Parser.rejectAt_invariantFreeOnValid
                (alpha := ImplBody)
                { head := .keyword .functionKw,
                  tail := [.symbol .rightBrace] }
                .topItem) input inputValid

/-- Production fuel is one more than the current remaining token count. -/
theorem implMethods_production_ordinary
    (opening : Token) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body next,
      implMethods opening (input.remainingCount + 1) methodsRev input =
        .ok body next) ∨
      (∃ failure next,
        implMethods opening (input.remainingCount + 1) methodsRev input =
          .reject failure next) :=
  implMethods_ordinary_of_remainingCount_lt opening
    (input.remainingCount + 1) methodsRev input inputValid (by omega)

theorem implMethods_production_invariantFreeOnValid
    (opening : Token) (methodsRev : List ImplMethod) :
    Parser.InvariantFreeOnValid (fun input =>
      implMethods opening (input.remainingCount + 1) methodsRev input) :=
  fun input inputValid =>
    implMethods_production_ordinary opening methodsRev input inputValid

theorem implMethods_production_ne_invariant
    (opening : Token) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implMethods opening (input.remainingCount + 1) methodsRev input ≠
      .invariant error :=
  (implMethods_production_invariantFreeOnValid opening methodsRev
    ).ne_invariant input inputValid error

theorem implMethods_ne_invariant_of_remainingCount_lt
    (opening : Token) (fuel : Nat) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    implMethods opening fuel methodsRev input ≠ .invariant error := by
  intro failed
  rcases implMethods_ordinary_of_remainingCount_lt opening fuel methodsRev
      input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- A complete canonical implementation body is total on valid input. -/
theorem implBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implBody := by
  intro input inputValid
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, next, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    simpa only [implBody, openingResult] using
      implMethods_production_ordinary opening [] next openingReply.2.1
  · exact Or.inr ⟨failure, rejected, by
      simp only [implBody, openingResult]⟩

theorem implBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, implBody input = .ok body next) ∨
      (∃ failure next, implBody input = .reject failure next) :=
  implBody_invariantFreeOnValid input inputValid

theorem implBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implBody input ≠ .invariant error :=
  implBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplHeadTotalityProperties`
-/

/-! Totality helpers for canonical implementation declaration heads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- A syntactically nonempty implementation argument list refines safely. -/
theorem requireImplArguments_ok_of_delimited_false_ok
    {input afterDelimited : State} {values : DelimitedList TypeExpr}
    (parsed : delimited .less .greater false typeExpr .typeExpr .topLevel
      input = .ok values afterDelimited) :
    ∃ nonempty,
      requireImplArguments values afterDelimited =
        .ok nonempty afterDelimited := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess .less .greater
    typeExpr .typeExpr .topLevel parsed
  unfold requireImplArguments
  cases elements : values.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

/-- The optional leading `default` marker is ordinary on valid input. -/
theorem implDefaultMarker_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implDefaultMarker := by
  unfold implDefaultMarker
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (keyword_validFor .defaultKw .topItem)
      (keyword_ordinary .defaultKw .topItem).invariantFreeOnValid
    intro marker
    exact Parser.pure_invariantFreeOnValid (some marker.span)
  · simp only [present, Bool.false_eq_true, if_false]
    exact Parser.pure_invariantFreeOnValid none

theorem implDefaultMarker_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDefaultMarker input ≠ .invariant error :=
  implDefaultMarker_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDeclarationTotalityProperties`
-/

/-! Valid-input totality for complete canonical implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ImplInternals

/--
Compose a total parser with a defensive refinement known to succeed for every
value actually produced by that parser.
-/
private theorem bind_refinement_invariantFreeOnValid
    {alpha beta gamma : Type} {first : Parser alpha}
    {refine : alpha → Parser beta} {next : beta → Parser gamma}
    (firstValid : first.ValidFor (fun _ _ => True))
    (firstFree : Parser.InvariantFreeOnValid first)
    (refineOk : ∀ {input after : State} {value : alpha},
      first input = .ok value after →
        ∃ refined, refine value after = .ok refined after)
    (nextFree : ∀ refined, Parser.InvariantFreeOnValid (next refined)) :
    Parser.InvariantFreeOnValid (do
      let value ← first
      let refined ← refine value
      next refined) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨value, after, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · have firstReply := firstValid input inputValid
    rw [firstResult] at firstReply
    rcases refineOk firstResult with ⟨refined, refineResult⟩
    rcases nextFree refined after firstReply.2.1 with
      ⟨result, final, nextResult⟩ |
      ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨result, final, by
        simp only [bind, firstResult, refineResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, refineResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- The declaration suffix is total after either optional-default outcome. -/
theorem implDeclAfterDefault_invariantFreeOnValid
    (defaultMarker : Option SourceSpan) :
    Parser.InvariantFreeOnValid (implDeclAfterDefault defaultMarker) := by
  unfold implDeclAfterDefault
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .impl .topItem)
    (contextual_ordinary .impl .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro genericParameters
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro traitName
  apply bind_refinement_invariantFreeOnValid
    ((delimited_validFor TypeExpr.ValidFor .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_validFor
      typeExpr_preservesTokensOnSuccess).mono (fun _ _ _ => trivial))
    (fun input inputValid =>
      delimited_ordinary .less .greater false typeExpr .typeExpr .topLevel
        typeExpr_elementTotalityContract input inputValid)
    requireImplArguments_ok_of_delimited_false_ok
  intro headArguments
  apply Parser.bind_invariantFreeOnValid whereClause_validFor
    whereClause_invariantFreeOnValid
  intro parsedWhereClause
  apply Parser.bind_invariantFreeOnValid
    (implBody_validFor CoreStatement.ValidFor
      (block_canonical_validFor .allow)
      (block_canonical_preservesTokenWindow .allow))
    implBody_invariantFreeOnValid
  intro body
  let startSpan := defaultMarker.getD marker.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover startSpan body.span
    value := {
      defaultMarker
      genericParameters
      traitName
      headArguments
      whereClause := parsedWhereClause
      bodySpan := body.span
      methods := body.methods
    }
  } : ImplDecl)

theorem implDeclAfterDefault_ordinary
    (defaultMarker : Option SourceSpan)
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next,
      implDeclAfterDefault defaultMarker input = .ok declaration next) ∨
      (∃ failure next,
        implDeclAfterDefault defaultMarker input = .reject failure next) :=
  implDeclAfterDefault_invariantFreeOnValid defaultMarker input inputValid

theorem implDeclAfterDefault_ne_invariant
    (defaultMarker : Option SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDeclAfterDefault defaultMarker input ≠ .invariant error :=
  (implDeclAfterDefault_invariantFreeOnValid defaultMarker).ne_invariant
    input inputValid error

end ImplInternals

open ImplInternals

/-- A complete optional-default implementation is total on valid input. -/
theorem implDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implDecl := by
  unfold implDecl
  apply Parser.bind_invariantFreeOnValid implDefaultMarker_validFor
    implDefaultMarker_invariantFreeOnValid
  intro defaultMarker
  exact implDeclAfterDefault_invariantFreeOnValid defaultMarker

theorem implDecl_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, implDecl input = .ok declaration next) ∨
      (∃ failure next, implDecl input = .reject failure next) :=
  implDecl_invariantFreeOnValid input inputValid

theorem implDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implDecl input ≠ .invariant error :=
  implDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplMethodSoundnessProperties`
-/

/-! Parametric diagnostic-free soundness for one implementation method. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem implMethodSoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

namespace ImplInternals

/-- One implementation method reflects diagnostic freedom through its body. -/
theorem implMethod_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implMethod := by
  unfold implMethod
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionDecl_reflectsDiagnosticFreeOnSuccess .module bodyReflects)
  intro declaration
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/--
Every diagnostic-free method success is an exact module-policy function over
the supplied parser-independent block grammar.
-/
theorem implMethod_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {method : ImplMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implMethod input = .ok method next) :
    DeclarativeGrammar.ImplMethodParses bodyParses
      input.declarativeRemainder method next.declarativeRemainder := by
  unfold implMethod at result
  rcases implMethodSoundness_bind_ok_components result with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  exact .parsed (functionDecl_success_sound .module bodyParses bodyReflects
    bodySound diagnosticFree declarationResult)

/-- Parametric method grammar soundness composes with source validity. -/
theorem implMethod_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {method : ImplMethod}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implMethod input = .ok method next) :
    DeclarativeGrammar.ImplMethodParses bodyParses
        input.declarativeRemainder method next.declarativeRemainder ∧
      ImplMethod.ValidFor statementValid input.file method := by
  refine ⟨implMethod_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implMethod_validFor statementValid bodyValid input inputValid
  rw [result] at valid
  exact valid.1

end ImplInternals

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplBodySoundnessProperties`
-/

/-! Parametric diagnostic-free soundness for the fuel-bounded implementation body. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem implBodySoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem closeImplBody_success_sound_and_reflects
    (opening : Token) (methodsRev : List ImplMethod)
    {input next : State} {body : ImplBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : closeImplBody opening methodsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        methods := methodsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder ∧
      input.diagnosticsRev = [] := by
  unfold closeImplBody at result
  rcases implBodySoundness_bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  have afterClosingFree : afterClosing.diagnosticsRev = [] := by
    cases finished
    exact diagnosticFree
  have inputFree : input.diagnosticsRev = [] :=
    symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .topItem input closing
      afterClosing closingResult afterClosingFree
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult,
    inputFree⟩

private theorem implMethods_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) (opening : Token) :
    ∀ fuel methodsRev input body next,
      implMethods opening fuel methodsRev input = .ok body next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next result diagnosticFree
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next result diagnosticFree
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeImplBody_success_sound_and_reflects opening methodsRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact inputFree
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases methodPresent : isKeyword input .functionKw with
          | false => simp [methodPresent, rejectAt] at result
          | true =>
              simp only [methodPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    have afterMethodFree := inductionHypothesis
                      (method :: methodsRev) afterMethod body next result
                        diagnosticFree
                    exact implMethod_reflectsDiagnosticFreeOnSuccess
                      bodyReflects input method afterMethod methodResult
                        afterMethodFree
                  · simp only [progress, if_false] at result
                    contradiction

/-- Implementation-body parsing cannot erase an incoming diagnostic. -/
theorem implBody_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implBody := by
  intro input body next result diagnosticFree
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have afterOpeningFree := implMethods_reflectsDiagnosticFreeOnSuccess
        bodyReflects opening (afterOpening.remainingCount + 1) []
          afterOpening body next result diagnosticFree
      exact symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .topItem input
        opening afterOpening openingResult afterOpeningFree

private theorem implMethods_success_sound_strong
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (opening : Token) :
    ∀ fuel methodsRev input body next,
      next.diagnosticsRev = [] →
      implMethods opening fuel methodsRev input = .ok body next →
      ∃ methods closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          methods := methodsRev.reverse ++ methods
        } ∧
        DeclarativeGrammar.ImplMethodTailParses bodyParses
          input.declarativeRemainder methods closingSpan
            next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro methodsRev input body next diagnosticFree result
      simp [implMethods] at result
  | succ fuel inductionHypothesis =>
      intro methodsRev input body next diagnosticFree result
      unfold implMethods at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeImplBody_success_sound_and_reflects opening methodsRev
              diagnosticFree result with
            ⟨closingSpan, bodyEq, closingGrammar, inputFree⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingGrammar, inputFree⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases methodPresent : isKeyword input .functionKw with
          | false => simp [methodPresent, rejectAt] at result
          | true =>
              simp only [methodPresent, if_true] at result
              cases methodResult : implMethod input with
              | invariant error => simp [methodResult] at result
              | reject failure rejected => simp [methodResult] at result
              | ok method afterMethod =>
                  simp only [methodResult] at result
                  by_cases progress : afterMethod.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (method :: methodsRev)
                        afterMethod body next diagnosticFree result with
                      ⟨methods, closingSpan, bodyEq, tailGrammar,
                        afterMethodFree⟩
                    have methodGrammar := implMethod_success_sound bodyParses
                      bodyReflects bodySound afterMethodFree methodResult
                    have inputFree := implMethod_reflectsDiagnosticFreeOnSuccess
                      bodyReflects input method afterMethod methodResult
                        afterMethodFree
                    refine ⟨method :: methods, closingSpan, ?_,
                      .next
                        (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingPresent)
                        methodGrammar progress tailGrammar,
                      inputFree⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction

/-!
Every diagnostic-free implementation body follows the supplied exact block
grammar, including brace spans, method order, branch priority, and progress.
-/
theorem implBody_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ImplBody}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implBody input = .ok body next) :
    DeclarativeGrammar.ImplBodyParses bodyParses input.declarativeRemainder
      body.span body.methods next.declarativeRemainder := by
  unfold implBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases implMethods_success_sound_strong bodyParses bodyReflects bodySound
          opening (afterOpening.remainingCount + 1) [] afterOpening body next
          diagnosticFree result with
        ⟨methods, closingSpan, bodyEq, tailGrammar, afterOpeningFree⟩
      rw [bodyEq]
      simpa using DeclarativeGrammar.ImplBodyParses.parsed opening.span
        closingSpan
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        tailGrammar

/-- Implementation-body grammar soundness composes with source validity. -/
theorem implBody_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {body : ImplBody}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implBody input = .ok body next) :
    DeclarativeGrammar.ImplBodyParses bodyParses input.declarativeRemainder
        body.span body.methods next.declarativeRemainder ∧
      ImplBody.ValidFor statementValid input.file body := by
  refine ⟨implBody_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implBody_validFor statementValid bodyValid bodyWindow
    input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.ImplInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ImplDeclSoundnessProperties`
-/

/-! Parametric diagnostic-free soundness for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem implDeclSoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-!
Implementation parsing reflects diagnostic freedom whenever the isolated block
parser used by its methods does.  The nonempty-head refinement is included
explicitly so the whole executable bind chain remains visible.
-/
theorem implDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow))) :
    Parser.ReflectsDiagnosticFreeOnSuccess implDecl := by
  unfold implDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ImplInternals.implDefaultMarker_reflectsDiagnosticFreeOnSuccess
  intro defaultMarker
  unfold ImplInternals.implDeclAfterDefault
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .impl .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro traitName
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false typeExpr
      .typeExpr .topLevel typeExpr_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ImplInternals.requireImplArguments_reflectsDiagnosticFreeOnSuccess
      arguments)
  intro headArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro parsedWhereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ImplInternals.implBody_reflectsDiagnosticFreeOnSuccess bodyReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-!
Every diagnostic-free implementation success follows the exact optional
`default`, marker, head, where-clause, and method-body grammar.  Function bodies
remain abstract behind `bodyParses`.
-/
theorem implDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    DeclarativeGrammar.ImplDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold implDecl at result
  rcases implDeclSoundness_bind_ok_components result with
    ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
  unfold ImplInternals.implDeclAfterDefault at suffix
  rcases implDeclSoundness_bind_ok_components suffix with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨arguments, afterValues, valuesResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨headArguments, afterArguments, argumentsResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨parsedWhereClause, afterWhere, whereResult, rest⟩
  rcases implDeclSoundness_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (ImplInternals.implDefaultMarker_success_sound defaultResult)
    (contextual_success_exactTokenParses .impl .topItem markerResult)
    (optionalGenericParameters_success_sound genericsResult)
    (identifier_success_sound .topItem nameResult)
    (ImplInternals.implHeadArguments_success_sound valuesResult
      argumentsResult)
    (whereClause_success_sound whereResult)
    (ImplInternals.implBody_success_sound bodyParses bodyReflects bodySound
      diagnosticFree bodyResult)

/-! Parametric implementation grammar soundness composes with source validity. -/
theorem implDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    DeclarativeGrammar.ImplDeclParses bodyParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      ImplDecl.ValidFor statementValid input.file declaration := by
  refine ⟨implDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := implDecl_validFor statementValid bodyValid bodyWindow
    input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
