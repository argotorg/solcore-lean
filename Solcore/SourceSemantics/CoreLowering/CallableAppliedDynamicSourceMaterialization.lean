import Solcore.SourceSemantics.CoreLowering.CallableAppliedViewProvenance
import Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-!
Exact finite correspondence between independent source substitution and the
compiler's occurrence-sensitive requirement rewriting. Each applied edge
retains both authentic metadata parents and the actual read/application
factories. Earlier rewrites stay in the lexical metadata source; the independent
source receives only the same sequence of substitutions.

This relation can be produced from authenticated metadata ancestry. Identifying
its independent source with a live generalized cell still requires an allocation
and heap invariant. The final theorem consumes genuine GeneralizedClosureCaptures
at that independent source. It derives the actual closed header without assuming
full lexical source equality, rewrite invariance, method identity, or execution.
The materialization below uses the authenticated read substitution. A live
Dynamic use additionally needs extensional agreement with its actual
substitution: matching a permuted variable domain alone does not establish
that agreement. Literal substitution-list equality is not asserted.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryMetadata (eraseRequirements eraseNodeRequirements rewrite_erased)

abbrev Frame := SourceCoreCallablePairedFrames.Frame

/-- An exact source recipe at one authentic paired frame. The source index is
substituted independently; compiler metadata retains every actual rewrite. -/
inductive Pair {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    Frame → SourceCoreCallableAncestryReadRecipes.State → TypedSource → Prop where
  | named {id : Core.Word} {state : SourceCoreCallableAncestryReadRecipes.State}
      (selected : SourceCoreCallableAncestryPairedPreparation.named? inputs id = some state) :
      Pair inputs (.named id) state state.metadata.source
  | lambda {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource} {id : Core.Word}
      (prior : Pair inputs frame state source)
      (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) :
      Pair inputs (.lambda id frame) state source
  | applied {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State}
      {source : TypedSource} {id target : Core.Word}
      (prior : Pair inputs lexicalFrame lexical source)
      (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
        caller lexical id target) :
      Pair inputs (.appliedView id target callerFrame lexicalFrame)
        (recipe.read.after lexical) (source.applySubstitution recipe.read.substitution)

private def HasSource {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (frame : Frame) : Option SourceCoreCallableAncestryReadRecipes.State → Prop
  | none => True
  | some state => ∃ source, Pair inputs frame state source

private theorem authenticated_has_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : Option SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame state) :
    HasSource inputs frame state := by
  induction authenticated with
  | empty => trivial
  | named selected => exact ⟨_, .named selected⟩
  | lambda ancestry allowed ih =>
      obtain ⟨source, prior⟩ := ih
      exact ⟨source, .lambda prior allowed⟩
  | appliedView callerAncestry lexicalAncestry selected _callerIH lexicalIH =>
      obtain ⟨source, prior⟩ := lexicalIH
      obtain ⟨recipe, same⟩ :=
        CallableAppliedViewProvenance.Recipe.of_view callerAncestry lexicalAncestry selected
      cases same
      exact ⟨source.applySubstitution recipe.read.substitution, .applied prior recipe⟩

/-- The actual finite metadata derivation supplies this recipe. Its source is
an exact independently substituted candidate, not an asserted live heap value. -/
theorem of_authenticated
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (authenticated : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ source, Pair inputs frame state source :=
  authenticated_has_source authenticated

/-- Every previous substitution and rewrite is retained by induction. Only
expression requirement lists are erased; all other source fields stay exact. -/
theorem erase_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : Pair inputs frame state source) :
    eraseRequirements state.metadata.source = eraseRequirements source := by
  induction paired with
  | named _selected => rfl
  | lambda _prior _allowed ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _prior recipe ih =>
      change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements
        recipe.read.witnesses (lexical.metadata.source.applySubstitution recipe.read.substitution)) = _
      rw [rewrite_erased, CallableAncestryProfiles.erase_substitute,
        CallableAncestryProfiles.erase_substitute, ih]

/-- These are the two different exact source equations at a genuine step.
The lexical metadata on the right may already contain earlier rewrites. -/
theorem step_sources
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    (function : Dynamic.GeneralizedClosure) (evidence : Dynamic.EvidenceEnvironment) :
    (function.instantiate recipe.read.substitution evidence).source =
      function.source.applySubstitution recipe.read.substitution ∧
    (recipe.read.after lexical).metadata.source =
      SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
        (lexical.metadata.source.applySubstitution recipe.read.substitution) :=
  ⟨rfl, rfl⟩

private theorem lookup_erased {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    (eraseRequirements source).lookupExpression? id =
      some {node with requirements := []} := by
  unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found ⊢
  simp only [eraseRequirements, List.find?_map]
  have samePredicate :
      ((fun candidate => decide (candidate.occurrenceId = id.occurrence)) ∘
        eraseNodeRequirements) =
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) := by
    funext candidate
    cases candidate <;> rfl
  rw [samePredicate]
  cases selected : List.find?
      (fun candidate => decide (candidate.occurrenceId = id.occurrence)) source.nodes with
  | none => simp [selected] at found
  | some candidate =>
      cases candidate with
      | expression selectedNode =>
          simp [selected, eraseNodeRequirements] at found ⊢
          cases found
          simp
      | statement selectedNode => simp [selected] at found

/-- A real generalized capture at the independently tracked source attaches
one actual materialization. Uniqueness makes its declarative lambda occurrence
agree with the compiler's executable lookup. No full-source equality is needed.

Producing `paired` for the actual source retained by a live generalized cell is
one remaining heap/allocation attachment obligation. A real Dynamic use also
needs agreement of its substitution action with this read substitution; this
theorem does not derive it from a domain permutation. -/
theorem materialize
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {callerFrame lexicalFrame : Frame} {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    {id target : Core.Word}
    (paired : Pair inputs lexicalFrame lexical source)
    (recipe : CallableAppliedViewProvenance.Recipe inputs callerFrame lexicalFrame
      caller lexical id target)
    {context : Context} {captured : Dynamic.Environment} {binder : TypedBinder}
    {function : Dynamic.GeneralizedClosure}
    (captures : Dynamic.GeneralizedClosureCaptures context source captured binder
      recipe.read.entry.view.principal.initializer function)
    (unique : NodeOccurrencesUnique source) (evidence : Dynamic.EvidenceEnvironment) :
    Pair inputs (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) (function.instantiate recipe.read.substitution evidence).source ∧
    eraseRequirements (recipe.read.after lexical).metadata.source =
      eraseRequirements (function.instantiate recipe.read.substitution evidence).source ∧
    ExpressionForm.lambda (function.instantiate recipe.read.substitution evidence).parameters
      (function.instantiate recipe.read.substitution evidence).resultType
      (function.instantiate recipe.read.substitution evidence).body = recipe.read.template.node.form ∧
    (function.instantiate recipe.read.substitution evidence).captured = captured ∧
    (function.instantiate recipe.read.substitution evidence).evidence = evidence := by
  have sourceEq := captures.source_eq
  have initializerEq := captures.initializer_eq
  have transported : Pair inputs (.appliedView id target callerFrame lexicalFrame)
      (recipe.read.after lexical) (function.instantiate recipe.read.substitution evidence).source := by
    change Pair inputs _ _ (function.source.applySubstitution recipe.read.substitution)
    rw [sourceEq]
    exact .applied paired recipe
  obtain ⟨node, contains, form, _rawType, _type, _requirements, _coercions⟩ := captures.occurrence
  have found : source.lookupExpression? recipe.read.entry.view.principal.initializer = some node := by
    apply lookupExpression?_complete unique
    simpa only [sourceEq, initializerEq] using contains
  have nativeFound := lookup_erased recipe.applied.found
  have dynamicFound := lookup_erased found
  rw [erase_source paired] at nativeFound
  have nodeEq : ({recipe.applied.node with requirements := []} : ExpressionNode) =
      {node with requirements := []} :=
    Option.some.inj (nativeFound.symm.trans dynamicFound)
  have formsErased := congrArg ExpressionNode.form nodeEq
  have forms : recipe.applied.node.form = node.form := formsErased
  have sameHeader : ExpressionForm.lambda recipe.applied.parameters recipe.applied.resultType
      recipe.applied.body = ExpressionForm.lambda function.parameters function.resultType function.body :=
    recipe.applied.shape.symm.trans (forms.trans form)
  rcases ExpressionForm.lambda.inj sameHeader with ⟨parameters, resultType, body⟩
  have header := recipe.applied.nativeHeader
  rw [parameters, resultType, body] at header
  exact ⟨transported, erase_source transported, header, captures.captured_eq, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization
