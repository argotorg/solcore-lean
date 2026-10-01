import Solcore.Frontend.SourceCoreCallablePrincipals
import Solcore.Frontend.SourceCoreCallableViews
import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.Frontend.SourceCoreCallableContextFrames
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-! Independent metadata transport for dynamic callable ancestry. Owned
contracts, local-read receipts, and lambda templates determine finite metadata
recipes. Preparation may inspect source metadata and run the pure local-witness
factory; it never evaluates source code or resolves runtime dictionaries.

An authenticated frame describes a permitted metadata composition, not an
execution history. Native context-cell placement, closure-code/capture
ownership, and allocation-ledger provenance are separate obligations. A finite
cache below covers only its supplied frames; complete transition saturation for
arbitrary repeated frame nesting is deliberately not claimed.

Plain Dynamic.GeneralizedClosure.instantiate substitutes source types and
assembles independent evidence; it does not rewrite expression requirement IDs.
The occurrence-sensitive recipe here therefore is not asserted equal to that
entire dynamic closure. Their source views agree after forgetting requirement
IDs; exact source equality additionally requires rewrite invariance. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Frontend SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Key := SourceSpecialization.SpecializationKey
abbrev ContextFrame := SourceCoreCallableContextFrames.Frame
abbrev Witness := SourceCoreLocalEvidence.Witness
abbrev Lambda := SourceCoreLambdaTemplates.Lambda

inductive Error where
  | views (error : SourceCoreCallableViews.Error)
  | principals (error : SourceCoreCallablePrincipals.Error)
  | templates (error : SourceCoreLambdaTemplates.Error)
  | plan (error : SourceCompilationPlan.Error)
  | contractsUnavailable
  | unknownDescriptor (id : Core.Word)
  | wrongOrigin (id : Core.Word)
  | unknownView (id : Core.Word)
  | wrongTarget (view target : Core.Word)
  | invalidParent
  | invalidSource (id : ExpressionId)
  | invalidBinder (id : Resolved.LocalId)
  | wrongContext (owner : Key) (active : Substitution)
  | wrongSubstitution (id : Core.Word)
  deriving Repr

structure Owned {checked : Checked} (base : Base checked) where private mk ::
  views : SourceCoreCallableViews.Table base.sourceProgram base.plan
  viewsPrepared : SourceCoreCallableViews.prepare base = .ok views
  principals : SourceCoreCallablePrincipals.Table base.sourceProgram base.plan base.contexts
  principalsPrepared : SourceCoreCallablePrincipals.prepare base = .ok principals
  templates : SourceCoreLambdaTemplates.Inventory checked
  templatesPrepared : SourceCoreLambdaTemplates.prepare base = .ok templates
  callable : SourceCoreGeneralFunctions.CallableContext
  callableSelected : base.callableContext = some callable

/-- All tables come from the same sealed artifact. Dictionary resolution, if
required by those existing table factories, finishes here at preparation. -/
def prepare {checked : Checked} (base : Base checked) : Except Error (Owned base) := do
  match viewsPrepared : SourceCoreCallableViews.prepare base with
  | .error error => throw (.views error)
  | .ok views =>
    match principalsPrepared : SourceCoreCallablePrincipals.prepare base with
    | .error error => throw (.principals error)
    | .ok principals =>
      match templatesPrepared : SourceCoreLambdaTemplates.prepare base with
      | .error error => throw (.templates error)
      | .ok templates =>
        match callableSelected : base.callableContext with
        | none => throw .contractsUnavailable
        | some callable => pure ⟨views, viewsPrepared, principals, principalsPrepared,
            templates, templatesPrepared, callable, callableSelected⟩

structure State where
  owner : Key
  active : Substitution
  source : TypedSource
  deriving DecidableEq, Repr

/-- The independent composition law records exactly which substitution and
which occurrence-specific witnesses act on the preceding principal source. -/
inductive SourceRecipe : TypedSource → TypedSource → Prop where
  | unchanged (source : TypedSource) : SourceRecipe source source
  | instance {original current : TypedSource} (prior : SourceRecipe original current)
      (substitution : Substitution) (witnesses : List Witness) :
      SourceRecipe original (SourceTypedRuntime.rewriteLocalRequirements witnesses
        (current.applySubstitution substitution))

/-- Unlike the coarser allocation source view, this erases only expression
requirement lists and retains every type, coercion, form and source location. -/
def eraseNodeRequirements : Node → Node
  | .expression node => .expression {node with requirements := []}
  | .statement node => .statement node

def eraseRequirements (source : TypedSource) : TypedSource :=
  {source with nodes := source.nodes.map eraseNodeRequirements}

def nodeRequirements : Node → List RequirementId
  | .expression node => node.requirements
  | .statement _ => []

def requirementProfile (source : TypedSource) : List (List RequirementId) :=
  source.nodes.map nodeRequirements

theorem rewrite_erased (witnesses : List Witness) (source : TypedSource) :
    eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements witnesses source) = eraseRequirements source := by
  simp only [eraseRequirements, SourceTypedRuntime.rewriteLocalRequirements, List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

theorem dynamic_instantiate_erased (function : Dynamic.GeneralizedClosure)
    (substitution : Substitution) (evidence : Dynamic.EvidenceEnvironment) (witnesses : List Witness) :
    eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements witnesses
      (function.source.applySubstitution substitution)) =
      eraseRequirements (function.instantiate substitution evidence).source := rewrite_erased witnesses _

namespace FiniteProfiles

/-- Explicit finite enumeration of all requirement spines with a fixed length
and alphabet. This is a mathematical bound, not the preparation strategy. -/
def spines (alphabet : List RequirementId) : Nat → List (List RequirementId)
  | 0 => [[]]
  | length + 1 => alphabet.flatMap fun head => (spines alphabet length).map (head :: ·)

theorem spine_member {alphabet : List RequirementId} (requirements : List RequirementId)
    (bounded : ∀ id ∈ requirements, id ∈ alphabet) : requirements ∈ spines alphabet requirements.length := by
  induction requirements with
  | nil => simp [spines]
  | cons head tail ih =>
    apply List.mem_flatMap.mpr
    refine ⟨head, bounded head (by simp), ?_⟩
    apply List.mem_map.mpr
    exact ⟨tail, ih (fun id member => bounded id (by simp [member])), rfl⟩

def profiles (alphabet : List RequirementId) : List Nat → List (List (List RequirementId))
  | [] => [[]]
  | length :: rest => (spines alphabet length).flatMap fun first => (profiles alphabet rest).map (first :: ·)

theorem profile_member {alphabet : List RequirementId} (profile : List (List RequirementId))
    (bounded : ∀ spine ∈ profile, ∀ id ∈ spine, id ∈ alphabet) :
    profile ∈ profiles alphabet (profile.map List.length) := by
  induction profile with
  | nil => simp [profiles]
  | cons head tail ih =>
    apply List.mem_flatMap.mpr
    refine ⟨head, spine_member head (bounded head (by simp)), ?_⟩
    apply List.mem_map.mpr
    exact ⟨tail, ih (fun spine member => bounded spine (by simp [member])), rfl⟩

private theorem node_unique {left right : Node}
    (erased : eraseNodeRequirements left = eraseNodeRequirements right)
    (requirements : nodeRequirements left = nodeRequirements right) : left = right := by
  cases left with
  | expression left =>
    cases right with
    | statement right => cases erased
    | expression right =>
      cases left
      cases right
      simp_all [eraseNodeRequirements, nodeRequirements]
  | statement left =>
    cases right with
    | expression right => cases erased
    | statement right => exact erased

private theorem nodes_unique {left right : List Node}
    (erased : left.map eraseNodeRequirements = right.map eraseNodeRequirements)
    (requirements : left.map nodeRequirements = right.map nodeRequirements) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at erased
    | cons other rest =>
      simp only [List.map_cons, List.cons.injEq] at erased requirements
      rw [node_unique erased.1 requirements.1, ih erased.2 requirements.2]

theorem source_unique {left right : TypedSource}
    (erased : eraseRequirements left = eraseRequirements right)
    (requirements : requirementProfile left = requirementProfile right) : left = right := by
  cases left with
  | mk owner inputs roots nodes =>
    cases right with
    | mk otherOwner otherInputs otherRoots otherNodes =>
      simp only [eraseRequirements, TypedSource.mk.injEq] at erased
      rcases erased with ⟨rfl, rfl, rfl, erased⟩
      have same := nodes_unique erased requirements
      cases same
      rfl

/-- Under fixed erased source, spine lengths and a finite ID alphabet, this
finite profile list indexes every possible source uniquely. Establishing these
invariants for all reachable transitions is still required for saturation. -/
theorem source_profile_bound (canonical source : TypedSource) (alphabet : List RequirementId)
    (erased : eraseRequirements source = eraseRequirements canonical)
    (lengths : (requirementProfile source).map List.length = (requirementProfile canonical).map List.length)
    (bounded : ∀ spine ∈ requirementProfile source, ∀ id ∈ spine, id ∈ alphabet) :
    requirementProfile source ∈ profiles alphabet ((requirementProfile canonical).map List.length) ∧
      ∀ other, eraseRequirements other = eraseRequirements canonical →
        requirementProfile other = requirementProfile source → other = source := by
  constructor
  · rw [← lengths]
    exact profile_member _ bounded
  · intro other otherErased same
    exact source_unique (otherErased.trans erased.symm) same
end FiniteProfiles

/-- This theorem forgets requirement IDs only, and does not claim dictionary
or whole-program semantic preservation. -/
theorem rewrite_sourceView (witnesses : List Witness) (source : TypedSource) :
    SourceCoreAllocationCodebook.sourceView (SourceTypedRuntime.rewriteLocalRequirements witnesses source) =
      SourceCoreAllocationCodebook.sourceView source := by
  simp only [SourceCoreAllocationCodebook.sourceView, SourceTypedRuntime.rewriteLocalRequirements,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

theorem dynamic_instantiate_sourceView (function : Dynamic.GeneralizedClosure)
    (substitution : Substitution) (evidence : Dynamic.EvidenceEnvironment) (witnesses : List Witness) :
    SourceCoreAllocationCodebook.sourceView (SourceTypedRuntime.rewriteLocalRequirements witnesses
      (function.source.applySubstitution substitution)) =
      SourceCoreAllocationCodebook.sourceView (function.instantiate substitution evidence).source :=
  rewrite_sourceView witnesses _

theorem dynamic_instantiate_source_exact (function : Dynamic.GeneralizedClosure)
    (substitution : Substitution) (evidence : Dynamic.EvidenceEnvironment) (witnesses : List Witness)
    (unchanged : SourceTypedRuntime.rewriteLocalRequirements witnesses
      (function.source.applySubstitution substitution) = function.source.applySubstitution substitution) :
    SourceTypedRuntime.rewriteLocalRequirements witnesses (function.source.applySubstitution substitution) =
      (function.instantiate substitution evidence).source := unchanged

structure Named {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) where private mk ::
  entry : SourceCoreStageCodebook.Entry
  selected : owned.callable.table.entryAt? id = some entry
  owner : Key
  origin : entry.origin = .named owner
  caller : SourceSpecialization.SpecializedFunction
  found : SourceCompilationPlan.exactSpecialization base.plan owner = .ok caller

def Named.state {checked : Checked} {base : Base checked} {owned : Owned base} {id : Core.Word}
    (named : Named owned id) : State := ⟨named.owner, [], named.caller.function.typedBody⟩

private def named {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) :
    Except Error (Named owned id) := do
  match selected : owned.callable.table.entryAt? id with
  | none => throw (.unknownDescriptor id)
  | some entry =>
    match origin : entry.origin with
    | .named owner =>
      match found : SourceCompilationPlan.exactSpecialization base.plan owner with
      | .error error => throw (.plan error)
      | .ok caller => pure ⟨entry, selected, owner, origin, caller, found⟩
    | _ => throw (.wrongOrigin id)

structure LambdaAt {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) where private mk ::
  template : Lambda
  selected : owned.templates.lambdaAt? id = some template
  entry : SourceCoreStageCodebook.Entry
  descriptorSelected : owned.callable.table.entryAt? id = some entry
  origin : entry.origin = .lambda template.owner template.id template.active

private def lambdaAt {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) :
    Except Error (LambdaAt owned id) := do
  match selected : owned.templates.lambdaAt? id with
  | none => throw (.unknownDescriptor id)
  | some template =>
    match descriptorSelected : owned.callable.table.entryAt? id with
    | none => throw (.unknownDescriptor id)
    | some entry =>
      if origin : entry.origin = .lambda template.owner template.id template.active then
        pure ⟨template, selected, entry, descriptorSelected, origin⟩
      else throw (.wrongOrigin id)

structure ViewAt {checked : Checked} {base : Base checked} (owned : Owned base)
    (id target : Core.Word) where private mk ::
  entry : SourceCoreCallableViews.Entry base.sourceProgram base.plan
  selected : owned.views.entryAt? id = some entry
  targetLambda : LambdaAt owned target
  targetOrigin : targetLambda.entry.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative
  generalized : entry.view.wrapsPrincipal = true

private def viewAt {checked : Checked} {base : Base checked} (owned : Owned base) (id target : Core.Word) :
    Except Error (ViewAt owned id target) := do
  match selected : owned.views.entryAt? id with
  | none => throw (.unknownView id)
  | some entry =>
    let targetLambda ← lambdaAt owned target
    if targetOrigin : targetLambda.entry.origin = .lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative then
      if generalized : entry.view.wrapsPrincipal = true then
        pure ⟨entry, selected, targetLambda, targetOrigin, generalized⟩
      else throw (.wrongTarget id target)
    else throw (.wrongTarget id target)

/-- Preparation repeats the actual pure witness *factory* on the transported
occurrence metadata. It does not guess renamed witness IDs from equal types
and does not perform trait resolution during reconstruction. -/
structure ViewStep {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} (view : ViewAt owned id target) (before : State) where private mk ::
  owner : before.owner = view.entry.view.owner
  active : before.active = view.entry.view.parentActive
  caller : SourceSpecialization.SpecializedFunction
  callerFound : SourceCompilationPlan.exactSpecialization base.plan before.owner = .ok caller
  node : ExpressionNode
  found : before.source.lookupExpression? view.entry.view.read = some node
  name : String
  reference : node.form = .reference name (.local view.entry.view.binding.binder.id)
  binder : TypedBinder
  binderExact : binder = view.entry.view.binding.binder.applySubstitution before.active
  declaration : (⟨binder, view.entry.view.principal.initializer⟩ : SourceCoreCallablePrincipals.Declaration) ∈
    SourceCoreCallablePrincipals.declarations before.source
  requirements : List RequirementId
  requirementLayout : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  substitution : Substitution
  witnesses : List Witness
  factory : SourceCompilationPlan.localRequirementWitnesses caller view.entry.view.principal.evidence binder
    {node with type := node.rawType, requirements, coercions := []} = .ok (substitution, witnesses)
  substitutionExact : substitution = view.entry.view.ownSubstitution

namespace ViewStep
variable {checked : Checked} {base : Base checked} {owned : Owned base} {id target : Core.Word}
  {view : ViewAt owned id target} {before : State}
def after (step : ViewStep view before) : State :=
  ⟨before.owner, step.substitution.compose before.active,
    SourceTypedRuntime.rewriteLocalRequirements step.witnesses (before.source.applySubstitution step.substitution)⟩
theorem cumulative (step : ViewStep view before) : step.after.active = view.entry.view.cumulative := by
  change step.substitution.compose before.active = _
  rw [step.substitutionExact, step.active]
  exact view.entry.view.cumulativeExact.symm

theorem source_exact (step : ViewStep view before) :
    step.after.source = SourceTypedRuntime.rewriteLocalRequirements step.witnesses
      (before.source.applySubstitution step.substitution) := rfl

theorem recipe {original : TypedSource} (step : ViewStep view before) (prior : SourceRecipe original before.source) :
    SourceRecipe original step.after.source := .instance prior step.substitution step.witnesses
end ViewStep

private def prepareStep {checked : Checked} {base : Base checked} {owned : Owned base} {id target : Core.Word}
    (view : ViewAt owned id target) (before : State) : Except Error (ViewStep view before) := do
  if owner : before.owner = view.entry.view.owner then
    if active : before.active = view.entry.view.parentActive then
      match callerFound : SourceCompilationPlan.exactSpecialization base.plan before.owner with
      | .error error => throw (.plan error)
      | .ok caller =>
        match found : before.source.lookupExpression? view.entry.view.read with
        | none => throw (.invalidSource view.entry.view.read)
        | some node =>
          match reference : node.form with
          | .reference name (.local binderId) =>
            if sameBinder : binderId = view.entry.view.binding.binder.id then
              let binder := view.entry.view.binding.binder.applySubstitution before.active
              if declaration : (⟨binder, view.entry.view.principal.initializer⟩ : SourceCoreCallablePrincipals.Declaration) ∈
                  SourceCoreCallablePrincipals.declarations before.source then
                match requirementLayout : SourceCompilationPlan.ordinaryOwnedRequirements? node with
                | none => throw (.invalidSource node.id)
                | some requirements =>
                  match factory : SourceCompilationPlan.localRequirementWitnesses caller view.entry.view.principal.evidence binder
                      {node with type := node.rawType, requirements, coercions := []} with
                  | .error error => throw (.plan error)
                  | .ok (substitution, witnesses) =>
                    if substitutionExact : substitution = view.entry.view.ownSubstitution then
                      pure ⟨owner, active, caller, callerFound, node, found, name, sameBinder ▸ reference,
                        binder, rfl, declaration, requirements, requirementLayout, substitution, witnesses, factory, substitutionExact⟩
                    else throw (.wrongSubstitution id)
              else throw (.invalidBinder binderId)
            else throw (.invalidBinder binderId)
          | _ => throw (.invalidSource node.id)
    else throw (.wrongContext before.owner before.active)
  else throw (.wrongContext before.owner before.active)

/-- Lambda headers are selected from the transported whole source. Captured
source locations and native emitted code are deliberately absent. -/
structure LambdaSource {checked : Checked} {base : Base checked} {owned : Owned base} {id : Core.Word}
    (lambda : LambdaAt owned id) (state : State) where private mk ::
  owner : state.owner = lambda.template.owner
  active : state.active = lambda.template.active
  node : ExpressionNode
  found : state.source.lookupExpression? lambda.template.id = some node
  sameForm : node.form = lambda.template.node.form
  parameters : List TypedBinder
  resultType : Ty
  body : List StatementId
  shape : node.form = .lambda parameters resultType body

private def lambdaSource {checked : Checked} {base : Base checked} {owned : Owned base} {id : Core.Word}
    (lambda : LambdaAt owned id) (state : State) : Except Error (LambdaSource lambda state) := do
  if owner : state.owner = lambda.template.owner then
    if active : state.active = lambda.template.active then
      match found : state.source.lookupExpression? lambda.template.id with
      | none => throw (.invalidSource lambda.template.id)
      | some node =>
        if sameForm : node.form = lambda.template.node.form then
          match shape : node.form with
          | .lambda parameters resultType body => pure ⟨owner, active, node, found, sameForm, parameters, resultType, body, shape⟩
          | _ => throw (.invalidSource lambda.template.id)
        else throw (.invalidSource lambda.template.id)
    else throw (.wrongContext state.owner state.active)
  else throw (.wrongContext state.owner state.active)

/-- The cached canonical principal identifies the same declaration/header;
only its dynamic requirement view may differ. This certificate contains no
source locations and authenticates no native closure value. -/
structure PrincipalSource {checked : Checked} {base : Base checked} (owned : Owned base)
    (state : State) (binder : Resolved.LocalId) where private mk ::
  entry : SourceCoreCallablePrincipals.Entry base.sourceProgram base.plan base.contexts
  selected : owned.principals.find? state.owner state.active binder = some entry
  erased : eraseRequirements state.source = eraseRequirements entry.context.source
  node : ExpressionNode
  found : state.source.lookupExpression? entry.principal.declaration.initializer = some node
  shape : node.form = .lambda entry.principal.parameters entry.principal.resultType entry.principal.body

/-- Run while preparing metadata recipes, then cache the result alongside the
frame state. Exact source equality is deliberately not required here. -/
def preparePrincipal {checked : Checked} {base : Base checked} (owned : Owned base)
    (state : State) (binder : Resolved.LocalId) : Except Error (PrincipalSource owned state binder) := do
  match selected : owned.principals.find? state.owner state.active binder with
  | none => throw (.invalidBinder binder)
  | some entry =>
    if erased : eraseRequirements state.source = eraseRequirements entry.context.source then
      match found : state.source.lookupExpression? entry.principal.declaration.initializer with
      | none => throw (.invalidSource entry.principal.declaration.initializer)
      | some node =>
        if shape : node.form = .lambda entry.principal.parameters entry.principal.resultType entry.principal.body then
          pure ⟨entry, selected, erased, node, found, shape⟩
        else throw (.invalidSource node.id)
    else throw (.invalidBinder binder)

namespace PrincipalSource
variable {checked : Checked} {base : Base checked} {owned : Owned base} {state : State} {binder : Resolved.LocalId}
theorem canonical_recipe (principal : PrincipalSource owned state binder) :
    principal.entry.context.source = SourceTypedRuntime.rewriteLocalRequirements principal.entry.context.inherited
      (principal.entry.context.originalSource.applySubstitution principal.entry.context.active) := rfl

theorem dynamic_header (principal : PrincipalSource owned state binder) :
    ∃ node, state.source.lookupExpression? principal.entry.principal.declaration.initializer = some node ∧
      node.form = .lambda principal.entry.principal.parameters principal.entry.principal.resultType principal.entry.principal.body :=
  ⟨principal.node, principal.found, principal.shape⟩
end PrincipalSource

/-- Metadata consistency of a frame; this relation carries no premise or
conclusion that a runtime execution actually produced that frame. -/
inductive Authenticates {checked : Checked} {base : Base checked} (owned : Owned base) : ContextFrame → Option State → Prop where
  | empty : Authenticates owned .empty none
  | named {id : Core.Word} (receipt : Named owned id) : Authenticates owned (.named id) (some receipt.state)
  | lambda {id : Core.Word} {captured : ContextFrame} {state : State}
      (parent : Authenticates owned captured (some state)) (receipt : LambdaAt owned id)
      (metadata : LambdaSource receipt state) : Authenticates owned (.lambda id captured) (some state)
  | view {id target : Core.Word} {parent : ContextFrame} {state : State}
      (ancestry : Authenticates owned parent (some state)) (receipt : ViewAt owned id target)
      (step : ViewStep receipt state) : Authenticates owned (.view id target parent) (some step.after)

/-- Compile-time metadata preparation only. Runtime callers use an already
prepared cache. No source expression/statement evaluator is imported. -/
def prepareFrame {checked : Checked} {base : Base checked} (owned : Owned base) :
    (frame : ContextFrame) → Except Error {state : Option State // Authenticates owned frame state}
  | .empty => pure ⟨none, .empty⟩
  | .named id => do
    let receipt ← named owned id
    pure ⟨some receipt.state, .named receipt⟩
  | .lambda id captured => do
    let parent ← prepareFrame owned captured
    match parent with
    | ⟨none, _⟩ => throw .invalidParent
    | ⟨some state, ancestry⟩ =>
      let receipt ← lambdaAt owned id
      let metadata ← lambdaSource receipt state
      pure ⟨some state, .lambda ancestry receipt metadata⟩
  | .view id target parent => do
    let previous ← prepareFrame owned parent
    match previous with
    | ⟨none, _⟩ => throw .invalidParent
    | ⟨some state, ancestry⟩ =>
      let receipt ← viewAt owned id target
      let step ← prepareStep receipt state
      pure ⟨some step.after, .view ancestry receipt step⟩

/-- Every authenticated nonempty state has one owned named starting source
and a finite sequence of exact occurrence-sensitive source recipes. -/
theorem Authenticates.recipe {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : State} (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), SourceRecipe named.state.source state.source := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt => cases resultEq; exact ⟨_, receipt, .unchanged _⟩
  | lambda parent receipt metadata ih => exact ih resultEq
  | view parent receipt step ih =>
    cases resultEq
    obtain ⟨id, named, prior⟩ := ih rfl
    exact ⟨id, named, step.recipe prior⟩

theorem Authenticates.view_step {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {parent : ContextFrame} {after : State}
    (authenticated : Authenticates owned (.view id target parent) (some after)) :
    ∃ (before : State) (view : ViewAt owned id target) (step : ViewStep view before),
      Authenticates owned parent (some before) ∧ after = step.after := by
  cases authenticated with
  | view ancestry receipt step => exact ⟨_, receipt, step, ancestry, rfl⟩

theorem Authenticates.lambda_source {checked : Checked} {base : Base checked} {owned : Owned base}
    {id : Core.Word} {captured : ContextFrame} {state : State}
    (authenticated : Authenticates owned (.lambda id captured) (some state)) :
    ∃ (receipt : LambdaAt owned id) (metadata : LambdaSource receipt state),
      Authenticates owned captured (some state) ∧
      state.source.lookupExpression? receipt.template.id = some metadata.node ∧
      metadata.node.form = .lambda metadata.parameters metadata.resultType metadata.body := by
  cases authenticated with
  | lambda parent receipt metadata => exact ⟨receipt, metadata, parent, metadata.found, metadata.shape⟩

theorem sources_distinct {left right : TypedSource} {id : ExpressionId} {leftNode rightNode : ExpressionNode}
    (leftFound : left.lookupExpression? id = some leftNode)
    (rightFound : right.lookupExpression? id = some rightNode)
    (different : leftNode.requirements ≠ rightNode.requirements) : left ≠ right := by
  intro same
  subst right
  have nodeSame := Option.some.inj (leftFound.symm.trans rightFound)
  exact different (congrArg ExpressionNode.requirements nodeSame)

structure Row {checked : Checked} {base : Base checked} (owned : Owned base) where private mk ::
  frame : ContextFrame
  state : Option State
  authenticated : Authenticates owned frame state

structure Cache {checked : Checked} {base : Base checked} (owned : Owned base) where private mk ::
  rows : List (Row owned)

def prepareCache {checked : Checked} {base : Base checked} (owned : Owned base) (frames : List ContextFrame) :
    Except Error (Cache owned) := do
  let rows ← frames.mapM fun frame => do
    let result ← prepareFrame owned frame
    pure (⟨frame, result.val, result.property⟩ : Row owned)
  pure ⟨rows⟩

/-- Reconstruction only selects cached metadata; it performs no source
traversal, type substitution, witness matching, or dictionary resolution. -/
def Cache.lookup? {checked : Checked} {base : Base checked} {owned : Owned base}
    (cache : Cache owned) (frame : ContextFrame) : Option (Row owned) :=
  cache.rows.find? (fun row => decide (row.frame = frame))

theorem Cache.lookup?_authenticates {checked : Checked} {base : Base checked} {owned : Owned base}
    (cache : Cache owned) {frame : ContextFrame} {row : Row owned}
    (found : cache.lookup? frame = some row) : row ∈ cache.rows ∧ Authenticates owned frame row.state := by
  have tested := List.find?_some found
  have equal : row.frame = frame := of_decide_eq_true tested
  exact ⟨List.mem_of_find?_eq_some found, equal ▸ row.authenticated⟩

/-- A cached principal retains the exact root/parent metadata recipe. This is
independent of whether its runtime native bundle contains any lambdas. -/
theorem principal_recipe {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {parents : List SourceCoreLocalEvidence.Prepared}
    (entry : SourceCoreCallablePrincipals.Entry program plan parents) :
    SourceRecipe entry.context.originalSource entry.context.source :=
  .instance (.unchanged _) entry.context.active entry.context.inherited

end Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
