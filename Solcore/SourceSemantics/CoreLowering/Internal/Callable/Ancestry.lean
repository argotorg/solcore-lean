import Solcore.Frontend.SourceCoreCallablePrincipals
import Solcore.Frontend.SourceCoreCallableViews
import Solcore.Frontend.SourceCoreLambdaTemplates
import Solcore.Frontend.SourceCoreCallableContextFrames
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.CoreLowering.EmptySourceSubstitution
import Solcore.TypeSystem.SubstitutionProperties

/-!
# Callable ancestry

Ancestry metadata, profiles and composition.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
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

def named {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) :
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

def lambdaAt {checked : Checked} {base : Base checked} (owned : Owned base) (id : Core.Word) :
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

def viewAt {checked : Checked} {base : Base checked} (owned : Owned base) (id target : Core.Word) :
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

def prepareStep {checked : Checked} {base : Base checked} {owned : Owned base} {id target : Core.Word}
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

def lambdaSource {checked : Checked} {base : Base checked} {owned : Owned base} {id : Core.Word}
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
/-! Invariants for occurrence-sensitive callable ancestry metadata. These
proofs concern retained metadata only: they do not evaluate source bodies or
resolve dictionaries during a runtime call. A requirement profile records the
actual IDs at every occurrence, rather than identifying equal types with equal
source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item, item ∈ items → ∀ state outcome, invariant state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant updated) : invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item items ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

def alphabet (source : TypedSource) : List RequirementId :=
  (requirementProfile source).flatten

def Bounded (ids : List RequirementId) (source : TypedSource) : Prop :=
  ∀ spine ∈ requirementProfile source, ∀ requirement ∈ spine, requirement ∈ ids

theorem bounded_alphabet (source : TypedSource) : Bounded (alphabet source) source := by
  intro spine member requirement occurs
  exact List.mem_flatten.mpr ⟨spine, member, occurs⟩

@[simp] theorem profile_substitute (source : TypedSource) (substitution : Substitution) :
    requirementProfile (source.applySubstitution substitution) = requirementProfile source := by
  simp only [requirementProfile, TypedSource.applySubstitution, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

@[simp] theorem profile_rewrite (source : TypedSource) (witnesses : List Witness) :
    requirementProfile (SourceTypedRuntime.rewriteLocalRequirements witnesses source) =
      (requirementProfile source).map (List.map (SourceTypedRuntime.rewriteLocalRequirement witnesses)) := by
  simp only [requirementProfile, SourceTypedRuntime.rewriteLocalRequirements, List.map_map]
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

@[simp] theorem lengths_rewrite (source : TypedSource) (witnesses : List Witness) :
    (requirementProfile (SourceTypedRuntime.rewriteLocalRequirements witnesses source)).map List.length =
      (requirementProfile source).map List.length := by
  simp only [profile_rewrite, List.map_map, Function.comp_def, List.length_map]

theorem SourceRecipe.lengths {original source : TypedSource} (recipe : SourceRecipe original source) :
    (requirementProfile source).map List.length = (requirementProfile original).map List.length := by
  induction recipe with
  | unchanged => rfl
  | «instance» _ _ _ ih => rw [lengths_rewrite, profile_substitute]; exact ih

theorem ViewStep.lengths {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State} (step : ViewStep view before) :
    (requirementProfile step.after.source).map List.length = (requirementProfile before.source).map List.length := by
  simp [ViewStep.after]

theorem rewrite_id_bounded {ids : List RequirementId} {witnesses : List Witness}
    (witnessesBounded : ∀ witness ∈ witnesses, witness.actualRequirement ∈ ids)
    {requirement : RequirementId} (member : requirement ∈ ids) :
    SourceTypedRuntime.rewriteLocalRequirement witnesses requirement ∈ ids := by
  unfold SourceTypedRuntime.rewriteLocalRequirement
  split
  · next witness found => exact witnessesBounded witness (List.mem_of_find?_eq_some found)
  · exact member

theorem bounded_rewrite {ids : List RequirementId} {source : TypedSource} {witnesses : List Witness}
    (sourceBounded : Bounded ids source)
    (witnessesBounded : ∀ witness ∈ witnesses, witness.actualRequirement ∈ ids) :
    Bounded ids (SourceTypedRuntime.rewriteLocalRequirements witnesses source) := by
  intro spine member requirement occurs
  rw [profile_rewrite] at member
  obtain ⟨oldSpine, oldMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨oldRequirement, oldOccurs, rfl⟩ := List.mem_map.mp occurs
  exact rewrite_id_bounded witnessesBounded (sourceBounded oldSpine oldMember oldRequirement oldOccurs)

theorem bounded_substitute {ids : List RequirementId} {source : TypedSource}
    (bounded : Bounded ids source) (substitution : Substitution) :
    Bounded ids (source.applySubstitution substitution) := by
  simpa only [Bounded, profile_substitute] using bounded

theorem lookup_requirements_bounded {ids : List RequirementId} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} (bounded : Bounded ids source)
    (found : source.lookupExpression? id = some node) :
    ∀ requirement ∈ node.requirements, requirement ∈ ids := by
  have member : Node.expression node ∈ source.nodes := by
    unfold TypedSource.lookupExpression? TypedSource.lookupNode? at found
    split at found
    · next selected selectedEq =>
      cases found
      exact List.mem_of_find?_eq_some selectedEq
    · cases found
  exact bounded node.requirements (List.mem_map.mpr ⟨.expression node, member, rfl⟩)

theorem ordinary_requirements_subset {node : ExpressionNode} {requirements : List RequirementId}
    (accepted : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements) :
    ∀ requirement ∈ requirements, requirement ∈ node.requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements? at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
      intro requirement member
      exact List.mem_of_mem_take member
    · cases accepted

@[simp] theorem erase_substitute (source : TypedSource) (substitution : Substitution) :
    eraseRequirements (source.applySubstitution substitution) =
      (eraseRequirements source).applySubstitution substitution := by
  simp only [eraseRequirements, TypedSource.applySubstitution, List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  cases node <;> rfl

theorem ViewStep.erase {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) :
    eraseRequirements step.after.source =
      (eraseRequirements before.source).applySubstitution view.entry.view.ownSubstitution := by
  change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements step.witnesses
    (before.source.applySubstitution step.substitution)) = _
  rw [rewrite_erased, erase_substitute, step.substitutionExact]

/-- A canonical source is transported by the actual selected view's exact
substitution. This law does not assume arbitrary source substitutions commute
with quantified binders, nor erase the occurrence-specific requirement IDs. -/
theorem ViewStep.canonical {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {canonical : TypedSource}
    (beforeCanonical : eraseRequirements before.source = eraseRequirements canonical) :
    step.after.owner = view.entry.view.owner ∧ step.after.active = view.entry.view.cumulative ∧
      eraseRequirements step.after.source =
        eraseRequirements (canonical.applySubstitution view.entry.view.ownSubstitution) := by
  refine ⟨step.owner, step.cumulative, ?_⟩
  rw [ViewStep.erase step, beforeCanonical, erase_substitute]

/-- Every actual ID emitted by the real matching loop is taken from the
reference's requirement spine. Predicate and dictionary checks cannot invent
new occurrence identities. -/
theorem bindings_actual_subset {caller : SourceSpecialization.SpecializedFunction}
    {binder : TypedBinder} {node : ExpressionNode} {substitution : Substitution}
    {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)) :
    ∀ binding ∈ bindings, binding.actualRequirement ∈ node.requirements := by
  unfold SourceCompilationPlan.localRequirementBindings at accepted
  simp (maxSteps := 1000000) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨final, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant (invariant := fun current => ∀ binding ∈ current, binding.actualRequirement ∈ node.requirements) loop
  · simp
  · intro pair member current outcome prior iteration
    rcases pair with ⟨template, actual⟩
    have actualMember : actual ∈ node.requirements := List.of_mem_zip member |>.2
    try dsimp only at iteration
    obtain ⟨templateSolved, _, iteration⟩ := bind_ok iteration
    try dsimp only at iteration
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    obtain ⟨actualSolved, _, iteration⟩ := bind_ok iteration
    try dsimp only at iteration
    split at iteration <;> try contradiction
    split at iteration <;> try contradiction
    cases iteration
    refine ⟨_, rfl, ?_⟩
    intro binding member
    rcases List.mem_append.mp member with old | fresh
    · exact prior binding old
    · cases List.mem_singleton.mp fresh
      exact actualMember

theorem witnesses_actual_subset {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    ∀ witness ∈ witnesses, witness.actualRequirement ∈ node.requirements := by
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨matched, bindings⟩, bound, accepted⟩ := bind_ok accepted
  obtain ⟨final, loop, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant (invariant := fun current => ∀ witness ∈ current, witness.actualRequirement ∈ node.requirements) loop
  · simp
  · intro binding member current outcome prior iteration
    have actualMember := bindings_actual_subset bound binding member
    dsimp only at iteration
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at iteration
    split at iteration
    · next evidence caseEq =>
      cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness member
      rcases List.mem_append.mp member with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact actualMember
    · split at iteration <;> try contradiction
      cases iteration
      refine ⟨_, rfl, ?_⟩
      intro witness member
      rcases List.mem_append.mp member with old | fresh
      · exact prior witness old
      · cases List.mem_singleton.mp fresh
        exact actualMember

theorem ViewStep.actual_ids_bounded {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {ids : List RequirementId} (bounded : Bounded ids before.source) :
    ∀ witness ∈ step.witnesses, witness.actualRequirement ∈ ids := by
  intro witness member
  have selected := witnesses_actual_subset step.factory witness member
  have owned := ordinary_requirements_subset step.requirementLayout witness.actualRequirement selected
  exact lookup_requirements_bounded bounded step.found _ owned

theorem ViewStep.bounded {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) {ids : List RequirementId} (bounded : Bounded ids before.source) :
    Bounded ids step.after.source :=
  bounded_rewrite (bounded_substitute bounded step.substitution) (ViewStep.actual_ids_bounded step bounded)

/-- The actual factories keep every reachable expression requirement inside
the original named source's finite alphabet, for arbitrary finite ancestry
depth. No supplied witness-range or child evaluation premise is needed. -/
theorem Authenticates.original_bound {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      Bounded (alphabet named.state.source) state.source ∧
      (requirementProfile state.source).map List.length = (requirementProfile named.state.source).map List.length := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt => cases resultEq; exact ⟨_, receipt, rfl, bounded_alphabet _, rfl⟩
  | lambda parent receipt metadata ih => exact ih resultEq
  | view parent receipt step ih =>
    cases resultEq
    obtain ⟨id, named, owner, bounded, lengths⟩ := ih rfl
    exact ⟨id, named, owner, ViewStep.bounded step bounded, (ViewStep.lengths step).trans lengths⟩



end Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
/-! Composition through quantified source metadata requires closed substitution
ranges. These syntax laws do not assert dictionary or execution correctness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
open Frontend SourceInference TypeSystem
open CallableAncestryMetadata

namespace SourceComposition

private theorem except_bind {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

def RangesClosed (substitution : Substitution) : Prop :=
  ∀ entry ∈ substitution, entry.2.freeVariables = []

theorem RangesClosed.without {substitution : Substitution} (closed : RangesClosed substitution)
    (variables : List TypeVarId) : RangesClosed (substitution.without variables) :=
  fun entry member => closed entry (Substitution.mem_of_mem_without member)

theorem fixed {type : Ty} (closed : type.freeVariables = []) (substitution : Substitution) :
    substitution.apply type = type :=
  Ty.apply_eq_self_of_domain_disjoint_freeVariables substitution type (by simp [closed])

theorem lookup_without (substitution : Substitution) (variables : List TypeVarId) (metavariable : TypeVarId) :
    (substitution.without variables).lookup? metavariable =
      if metavariable ∈ variables then none else substitution.lookup? metavariable := by
  by_cases member : metavariable ∈ variables
  · simp [member, Substitution.lookup?_without_of_mem substitution member]
  · rw [if_neg member]
    induction variables generalizing substitution with
    | nil => rfl
    | cons head rest ih =>
      change ((substitution.erase head).without rest).lookup? metavariable = _
      rw [ih (substitution.erase head) (by simp_all)]
      exact Substitution.lookup?_erase_of_ne substitution (by simp_all)

theorem apply_lookup_congr {left right : Substitution}
    (same : ∀ metavariable, left.lookup? metavariable = right.lookup? metavariable) (type : Ty) :
    left.apply type = right.apply type := by
  induction type <;> simp_all [Substitution.apply]

theorem mask_twice (substitution : Substitution) (variables : List TypeVarId) (type : Ty) :
    ((substitution.without variables).without variables).apply type =
      (substitution.without variables).apply type := by
  apply apply_lookup_congr
  intro metavariable
  simp only [lookup_without]
  split <;> rfl

/-- Closed earlier replacements cannot introduce a quantified metavariable into
a binder. This is the additional condition needed beyond type composition. -/
theorem masked_compose (newer older : Substitution) (closed : RangesClosed older)
    (variables : List TypeVarId) (type : Ty) :
    ((newer.compose older).without variables).apply type =
      (newer.without variables).apply ((older.without variables).apply type) := by
  induction type with
  | «variable» metavariable =>
    by_cases boundKey : metavariable ∈ variables
    · simp [Substitution.apply, lookup_without, boundKey]
    · cases found : older.lookup? metavariable with
      | none => simp [Substitution.apply, lookup_without, boundKey, Substitution.lookup?_compose, found]
      | some replacement =>
        have range := closed (metavariable, replacement) (Substitution.lookup?_eq_some_mem found)
        simp [Substitution.apply, lookup_without, boundKey, Substitution.lookup?_compose, found,
          fixed range newer, fixed range (newer.without variables)]
  | parameter | constructor | error => rfl
  | application _ _ left right | function _ _ left right | product _ _ left right | mapping _ _ left right =>
    simp only [Substitution.apply, left, right]
  | proxy _ ih | comptime _ ih => simp only [Substitution.apply, ih]

theorem scheme (newer older : Substitution) (closed : RangesClosed older) (value : Scheme) :
    value.apply (newer.compose older) = (value.apply older).apply newer := by
  simp only [Scheme.apply]
  rw [masked_compose newer older closed]

@[simp] theorem predicate (newer older : Substitution) (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution (newer.compose older) value =
      TypedTraitResolution.applySubstitution newer (TypedTraitResolution.applySubstitution older value) := by
  simp only [TypedTraitResolution.applySubstitution, Substitution.compose_apply, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro type _
  exact Substitution.compose_apply newer older type

theorem masked_predicate (newer older : Substitution) (closed : RangesClosed older)
    (variables : List TypeVarId) (value : ProgramPredicate) :
    TypedTraitResolution.applySubstitution ((newer.compose older).without variables) value =
      TypedTraitResolution.applySubstitution (newer.without variables)
        (TypedTraitResolution.applySubstitution (older.without variables) value) := by
  simp only [TypedTraitResolution.applySubstitution, masked_compose newer older closed,
    List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro type _
  exact masked_compose newer older closed variables type

@[simp] theorem requirement (newer older : Substitution) (value : LocalSchemeRequirement) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [LocalSchemeRequirement.applySubstitution]

@[simp] theorem binder (newer older : Substitution) (closed : RangesClosed older) (value : TypedBinder) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp only [TypedBinder.applySubstitution, Scheme.apply, mask_twice]
  rw [masked_compose newer older closed]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro requirement _
  simp only [Function.comp_def, LocalSchemeRequirement.applySubstitution, masked_predicate newer older closed]

@[simp] theorem type_function (newer older : Substitution) :
    Substitution.apply (newer.compose older) = (fun type => newer.apply (older.apply type)) :=
  funext (Substitution.compose_apply newer older)

@[simp] theorem predicate_function (newer older : Substitution) :
    TypedTraitResolution.applySubstitution (newer.compose older) =
      (fun value => TypedTraitResolution.applySubstitution newer (TypedTraitResolution.applySubstitution older value)) :=
  funext (predicate newer older)

theorem binder_function (newer older : Substitution) (closed : RangesClosed older) :
    TypedBinder.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (binder newer older closed)

@[simp] theorem integerResolution (newer older : Substitution) (value : IntegerLiteralResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [IntegerLiteralResolution.applySubstitution]

@[simp] theorem declaration (newer older : Substitution) (value : DeclarationInstantiation) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  unfold DeclarationInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, (newer.compose older).apply p.2))
    type := (newer.compose older).apply value.type
    predicates := value.predicates.map (TypedTraitResolution.applySubstitution (newer.compose older)) } =
    { value with
      parameterSubstitution := (value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, older.apply p.2))).map (fun (p : TypeParameterId × Ty) => (p.1, newer.apply p.2))
      type := newer.apply (older.apply value.type)
      predicates := (value.predicates.map (TypedTraitResolution.applySubstitution older)).map (TypedTraitResolution.applySubstitution newer) }
  simp [List.map_map, Function.comp_def]

@[simp] theorem constructor (newer older : Substitution) (value : DataConstructorInstantiation) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  unfold DataConstructorInstantiation.applySubstitution
  change { value with
    parameterSubstitution := value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, (newer.compose older).apply p.2))
    payloadTypes := value.payloadTypes.map (Substitution.apply (newer.compose older))
    resultType := (newer.compose older).apply value.resultType } =
    { value with
      parameterSubstitution := (value.parameterSubstitution.map (fun (p : TypeParameterId × Ty) => (p.1, older.apply p.2))).map (fun (p : TypeParameterId × Ty) => (p.1, newer.apply p.2))
      payloadTypes := (value.payloadTypes.map (Substitution.apply older)).map (Substitution.apply newer)
      resultType := newer.apply (older.apply value.resultType) }
  simp [List.map_map, Function.comp_def]

@[simp] theorem coercion (newer older : Substitution) (value : CoercionStep) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [CoercionStep.applySubstitution]

@[simp] theorem coercion_function (newer older : Substitution) :
    CoercionStep.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (coercion newer older)

@[simp] theorem indirect (newer older : Substitution) (value : IndirectCallResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value
  simp [IndirectCallResolution.applySubstitution]

@[simp] theorem reference (newer older : Substitution) (value : ReferenceResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ReferenceResolution.applySubstitution]

@[simp] theorem call (newer older : Substitution) (value : CallResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [CallResolution.applySubstitution]

@[simp] theorem expressionForm (newer older : Substitution) (closed : RangesClosed older) (value : ExpressionForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ExpressionForm.applySubstitution, binder_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem expression (newer older : Substitution) (closed : RangesClosed older) (value : ExpressionNode) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [ExpressionNode.applySubstitution, expressionForm newer older closed, List.map_map, Function.comp_def]

@[simp] theorem instruction (newer older : Substitution) (closed : RangesClosed older) (value : MatchPatternInstruction) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [MatchPatternInstruction.applySubstitution, binder newer older closed]

theorem instruction_function (newer older : Substitution) (closed : RangesClosed older) :
    MatchPatternInstruction.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (instruction newer older closed)

@[simp] theorem resolution (newer older : Substitution) (closed : RangesClosed older) (value : MatchPatternResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [MatchPatternResolution.applySubstitution, binder newer older closed,
    instruction_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem pattern (newer older : Substitution) (closed : RangesClosed older) (value : TypedMatchPattern) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedMatchPattern.applySubstitution, resolution newer older closed]

@[simp] theorem matchCase (newer older : Substitution) (closed : RangesClosed older) (value : TypedMatchCase) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedMatchCase.applySubstitution, pattern newer older closed]

theorem matchCase_function (newer older : Substitution) (closed : RangesClosed older) :
    TypedMatchCase.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (matchCase newer older closed)

@[simp] theorem matchResolution (newer older : Substitution) (closed : RangesClosed older) (value : MatchResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [MatchResolution.applySubstitution, matchCase_function newer older closed, List.map_map, Function.comp_def]

@[simp] theorem place (newer older : Substitution) (value : PlaceResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [PlaceResolution.applySubstitution]

@[simp] theorem assignment (newer older : Substitution) (value : AssignmentResolution) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [AssignmentResolution.applySubstitution]

@[simp] theorem forItem (newer older : Substitution) (closed : RangesClosed older) (value : ForItemForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [ForItemForm.applySubstitution, binder newer older closed]

theorem forItem_function (newer older : Substitution) (closed : RangesClosed older) :
    ForItemForm.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (forItem newer older closed)

@[simp] theorem statementForm (newer older : Substitution) (closed : RangesClosed older) (value : StatementForm) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [StatementForm.applySubstitution, binder newer older closed,
    forItem_function newer older closed, matchResolution newer older closed, List.map_map, Function.comp_def]

@[simp] theorem statement (newer older : Substitution) (closed : RangesClosed older) (value : StatementNode) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [StatementNode.applySubstitution, statementForm newer older closed]

@[simp] theorem node (newer older : Substitution) (closed : RangesClosed older) (value : Node) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  cases value <;> simp [Node.applySubstitution, expression newer older closed, statement newer older closed]

theorem node_function (newer older : Substitution) (closed : RangesClosed older) :
    Node.applySubstitution (newer.compose older) =
      (fun value => (value.applySubstitution older).applySubstitution newer) := funext (node newer older closed)

theorem source (newer older : Substitution) (closed : RangesClosed older) (value : TypedSource) :
    value.applySubstitution (newer.compose older) = (value.applySubstitution older).applySubstitution newer := by
  simp [TypedSource.applySubstitution, binder_function newer older closed,
    node_function newer older closed, List.map_map, Function.comp_def]

theorem RangesClosed.empty : RangesClosed [] := by intro entry member; cases member

theorem RangesClosed.compose {older newer : Substitution}
    (oldClosed : RangesClosed older) (newClosed : RangesClosed newer) : RangesClosed (newer.compose older) := by
  intro ⟨metavariable, replacement⟩ member
  rcases Substitution.mem_compose_iff.mp member with ⟨previous, oldMember, rfl⟩ | ⟨newMember, _⟩
  · rw [fixed (oldClosed _ oldMember) newer]
    exact oldClosed _ oldMember
  · exact newClosed _ newMember

theorem bindings_matched {caller : SourceSpecialization.SpecializedFunction}
    {binder : TypedBinder} {node : ExpressionNode} {substitution : Substitution}
    {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (accepted : SourceCompilationPlan.localRequirementBindings caller binder node = .ok (substitution, bindings)) :
    SourceSpecialization.matchClosedSchemeInstance? binder.scheme node.rawType = some substitution := by
  unfold SourceCompilationPlan.localRequirementBindings at accepted
  simp (maxSteps := 1000000) only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i matched matchEq
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  obtain ⟨final, _, accepted⟩ := except_bind accepted
  cases accepted
  exact matchEq

theorem witnesses_matched {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    SourceSpecialization.matchClosedSchemeInstance? binder.scheme node.rawType = some substitution := by
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨matched, bindings⟩, selected, accepted⟩ := except_bind accepted
  obtain ⟨final, _, accepted⟩ := except_bind accepted
  cases accepted
  exact bindings_matched selected

/-- The real structural matcher only adds types occurring in the actual
closed type. Existing assignments retain their already established closure. -/
theorem matchBody_closed (quantified : List TypeVarId) (expected actual : Ty)
    {initial final : Substitution} (initialClosed : RangesClosed initial)
    (actualClosed : actual.freeVariables = [])
    (matched : Scheme.matchBody? quantified expected actual initial = some final) : RangesClosed final := by
  induction expected generalizing actual initial final with
  | «variable» metavariable =>
    simp only [Scheme.matchBody?] at matched
    split at matched
    · split at matched
      · split at matched <;> try contradiction
        cases matched
        exact initialClosed
      · cases matched
        intro entry member
        rcases List.mem_cons.mp member with rfl | previous
        · exact actualClosed
        · exact initialClosed entry previous
    · split at matched <;> try contradiction
      cases matched
      exact initialClosed
  | parameter | constructor =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    split at matched <;> try contradiction
    cases matched
    exact initialClosed
  | error =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    cases matched
    exact initialClosed
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    rename_i actualLeft actualRight
    have closedParts : actualLeft.freeVariables = [] ∧ actualRight.freeVariables = [] := by
      simp only [List.eq_nil_iff_forall_not_mem] at actualClosed ⊢
      constructor <;> intro metavariable occurs <;> apply actualClosed metavariable <;> simp [occurs]
    obtain ⟨middle, leftMatched, rightMatched⟩ := Option.bind_eq_some_iff.mp matched
    exact ihRight actualRight (ihLeft actualLeft initialClosed closedParts.1 leftMatched) closedParts.2 rightMatched
  | proxy inner ih | comptime inner ih =>
    cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
    rename_i actualInner
    exact ih actualInner initialClosed actualClosed matched

private theorem mapM_closed {matched : Substitution} (closed : RangesClosed matched)
    {variables : List TypeVarId} {result : Substitution}
    (accepted : variables.mapM (fun metavariable => do
      pure (metavariable, ← matched.lookup? metavariable)) = some result) : RangesClosed result := by
  induction variables generalizing result with
  | nil => cases accepted; exact RangesClosed.empty
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest, remainder, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    cases accepted
    cases lookup : matched.lookup? head with
    | none => simp [lookup] at found
    | some replacement =>
      simp only [lookup, pure, bind, Option.bind, Option.some.injEq] at found
      cases found
      intro entry member
      rcases List.mem_cons.mp member with rfl | previous
      · exact closed _ (Substitution.lookup?_eq_some_mem lookup)
      · exact ih remainder entry previous

theorem matchInstance_closed {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (actualClosed : actual.freeVariables = [])
    (matched : scheme.matchInstance? actual = some substitution) : RangesClosed substitution := by
  unfold Scheme.matchInstance? at matched
  cases certified : Scheme.matchInstanceCertificate? scheme actual with
  | none => simp [certified] at matched
  | some certificate =>
    simp only [certified, Option.map_some, Option.some.injEq] at matched
    subst substitution
    unfold Scheme.matchInstanceCertificate? at certified
    split at certified <;> try contradiction
    obtain ⟨first, shape, certified⟩ := Option.bind_eq_some_iff.mp certified
    obtain ⟨reordered, ordering, certified⟩ := Option.bind_eq_some_iff.mp certified
    have closed := mapM_closed (matchBody_closed scheme.quantified scheme.body actual RangesClosed.empty actualClosed shape) ordering
    split at certified <;> try contradiction
    split at certified <;> try contradiction
    cases certified
    exact closed

theorem concrete_closed {actual : Ty} (concrete : SourceSpecialization.firstNonConcrete actual = none) :
    actual.freeVariables = [] := by
  induction actual with
  | «variable» => cases concrete
  | parameter | constructor | error => rfl
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
    simp only [SourceSpecialization.firstNonConcrete] at concrete
    cases leftConcrete : SourceSpecialization.firstNonConcrete left with
    | some issue => simp [leftConcrete] at concrete
    | none =>
      have rightConcrete : SourceSpecialization.firstNonConcrete right = none := by simpa [leftConcrete] using concrete
      have leftClosed := ihLeft leftConcrete
      have rightClosed := ihRight rightConcrete
      simp only [List.eq_nil_iff_forall_not_mem] at leftClosed rightClosed ⊢
      intro metavariable
      simp [leftClosed metavariable, rightClosed metavariable]
  | proxy _ ih | comptime _ ih => exact ih concrete

theorem matchClosed_ranges {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some substitution) : RangesClosed substitution := by
  have concrete := (SourceSpecialization.matchClosedSchemeInstance?_sound matched).1
  apply matchInstance_closed (concrete_closed concrete)
  simpa [SourceSpecialization.matchClosedSchemeInstance?, concrete] using matched

theorem ViewStep.rangesClosed {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target} {before : CallableAncestryMetadata.State}
    (step : ViewStep view before) : RangesClosed step.substitution :=
  matchClosed_ranges (witnesses_matched step.factory)

/-- An actual authenticated ancestry source agrees, after requirement erasure,
with its owned original source under the full cumulative type substitution.
Closed range evidence comes from the actual matcher, not an extra caller law. -/
theorem Authenticates.canonical {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      RangesClosed state.active ∧
      eraseRequirements state.source = eraseRequirements (named.state.source.applySubstitution state.active) := by
  generalize resultEq : some state = result at authenticated
  induction authenticated generalizing state with
  | empty => cases resultEq
  | named receipt =>
    cases resultEq
    exact ⟨_, receipt, rfl, RangesClosed.empty, by simp only [Named.state, EmptySourceSubstitution.source]⟩
  | lambda parent receipt metadata ih => exact ih resultEq
  | view parent receipt step ih =>
    cases resultEq
    obtain ⟨id, named, owner, closed, canonical⟩ := ih rfl
    refine ⟨id, named, owner, RangesClosed.compose closed (ViewStep.rangesClosed step), ?_⟩
    change eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements step.witnesses
      (TypedSource.applySubstitution step.substitution _)) =
      eraseRequirements (named.state.source.applySubstitution (step.substitution.compose _))
    rw [rewrite_erased, erase_substitute, canonical, ← erase_substitute,
      source step.substitution _ closed]

private theorem named_source_eq {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftId rightId : Core.Word} (left : Named owned leftId) (right : Named owned rightId)
    (same : left.state.owner = right.state.owner) : left.state.source = right.state.source := by
  have found := right.found
  change left.owner = right.owner at same
  rw [← same] at found
  have caller := Except.ok.inj (left.found.symm.trans found)
  exact congrArg (fun selected : SourceSpecialization.SpecializedFunction => selected.function.typedBody) caller

/-- The lookup key forgets arbitrary repetitions of lambda frames, but keeps
every occurrence-specific requirement ID. It is not a key by native type. -/
structure StateKey where
  owner : Key
  active : Substitution
  profile : List (List RequirementId)
  deriving DecidableEq, Repr

def stateKey (state : CallableAncestryMetadata.State) : StateKey :=
  ⟨state.owner, state.active, requirementProfile state.source⟩

/-- Within actually authenticated metadata recipes this finite-profile key
determines the complete source metadata. Frame history itself is intentionally
not reconstructed or authenticated by equality of these keys. -/
theorem stateKey_injective {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame} {left right : CallableAncestryMetadata.State}
    (leftAuthenticated : Authenticates owned leftFrame (some left))
    (rightAuthenticated : Authenticates owned rightFrame (some right))
    (same : stateKey left = stateKey right) : left = right := by
  have owner : left.owner = right.owner := congrArg StateKey.owner same
  have active : left.active = right.active := congrArg StateKey.active same
  have profile : requirementProfile left.source = requirementProfile right.source := congrArg StateKey.profile same
  obtain ⟨_, leftNamed, leftOwner, _, leftCanonical⟩ := Authenticates.canonical leftAuthenticated
  obtain ⟨_, rightNamed, rightOwner, _, rightCanonical⟩ := Authenticates.canonical rightAuthenticated
  have roots := named_source_eq leftNamed rightNamed (leftOwner.symm.trans (owner.trans rightOwner))
  have erased : eraseRequirements left.source = eraseRequirements right.source := by
    rw [leftCanonical, rightCanonical, roots, active]
  have sources := FiniteProfiles.source_unique erased profile
  cases left
  cases right
  cases owner
  cases active
  cases sources
  rfl

end SourceComposition

end Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
end
