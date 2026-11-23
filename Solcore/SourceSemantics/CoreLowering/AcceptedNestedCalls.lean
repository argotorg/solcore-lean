import Solcore.SourceSemantics.CoreLowering.AcceptedConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrayMemrefs

/-!
# Accepted bodies: direct calls and conversions inside expressions

Extends the expression closure of named-row bodies to direct calls at every
expression position: inside operators, conditionals, groups and pairs, and as
the arguments of other direct calls, and to the builtin conversions, the
mapping indices, the builtin closures and their calls, tuples beyond pairs,
constructor applications and the memory array forms there. Closes a family of such rows by one strong induction on the grade.

Main declarations:
- `CellAwareInvocationAcceptedTupleSites.TupleSite`, a tuple of more than two
  elements as a compiler site;
- `CellAwareInvocationAcceptedArraySites.ArraySite`, a memory array form of a
  shape the heads take as a compiler site;
- `CellAwareInvocationAcceptedNestedTrees.Nested`, the sites, and
  `CellAwareInvocationAcceptedNestedTrees.NestedTree`, their receipt trees;
- `CellAwareInvocationAcceptedNestedTrees.of_nested`, the receipt tree from the
  compiler's acceptance;
- `CellAwareInvocationAcceptedNestedBounds.preserves_nested_tree` and
  `CellAwareInvocationAcceptedNestedBounds.reflects_nested_tree`, their meaning;
- `CellAwareInvocationAcceptedNestedExpressions.ClosedNested` and
  `CellAwareInvocationAcceptedNestedExpressions.expressions`, the closure, with
  `CellAwareInvocationAcceptedNestedExpressions.closedNested_of_closedCalls` for
  rows whose calls are at expression roots;
- `CellAwareInvocationAcceptedCallFamily.Row`,
  `CellAwareInvocationAcceptedCallFamily.preserves` and
  `CellAwareInvocationAcceptedCallFamily.reflects`, the family closure;
- `CellAwareInvocationAcceptedNestedCheck.nodes?` and
  `CellAwareInvocationAcceptedNestedCheck.closedNested`, a finite check of the
  nested sites on an actually compiled row.
-/

section
/-! Tuples of more than two elements in named-row bodies as compiler sites. The
first subset's sites stop at pairs, so a longer tuple is a site of its own. It
has no coercions or requirements, is not a generalized initializer and lies in a
row without evidence assumptions, so the named policy's special callback
declines it and its read policy is the compatible reader, as at a call of a
builtin closure. `tupleSite?` recognizes one on an actually compiled row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTupleSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy)

/-- A tuple of more than two elements in a named-row body. -/
structure TupleSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (ids : List ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .tuple ids
  beyond : 2 < ids.length
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}
  {ids : List ExpressionId}

theorem contextual (site : TupleSite prepared named source id ids) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none (site : TupleSite prepared named source id ids)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil site.requirements site.coercions, site.found,
    site.form, site.requirements, site.coercions, site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a tuple. -/
theorem special (site : TupleSite prepared named source id ids) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : TupleSite prepared named source id ids) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

/-- Proof-producing recognition of a tuple of more than two elements of the row. -/
def tupleSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option (Σ' (ids : List ExpressionId), TupleSite prepared named source id ids) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .tuple ids =>
      if beyond : 2 < ids.length then
        match coercions : node.coercions, requirements : node.requirements with
        | [], [] =>
          match initializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
          | some _ => none
          | none =>
            match assumptions : named.specialized.assumptions with
            | [] => some ⟨ids, ⟨node, found, form, beyond, coercions, requirements, initializer, assumptions⟩⟩
            | _ :: _ => none
        | _, _ => none
      else none
    | _ => none

/-- A tuple site depends on its row only through the row's key and its empty
assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : TupleSite prepared first source id ids) : TupleSite prepared second source id ids where
  node := site.node
  found := site.found
  form := site.form
  beyond := site.beyond
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  assumptions := assumptions

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedTupleSites
end

section
/-! Memory array forms in named-row bodies as compiler sites, of the shapes the
heads take: a length, a read, a slice, `new`, a literal and `toArray` of a
slice made on the spot of an array. A site has no coercions or requirements, is
not a generalized initializer and lies in a row without evidence assumptions,
as a tuple's, so the named policy declines it and reads it as the compatible
reader. The arrays that `new` and a literal allocate have their default
elements' layouts registered in the catalog (`defaultLayouts?`), and a literal
has fewer than `2^256` elements. `arraySite?` recognizes one on an actually
compiled row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedArraySites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy)

/-- The array forms the heads take. -/
inductive Shape (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource) : ExpressionForm → Prop where
  | arrayLength (base : ExpressionId) : Shape checked source (.arrayLength base)
  | arrayIndex (base index : ExpressionId) : Shape checked source (.arrayIndex base index)
  | arraySlice (base : ExpressionId) (start stop : Option ExpressionId) :
      Shape checked source (.arraySlice base start stop)
  | newArray {element : TypeSystem.Ty} (length : ExpressionId)
      (layouts : CellAwareArrayCells.DefaultLayouts checked.catalog checked.catalog.definitions
        (TypeSystem.Ty.array element)) :
      Shape checked source (.newArray element length)
  | arrayLiteral {element : TypeSystem.Ty} {elements : List ExpressionId} (short : elements.length < wordModulus)
      (layouts : CellAwareArrayCells.DefaultLayouts checked.catalog checked.catalog.definitions
        (TypeSystem.Ty.array element)) :
      Shape checked source (.arrayLiteral element elements)
  | toArray {element arrayElement : TypeSystem.Ty} {slice base : ExpressionId} {start stop : Option ExpressionId}
      {sliceNode : ExpressionNode} (sliceFound : source.lookupExpression? slice = some sliceNode)
      (sliceForm : sliceNode.form = .arraySlice base start stop)
      (sliceType : sliceNode.type = TypeSystem.Ty.arraySlice (TypeSystem.Ty.array arrayElement)) :
      Shape checked source (.toArray element slice)

/-- A memory array form in a named-row body, of a shape the heads take. -/
structure ArraySite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (form : ExpressionForm) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  formEq : node.form = form
  shape : Shape checked source form
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}
  {form : ExpressionForm}

/-- An array site is not a local read. -/
theorem not_local (site : ArraySite prepared named source id form) (name : String) (binder : Resolved.LocalId) :
    site.node.form ≠ .reference name (.local binder) := by
  rw [site.formEq]
  cases site.shape <;> intro same <;> cases same

theorem contextual (site : ArraySite prepared named source id form) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  have formEq := site.formEq
  cases site.shape <;> simp [SourceCoreGeneralFunctions.contextualSource, site.found, formEq]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none (site : ArraySite prepared named source id form)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have formEq := site.formEq
  cases site.shape <;>
    simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil site.requirements site.coercions, site.found,
      formEq, site.requirements, site.coercions, site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines an array form. -/
theorem special (site : ArraySite prepared named source id form) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  have formEq := site.formEq
  cases site.shape <;> simp [formEq]

theorem read (site : ArraySite prepared named source id form) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

/-- The layouts of an element type's defaults, checked on the catalog: each
nested array's layout, down to a scalar. -/
def defaultLayouts? (checked : SourceCoreCompatibleCatalog.Checked) : TypeSystem.Ty → Bool
  | .application (.constructor (.builtin .memoryArray)) inner =>
      (match checked.catalog.mappingLayout (.constructor (.builtin .word)) inner with
        | .ok _ => true
        | .error _ => false) && defaultLayouts? checked inner
  | _ => true

theorem defaultLayouts?_sound {type : TypeSystem.Ty} (checkedLayouts : defaultLayouts? checked type = true) :
    CellAwareArrayCells.DefaultLayouts checked.catalog checked.catalog.definitions type := by
  induction type using defaultLayouts?.induct with
  | case1 inner ih =>
    simp only [defaultLayouts?, Bool.and_eq_true] at checkedLayouts
    obtain ⟨mapped, rest⟩ := checkedLayouts
    cases layoutEq : checked.catalog.mappingLayout (.constructor (.builtin .word)) inner with
    | error => simp [layoutEq] at mapped
    | ok layout =>
      obtain ⟨identified, keyProjected, valueProjected, registered⟩ :=
        CompatibleEncoding.mappingLayout_facts layoutEq
      refine .array (fun innerType identity projected identity' => ?_) (ih rest)
      have sameValue := Except.ok.inj (projected.symm.trans valueProjected)
      have sameIdentity := Option.some.inj (identity'.symm.trans identified)
      simp only [SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure, Except.ok.injEq] at keyProjected
      cases layout
      simp only at sameValue sameIdentity keyProjected
      subst sameValue sameIdentity keyProjected
      exact registered
  | case2 type notArray =>
    exact .scalar fun inner same => notArray inner same

/-- Proof-producing recognition of a memory array form of the row, of a shape
the heads take. -/
def arraySite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) :
    Option (Σ' (form : ExpressionForm), ArraySite prepared named source id form) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match coercions : node.coercions, requirements : node.requirements with
    | [], [] =>
      match initializer : prepared.base.locals.bindings.find? (fun binding =>
          decide (binding.caller = named.signature.key ∧ binding.initializer = id)) with
      | some _ => none
      | none =>
        match assumptions : named.specialized.assumptions with
        | _ :: _ => none
        | [] =>
          match form : node.form with
          | .arrayLength base =>
            some ⟨_, ⟨node, found, form, .arrayLength base, coercions, requirements, initializer, assumptions⟩⟩
          | .arrayIndex base index =>
            some ⟨_, ⟨node, found, form, .arrayIndex base index, coercions, requirements, initializer,
              assumptions⟩⟩
          | .arraySlice base start stop =>
            some ⟨_, ⟨node, found, form, .arraySlice base start stop, coercions, requirements, initializer,
              assumptions⟩⟩
          | .newArray element length =>
            if layouts : defaultLayouts? checked (TypeSystem.Ty.array element) = true then
              some ⟨_, ⟨node, found, form, .newArray length (defaultLayouts?_sound layouts), coercions,
                requirements, initializer, assumptions⟩⟩
            else none
          | .arrayLiteral element elements =>
            if short : elements.length < wordModulus then
              if layouts : defaultLayouts? checked (TypeSystem.Ty.array element) = true then
                some ⟨_, ⟨node, found, form, .arrayLiteral short (defaultLayouts?_sound layouts), coercions,
                  requirements, initializer, assumptions⟩⟩
              else none
            else none
          | .toArray _element slice =>
            match sliceFound : source.lookupExpression? slice with
            | none => none
            | some sliceNode =>
              match sliceForm : sliceNode.form, sliceType : sliceNode.type with
              | .arraySlice _base _start _stop, .application (.constructor (.builtin .arraySlice))
                  (.application (.constructor (.builtin .memoryArray)) _arrayElement) =>
                some ⟨_, ⟨node, found, form, .toArray sliceFound sliceForm sliceType, coercions, requirements,
                  initializer, assumptions⟩⟩
              | _, _ => none
          | _ => none
    | _, _ => none

/-- An array site depends on its row only through the row's key and its empty
assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : ArraySite prepared first source id form) : ArraySite prepared second source id form where
  node := site.node
  found := site.found
  formEq := site.formEq
  shape := site.shape
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  assumptions := assumptions

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedArraySites
end

section
/-! `CanStore.load(lidx(a, i))` and `CanStore.store(lidx(a, i), v)` in named-row bodies as compiler sites:
the memref is made on the spot, and the `CanStore` node and its `lidx` are each a site as an array form is,
so the named policy declines both and reads both as the compatible reader. `memrefSite?` recognizes one on
an actually compiled row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMemrefSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy)

/-- A `CanStore` node whose memref `reference` is `lidx(base, subscript)`, in a named-row body. -/
structure MemrefSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id reference : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  base : ExpressionId
  subscript : ExpressionId
  referenceNode : ExpressionNode
  referenceFound : source.lookupExpression? reference = some referenceNode
  referenceForm : referenceNode.form = .elementRef base subscript
  referenceCoercions : referenceNode.coercions = []
  referenceRequirements : referenceNode.requirements = []
  referenceNotInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = reference)) = none
  assumptions : named.specialized.assumptions = []

/-- The forms of a memref composite's two nodes. -/
inductive Form : ExpressionForm → Prop where
  | load (reference : ExpressionId) : Form (.memrefLoad reference)
  | store (reference value : ExpressionId) : Form (.memrefStore reference value)
  | element (base subscript : ExpressionId) : Form (.elementRef base subscript)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id reference : ExpressionId}

private theorem contextual_of {node : ExpressionNode} {form : ExpressionForm}
    (found : source.lookupExpression? id = some node) (formEq : node.form = form) (shape : Form form) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  cases shape <;> simp [SourceCoreGeneralFunctions.contextualSource, found, formEq]

private theorem ordinary_nil {node : ExpressionNode} (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

private theorem evidence_none_of {node : ExpressionNode} {form : ExpressionForm}
    (found : source.lookupExpression? id = some node) (formEq : node.form = form) (shape : Form form)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (assumptions : named.specialized.assumptions = [])
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  cases shape <;>
    simp [SourceCoreEvidence.lowerWithProjector, ordinary_nil requirements coercions, found, formEq, requirements,
      coercions, assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

private theorem special_of {node : ExpressionNode} {form : ExpressionForm}
    (found : source.lookupExpression? id = some node) (formEq : node.form = form) (shape : Form form)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (notInitializer : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none)
    (assumptions : named.specialized.assumptions = []) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual_of found formEq shape, bind, Except.bind, pure, Except.pure, found,
    notInitializer, Option.filter_none]
  rw [evidence_none_of found formEq shape requirements coercions assumptions child budget scope reasonAt]
  cases shape <;> simp [formEq]

private theorem read_of {node : ExpressionNode} {form : ExpressionForm}
    (found : source.lookupExpression? id = some node) (formEq : node.form = form) (shape : Form form)
    (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual_of found formEq shape, bind, Except.bind]
  rfl

/-- The named policy's special callback declines the `CanStore` node. -/
theorem special (site : MemrefSite prepared named source id reference) {form : ExpressionForm}
    (formEq : site.node.form = form) (shape : Form form) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none :=
  special_of compiled site.found formEq shape site.requirements site.coercions site.notInitializer site.assumptions
    rootFuel child budget scope reasonAt

theorem read (site : MemrefSite prepared named source id reference) {form : ExpressionForm}
    (formEq : site.node.form = form) (shape : Form form) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id :=
  read_of compiled site.found formEq shape rootFuel

/-- The named policy's special callback declines the `lidx` node. -/
theorem reference_special (site : MemrefSite prepared named source id reference) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope reference reasonAt = .ok none :=
  special_of compiled site.referenceFound site.referenceForm (.element _ _) site.referenceRequirements
    site.referenceCoercions site.referenceNotInitializer site.assumptions rootFuel child budget scope reasonAt

theorem reference_read (site : MemrefSite prepared named source id reference) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source reference =
      SourceCoreCompatibleDataExpressions.readExpression checked source reference :=
  read_of compiled site.referenceFound site.referenceForm (.element _ _) rootFuel

/-- Proof-producing recognition of a memref composite at `id` whose memref is `reference`. -/
def memrefSite? (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id reference : ExpressionId) : Option (MemrefSite prepared named source id reference) :=
  match found : source.lookupExpression? id, referenceFound : source.lookupExpression? reference with
  | some node, some referenceNode =>
    match coercions : node.coercions, requirements : node.requirements,
        referenceCoercions : referenceNode.coercions, referenceRequirements : referenceNode.requirements with
    | [], [], [], [] =>
      match referenceForm : referenceNode.form with
      | .elementRef base subscript =>
        match initializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = id)),
            referenceInitializer : prepared.base.locals.bindings.find? (fun binding =>
              decide (binding.caller = named.signature.key ∧ binding.initializer = reference)),
            assumptions : named.specialized.assumptions with
        | none, none, [] =>
          some ⟨node, found, coercions, requirements, initializer, base, subscript, referenceNode, referenceFound,
            referenceForm, referenceCoercions, referenceRequirements, referenceInitializer, assumptions⟩
        | _, _, _ => none
      | _ => none
    | _, _, _, _ => none
  | _, _ => none

/-- A memref site depends on its row only through the row's key and its empty assumptions. -/
def transport {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    (site : MemrefSite prepared first source id reference) : MemrefSite prepared second source id reference where
  node := site.node
  found := site.found
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  base := site.base
  subscript := site.subscript
  referenceNode := site.referenceNode
  referenceFound := site.referenceFound
  referenceForm := site.referenceForm
  referenceCoercions := site.referenceCoercions
  referenceRequirements := site.referenceRequirements
  referenceNotInitializer := keyEq ▸ site.referenceNotInitializer
  assumptions := assumptions

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedMemrefSites
end

section
/-! Direct calls and conversions inside the expressions of named-row bodies.
`Nested` closes the first subset's forms, direct calls, builtin conversions,
calls of builtin closures, tuples and the memory array forms under one another:
every operand, branch, pair and tuple element, every argument of a direct call
or of a closure, the argument of a conversion and every child of an array form
is again a `Nested` site.
`NestedTree` keeps the first subset's receipts at its forms, the direct-call
receipts of `CellAwareInvocationAcceptedCallTrees.CallTree` at its calls, and
the node's metadata at `word` at its conversions. A call's argument receipts
and a tuple's element receipts are indexed by the pairs of the arguments or
elements and their lowered codes: a receipt tree cannot be the certificate of
the head's argument sequence (`DataExpressionSequence.Tree`) inside its own
definition, so the bounds rebuild that sequence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedTrees
open Core Frontend SourceInference DataPatternValues
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedCallTrees (CallSubset)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CellAwareInvocationAcceptedConversionSites (ConversionSite)
open CellAwareInvocationAcceptedBuiltinSites (BuiltinSite)
open CellAwareInvocationAcceptedTupleSites (TupleSite)
open CellAwareInvocationAcceptedConstructorSites (ConstructorSite)
open CellAwareInvocationAcceptedArraySites (ArraySite)
open CellAwareInvocationAcceptedMemrefSites (MemrefSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Monomorphic)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)

/-- Sites of the nested closure: the first subset's forms with nested
children, direct calls with nested arguments whose instantiation the caller's
family admits, builtin conversions with a nested argument, mapping indices
with a nested base and key, references to builtin closures, calls of
builtin closures with nested arguments, tuples of more than two nested
elements, constructor applications with nested arguments, and array forms of
the heads' shapes with nested children, in the order the Source evaluates
them. -/
inductive Nested {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (called : DeclarationInstantiation → Prop) : ExpressionId → Prop where
  | literal {id} (site : Site prepared named source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Nested prepared named source called id
  | read {id name binder} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.local binder)) : Nested prepared named source called id
  | unary {id operator operand} (site : Site prepared named source id)
      (form : site.node.form = .unary operator operand)
      (child : Nested prepared named source called operand) : Nested prepared named source called id
  | binary {id operator left right} (site : Site prepared named source id)
      (form : site.node.form = .binary left operator right)
      (first : Nested prepared named source called left) (second : Nested prepared named source called right) :
      Nested prepared named source called id
  | conditional {id condition thenId elseId} (site : Site prepared named source id)
      (form : site.node.form = .conditional condition thenId elseId)
      (test : Nested prepared named source called condition) (yes : Nested prepared named source called thenId)
      (no : Nested prepared named source called elseId) : Nested prepared named source called id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Nested prepared named source called inner) : Nested prepared named source called id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Nested prepared named source called left) (second : Nested prepared named source called right) :
      Nested prepared named source called id
  | call {id callee ids instantiation} (site : DirectSite prepared named source id callee ids instantiation)
      (selected : called instantiation)
      (arguments : ∀ argument ∈ ids, Nested prepared named source called argument) :
      Nested prepared named source called id
  | conversion {id callee argument function target}
      (site : ConversionSite prepared named source id callee argument function target)
      (child : Nested prepared named source called argument) : Nested prepared named source called id
  | index {id base key} (site : Site prepared named source id) (form : site.node.form = .index base key)
      (first : Nested prepared named source called base) (second : Nested prepared named source called key) :
      Nested prepared named source called id
  | builtinValue {id name function} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.builtinFunction function)) : Nested prepared named source called id
  | builtin {id callee ids function} (site : BuiltinSite prepared named source id callee ids function)
      (arguments : ∀ argument ∈ ids, Nested prepared named source called argument) :
      Nested prepared named source called id
  | tuple {id ids} (site : TupleSite prepared named source id ids)
      (elements : ∀ element ∈ ids, Nested prepared named source called element) :
      Nested prepared named source called id
  | constructor {id instantiation ids} (site : ConstructorSite prepared named source id instantiation ids)
      (arguments : ∀ argument ∈ ids, Nested prepared named source called argument) :
      Nested prepared named source called id
  | array {id form} (site : ArraySite prepared named source id form)
      (children : ∀ child ∈ (Staging.Recursive.arrayChildren form).getD [],
        Nested prepared named source called child) :
      Nested prepared named source called id
  | memrefLoad {id reference} (site : MemrefSite prepared named source id reference)
      (form : site.node.form = .memrefLoad reference)
      (first : Nested prepared named source called site.base)
      (second : Nested prepared named source called site.subscript) : Nested prepared named source called id
  | memrefStore {id reference value} (site : MemrefSite prepared named source id reference)
      (form : site.node.form = .memrefStore reference value)
      (first : Nested prepared named source called site.base)
      (second : Nested prepared named source called site.subscript)
      (third : Nested prepared named source called value) : Nested prepared named source called id

/-- Static receipts at nested sites. The forms of the first subset keep the
receipts of `CellAwareInvocationAcceptedExpressionTrees.Tree` with nested
children; a call keeps the compiler's direct-call receipt, the authority of the
selected header and the receipt of every argument at its lowered code; a
conversion keeps its node's metadata at `word` and its argument's receipt; an
index keeps the compiler's index header, its key's node, the base's mapping
type and the receipts of its base and key; a reference to a builtin closure
keeps the closure's value certificate and the node's metadata; and a call of a
builtin closure keeps the compiler's builtin-call receipt, the native types of
its arguments and the receipt of every argument at its lowered code; a tuple
of more than two elements keeps its node's metadata at the type of its packed
codes and the receipt of every element at its lowered code; and a constructor
application keeps the compiler's constructor header, its closed substitution and
the receipt of every argument at its lowered code. -/
inductive NestedTree (whole : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)))
    (called : DeclarationInstantiation → Prop) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (solved : List SolvedRequirement) (source : TypedSource)
    (sourceContext : SourceSemantics.Context) (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | plain {id lowered}
      (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel
        (.initial whole.compatible.checked) source sourceContext solved reasonAt scope id lowered) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope inner
        lowered) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node
        (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope left
        first)
      (rightChild : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        right second) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core)
      (child : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope operand
        ⟨core.operandType, childCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨core.resultType, core.lower childCode⟩
  | binary {id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node
        (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = amountType)
      (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType amountType resultType mode)
      (first : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope left
        ⟨mode.operandType operator, leftCode⟩)
      (second : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope right
        ⟨mode.operandType operator, rightCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        condition ⟨.bool, conditionCode⟩)
      (thenTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope thenId
        ⟨type, thenCode⟩)
      (elseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope elseId
        ⟨type, elseCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩
  | call {policy body fuel id callee ids instantiation lowered}
      (receipt : Receipt policy body fuel compilation (.initial whole.compatible.checked) source scope id callee ids
        instantiation reasonAt lowered)
      (port : Port receipt headers)
      (requirements : receipt.node.requirements = [])
      (monomorphic : Monomorphic instantiation)
      (selected : called instantiation)
      (lengths : ids.length = receipt.codes.length)
      (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node)
      (arguments : ∀ argument ∈ ids.zip receipt.codes,
        NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope argument.1
          argument.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | conversion {id node callee argument function target argumentCode}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node .word)
      (form : node.form = .call callee [argument] (.builtinFunction function))
      (conversion : function.conversion? = some target)
      (argumentFound : ∃ argumentNode, source.lookupExpression? argument = some argumentNode)
      (child : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        argument ⟨.word, argumentCode⟩) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨.word, SourceCoreInteger.builtinConversion target argumentCode⟩
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header (.initial whole.compatible.checked) source id base node baseNode
        layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode) (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base
        first)
      (keyTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope key
        second) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression
          second.expression (reasonAt id)⟩
  | builtinValue {id lowered}
      (header : CellAwareBuiltinValueCertificates.Header whole.indexed source id lowered)
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id header.node lowered.type) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | builtin {policy body fuel id callee ids function lowered}
      (receipt : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body fuel compilation
        (.initial whole.compatible.checked) source scope id callee ids function reasonAt lowered)
      (nativeTypes : receipt.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
      (lengths : ids.length = receipt.codes.length)
      (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node)
      (arguments : ∀ argument ∈ ids.zip receipt.codes,
        NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope argument.1
          argument.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | tuple {id node ids codes}
      (metadata : CompatibleExpressionPrimitives.Metadata whole.compatible.checked source id node
        (SourceCoreCalls.packArguments codes).type)
      (form : node.form = .tuple ids) (beyond : 2 < ids.length) (lengths : ids.length = codes.length)
      (found : ∀ element ∈ ids, ∃ node, source.lookupExpression? element = some node)
      (elements : ∀ element ∈ ids.zip codes,
        NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope element.1
          element.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        (SourceCoreCalls.packArguments codes)
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header (.initial whole.compatible.checked) source id node
        instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
      (lengths : ids.length = codes.length)
      (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node)
      (arguments : ∀ argument ∈ ids.zip codes,
        NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope argument.1
          argument.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨.namedData tag.owner,
          SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩
  | arrayLength {id node base baseNode first lowered}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node .word)
      (form : node.form = .arrayLength base) (baseFound : source.lookupExpression? base = some baseNode)
      (code : (∃ rest, first.type = .cell (.product .word rest) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.arrayLength first.expression⟩) ∨
        (∃ view, first.type = .product view (.product .word .word) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.sliceLength first.expression⟩))
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered
  | arrayIndex {id node base subscript baseNode subscriptNode depth fuel layout comparison first second}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node layout.valueType)
      (form : node.form = .arrayIndex base subscript) (baseFound : source.lookupExpression? base = some baseNode)
      (subscriptFound : source.lookupExpression? subscript = some subscriptNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
      (prepared : SourceCoreCompatibleDataEquality.prepare fuel whole.compatible.checked
        (.constructor (.builtin .word)) = .ok comparison)
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) (subscriptTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope subscript second) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨layout.valueType,
        SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression second.expression⟩
  | sliceRange {id node base start stop baseNode startNode stopNode depth layout first startCode stopCode}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (.product first.type (.product .word .word)))
      (form : node.form = .arraySlice base (some start) (some stop))
      (baseFound : source.lookupExpression? base = some baseNode)
      (startFound : source.lookupExpression? start = some startNode)
      (stopFound : source.lookupExpression? stop = some stopNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) (startTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope start startCode) (stopTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope stop stopCode) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression (some startCode.expression)
          (some stopCode.expression)⟩
  | sliceFrom {id node base bound baseNode boundNode depth layout first boundCode}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (.product first.type (.product .word .word)))
      (form : node.form = .arraySlice base (some bound) none)
      (baseFound : source.lookupExpression? base = some baseNode)
      (boundFound : source.lookupExpression? bound = some boundNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) (boundTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope bound boundCode) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression (some boundCode.expression) none⟩
  | sliceTo {id node base bound baseNode boundNode depth layout first boundCode}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (.product first.type (.product .word .word)))
      (form : node.form = .arraySlice base none (some bound))
      (baseFound : source.lookupExpression? base = some baseNode)
      (boundFound : source.lookupExpression? bound = some boundNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) (boundTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope bound boundCode) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression none (some boundCode.expression)⟩
  | sliceWhole {id node base baseNode depth layout first}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (.product first.type (.product .word .word)))
      (form : node.form = .arraySlice base none none)
      (baseFound : source.lookupExpression? base = some baseNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base first) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression none none⟩
  | newArray {id node element length lengthNode payload identity default first}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (CompatibleExpressionArrays.arrayType payload identity))
      (form : node.form = .newArray element length)
      (lengthFound : source.lookupExpression? length = some lengthNode)
      (projected : whole.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
        .ok (CompatibleExpressionArrays.arrayType payload identity))
      (defined : SourceCoreCompatibleDataExpressions.arrayDefault whole.compatible.checked.catalog element =
        some default)
      (layouts : CellAwareArrayCells.DefaultLayouts whole.compatible.checked.catalog
        (CallableIndexedAmbient.ambientDefinitions whole.indexed).definitions (TypeSystem.Ty.array element))
      (lengthTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope length first) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨CompatibleExpressionArrays.arrayType payload identity,
        SourceCoreDataExpressions.newArray (CompatibleExpressionArrays.arrayLayout payload identity) default
          first.expression⟩
  | arrayLiteral {id node element elements payload identity default codes}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (CompatibleExpressionArrays.arrayType payload identity))
      (form : node.form = .arrayLiteral element elements) (lengths : elements.length = codes.length)
      (found : ∀ element ∈ elements, ∃ node, source.lookupExpression? element = some node)
      (codeTypes : ∀ code ∈ codes, code.type = payload) (short : elements.length < Core.wordModulus)
      (projected : whole.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
        .ok (CompatibleExpressionArrays.arrayType payload identity))
      (defined : SourceCoreCompatibleDataExpressions.arrayDefault whole.compatible.checked.catalog element =
        some default)
      (layouts : CellAwareArrayCells.DefaultLayouts whole.compatible.checked.catalog
        (CallableIndexedAmbient.ambientDefinitions whole.indexed).definitions (TypeSystem.Ty.array element))
      (elementTrees : ∀ pair ∈ elements.zip codes, NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope pair.1 pair.2) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨CompatibleExpressionArrays.arrayType payload identity,
        SourceCoreDataExpressions.arrayLiteral (CompatibleExpressionArrays.arrayLayout payload identity) default
          (SourceCoreCalls.packArguments codes).expression codes.length⟩
  | copy {id node element slice sliceNode sliceBase sliceStart sliceStop valueType dataType comparison fuel first}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node
        (.cell (.product .word (.product valueType (.namedData dataType)))))
      (form : node.form = .toArray element slice) (sliceFound : source.lookupExpression? slice = some sliceNode)
      (sliceForm : sliceNode.form = .arraySlice sliceBase sliceStart sliceStop)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0 + 1, ⟨.word, valueType, dataType⟩))
      (prepared : SourceCoreCompatibleDataEquality.prepare fuel whole.compatible.checked
        (.constructor (.builtin .word)) = .ok comparison)
      (sliceTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope slice first) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id ⟨.cell (.product .word (.product valueType (.namedData dataType))),
        SourceCoreDataExpressions.sliceCopy ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1) first.type
          first.expression⟩
  | memrefLoad {id node reference referenceNode base subscript baseNode subscriptNode layout comparison fuel first
      second}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node layout.valueType)
      (form : node.form = .memrefLoad reference)
      (referenceMetadata : CompatibleExpressionReads.Metadata whole.compatible.checked source reference referenceNode
        (.product first.type .word))
      (referenceForm : referenceNode.form = .elementRef base subscript)
      (baseFound : source.lookupExpression? base = some baseNode)
      (subscriptFound : source.lookupExpression? subscript = some subscriptNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
      (prepared : SourceCoreCompatibleDataEquality.prepare fuel whole.compatible.checked
        (.constructor (.builtin .word)) = .ok comparison)
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base
        first)
      (subscriptTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        subscript second) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨layout.valueType, SourceCoreDataExpressions.memrefLoad layout comparison.expression
          (SourceCoreDataExpressions.elementRef layout first.expression second.expression)⟩
  | memrefStore {id node reference value referenceNode base subscript baseNode subscriptNode valueNode layout
      comparison fuel first second third}
      (metadata : CompatibleExpressionReads.Metadata whole.compatible.checked source id node .unit)
      (form : node.form = .memrefStore reference value)
      (referenceMetadata : CompatibleExpressionReads.Metadata whole.compatible.checked source reference referenceNode
        (.product first.type .word))
      (referenceForm : referenceNode.form = .elementRef base subscript)
      (baseFound : source.lookupExpression? base = some baseNode)
      (subscriptFound : source.lookupExpression? subscript = some subscriptNode)
      (valueFound : source.lookupExpression? value = some valueNode)
      (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
      (valueType : third.type = layout.valueType)
      (prepared : SourceCoreCompatibleDataEquality.prepare fuel whole.compatible.checked
        (.constructor (.builtin .word)) = .ok comparison)
      (baseTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope base
        first)
      (subscriptTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        subscript second)
      (valueTree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope
        value third) :
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id
        ⟨.unit, SourceCoreDataExpressions.memrefStore layout comparison.expression
          (SourceCoreDataExpressions.elementRef layout first.expression second.expression) third.expression⟩

section Embedding
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {called : DeclarationInstantiation → Prop}

/-- Every first-subset site is a nested site. -/
theorem of_subset {id : ExpressionId} (subset : Subset prepared named source id) :
    Nested prepared named source called id := by
  induction subset with
  | literal site atomic => exact .literal site atomic
  | read site form => exact .read site form
  | unary site form _ child => exact .unary site form child
  | binary site form _ _ first second => exact .binary site form first second
  | conditional site form _ _ _ test yes no => exact .conditional site form test yes no
  | group site form _ child => exact .group site form child
  | pair site form _ _ first second => exact .pair site form first second

/-- Every extended root is a nested site. -/
theorem of_call_subset {id : ExpressionId} (subset : CallSubset prepared named source called id) :
    Nested prepared named source called id := by
  cases subset with
  | subset subset => exact of_subset subset
  | call site selected arguments =>
    exact .call site selected (fun argument member => of_subset (arguments argument member))

/-- A nested site is an expression node of its Source. -/
theorem nested_found {id : ExpressionId} (nested : Nested prepared named source called id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases nested with
  | literal site _ | read site _ | unary site _ _ | binary site _ _ _ | conditional site _ _ _ _
  | group site _ _ | pair site _ _ _ => exact ⟨_, site.found⟩
  | call site _ _ => exact ⟨_, site.found⟩
  | conversion site _ => exact ⟨_, site.found⟩
  | index site _ _ _ => exact ⟨_, site.found⟩
  | builtinValue site _ => exact ⟨_, site.found⟩
  | builtin site _ => exact ⟨_, site.found⟩
  | tuple site _ => exact ⟨_, site.found⟩
  | constructor site _ => exact ⟨_, site.found⟩
  | array site _ => exact ⟨_, site.found⟩
  | memrefLoad site _ _ _ | memrefStore site _ _ _ _ => exact ⟨_, site.found⟩

end Embedding

section Projection
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop} {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {solved : List SolvedRequirement} {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- Every receipt fixes its native type as the projection of its Source type. -/
theorem projected
    (tree : NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    whole.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | plain receipt => exact CompatibleExpressionPrimitives.Tree.projected (.product receipt.1) found
  | group metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | pair metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | unary metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | binary metadata _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | call receipt _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    exact receipt.metadata.projected
  | conversion metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | index header _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans header.metadata.found)
    exact header.metadata.projected
  | builtinValue _ metadata =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | builtin receipt _ _ _ _ =>
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    exact receipt.metadata.projected
  | tuple metadata _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | constructor receipt _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans receipt.metadata.found)
    exact receipt.metadata.projected
  | arrayLength metadata _ _ code _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    rcases code with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact metadata.projected
  | arrayIndex metadata _ _ _ _ _ _ _ | sliceRange metadata _ _ _ _ _ _ _ _ | sliceFrom metadata _ _ _ _ _ _
  | sliceTo metadata _ _ _ _ _ _ | sliceWhole metadata _ _ _ _ | newArray metadata _ _ _ _ _ _
  | arrayLiteral metadata _ _ _ _ _ _ _ _ _ | copy metadata _ _ _ _ _ _ | memrefLoad metadata _ _ _ _ _ _ _ _ _
  | memrefStore metadata _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected

/-- The receipts of typed sites have the projections of the sites' types as
their native types. -/
theorem projected_codes {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types) (lengths : ids.length = codes.length)
    (each : ∀ argument ∈ ids.zip codes,
      NestedTree whole headers called compilation readFuel solved source sourceContext reasonAt scope argument.1
        argument.2) :
    types.mapM whole.compatible.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    cases codes with
    | nil => rfl
    | cons _ _ => simp at lengths
  | cons id ids ih =>
    cases typed with
    | cons head tail =>
      cases codes with
      | nil => simp at lengths
      | cons code codes =>
        obtain ⟨node, contains, nodeType⟩ := head.stored_type
        have first := projected (each (id, code) (by simp)) (lookupExpression?_complete unique contains)
        rw [nodeType] at first
        have rest := ih tail (by simpa using lengths)
          (fun argument member => each argument (List.mem_cons_of_mem _ member))
        simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure]

end Projection

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {called : DeclarationInstantiation → Prop}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : Compilation whole.indexed named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem site_special {id : ExpressionId} (site : Site whole.indexed named source id) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareNamedExpressionPolicies.special generation site rootFuel child budget scope reasonAt

private theorem direct_special {id callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} (site : DirectSite whole.indexed named source id callee ids instantiation) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareInvocationAcceptedDirectSites.special generation site rootFuel child budget scope reasonAt

private theorem conversion_special {id callee argument : ExpressionId} {function : BuiltinFunctionId}
    {target : TypeSystem.Ty} (site : ConversionSite whole.indexed named source id callee argument function target) :
    ∀ child budget, (match (namedPolicy generation rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context whole.indexed named) child budget source scope id reasonAt) = .ok none :=
  fun child budget =>
    CellAwareInvocationAcceptedConversionSites.special generation site rootFuel child budget scope reasonAt

private theorem plain {id : ExpressionId} (site : Site whole.indexed named source id)
    (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (empty : site.node.form.references = [])
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id site.node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  have policy : CompatibleExpressionProducts.PolicyOn (namedPolicy generation rootFuel) (context whole.indexed named)
      whole.indexed.fuel (.initial whole.compatible.checked) source scope reasonAt (fun child => child = id) := {
    special := by intro child same _; subst child; exact site_special generation rootFuel site
    read := by intro child same _; subst child; exact CellAwareNamedExpressionPolicies.read generation site rootFuel
    lower := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).lowerRead
    leaf := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer }
  apply NestedTree.plain
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations policy
    ?_ ?_ syntaxTree rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have sameNode := Option.some.inj (site.found.symm.trans found)
    subst node
    rw [empty] at member
    cases member
  · intro child node same _ found
    subst child
    have sameNode := Option.some.inj (site.found.symm.trans found)
    exact sameNode ▸ site.coercions

private theorem argument_rel {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {relation : ExpressionId → SourceCoreBasic.LoweredExpr → Prop} :
    ∀ {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr},
      (∀ argument ∈ ids, ∀ {lowered}, lower argument = .ok lowered → relation argument lowered) →
      ids.mapM lower = .ok codes → ListRel relation ids codes := by
  intro ids
  induction ids with
  | nil =>
    intro codes _ generated
    simp at generated
    subst codes
    exact .nil
  | cons argument rest ih =>
    intro codes each generated
    cases head : lower argument with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at generated
    | ok lowered =>
      cases tail : rest.mapM lower with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at generated
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at generated
        subst codes
        exact .cons (each argument List.mem_cons_self head)
          (ih (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

/-- A constructor's argument receipts, which the compiler indexes by the
arguments and their payload types, relate each argument to its lowered code. -/
private theorem constructor_rel {values : SourceCoreCompatibleValues.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {relation : ExpressionId → SourceCoreBasic.LoweredExpr → Prop} :
    ∀ {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr},
      ids.length = types.length →
      (∀ argument ∈ ids, ∀ {lowered}, child fuel source scope argument reasonAt = .ok lowered →
        relation argument lowered) →
      ListRel (CompatibleExpressionConstructors.Argument values child fuel source scope reasonAt) (ids.zip types)
        codes →
      ListRel relation ids codes := by
  intro ids
  induction ids with
  | nil =>
    intro types codes _ _ related
    cases related
    exact .nil
  | cons argument rest ih =>
    intro types codes count each related
    cases types with
    | nil => cases count
    | cons type types =>
      cases related with
      | cons head tail =>
        exact .cons (each argument List.mem_cons_self head.generated)
          (ih (Nat.succ.inj count) (fun other member => each other (List.mem_cons_of_mem _ member)) tail)

/-- A pointwise relation of two lists relates them pair by pair along their
zip, which has every pair. -/
theorem zip_of_rel {α β : Type} {relation : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel relation xs ys →
      xs.length = ys.length ∧ ∀ pair ∈ xs.zip ys, relation pair.1 pair.2 := by
  intro xs ys related
  induction related with
  | nil => exact ⟨rfl, fun _ member => by cases member⟩
  | cons head _ ih =>
    refine ⟨by simp [ih.1], ?_⟩
    intro pair member
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact head
    · exact ih.2 pair member

/-- The Core type of a slice of a memory array is a view inside one slice. -/
private theorem slice_shape {catalog : SourceCoreCompatibleCatalog.Catalog} {arrayElement : TypeSystem.Ty}
    {type : Ty} {depth : Nat} {layout : OrderedMapping.Layout}
    (projected : catalog.project (TypeSystem.Ty.arraySlice (TypeSystem.Ty.array arrayElement)) = .ok type)
    (shaped : SourceCoreDataExpressions.viewShape? type = some (depth + 1, layout)) :
    depth = 0 ∧ ∃ valueType dataType, layout = ⟨.word, valueType, dataType⟩ := by
  cases elementEq : catalog.project arrayElement with
  | error reason =>
    simp [TypeSystem.Ty.arraySlice, TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project,
      SourceCoreRawMetadata.runtimeType, elementEq, bind, Except.bind] at projected
  | ok elementType =>
    cases identified : catalog.identity? (.mapping (.constructor (.builtin .word)) arrayElement) with
    | none =>
      simp [TypeSystem.Ty.arraySlice, TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project,
        SourceCoreRawMetadata.runtimeType, elementEq, identified, bind, Except.bind, throw, throwThe] at projected
    | some identity =>
      simp only [TypeSystem.Ty.arraySlice, TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project,
        SourceCoreRawMetadata.runtimeType, elementEq, identified, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at projected
      subst type
      have computed : SourceCoreDataExpressions.viewShape?
          (.product (.cell (.product .word (.product elementType (.namedData identity)))) (.product .word .word)) =
          some (0 + 1, ⟨.word, elementType, identity⟩) := rfl
      rw [computed] at shaped
      cases shaped
      exact ⟨rfl, _, _, rfl⟩

/-- A memref's layout is its array's. -/
private theorem memref_layout {type : Ty} {layout layout' : OrderedMapping.Layout}
    (shaped : SourceCoreDataExpressions.viewShape? type = some (0, layout'))
    (memrefShaped : SourceCoreDataExpressions.memrefLayout? (.product type .word) = some layout) :
    layout = layout' := by
  obtain ⟨rfl, keyType⟩ := CellAwareArrayCells.viewShape_zero shaped
  cases layout' with
  | mk keyType' valueType dataType =>
    simp only at keyType
    subst keyType
    simp only [SourceCoreDataExpressions.memrefLayout?, OrderedMapping.Layout.type, Option.some.injEq] at memrefShaped
    exact memrefShaped.symm

private theorem bound_some {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {bound : ExpressionId} {codes : Option SourceCoreBasic.LoweredExpr}
    (mapped : (some bound).mapM lower = .ok codes) : ∃ code, lower bound = .ok code ∧ codes = some code := by
  rw [Option.mapM_some] at mapped
  cases generated : lower bound with
  | error reason => rw [generated] at mapped; cases mapped
  | ok code => rw [generated] at mapped; cases mapped; exact ⟨code, rfl, rfl⟩

private theorem bound_none {lower : ExpressionId → Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr}
    {codes : Option SourceCoreBasic.LoweredExpr}
    (mapped : (none : Option ExpressionId).mapM lower = .ok codes) : codes = none := by
  rw [Option.mapM_none] at mapped
  cases mapped
  rfl

/-- The accepted named compiler yields the nested receipt tree at every nested
site. A call's authority is the input `ports`, as for extended roots. -/
theorem of_nested {id : ExpressionId}
    (nested : Nested whole.indexed named source called id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ports : ∀ {fuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
      {ids : List ExpressionId} {instantiation : DeclarationInstantiation} {callCode : SourceCoreBasic.LoweredExpr}
      (receipt : Receipt (namedPolicy generation rootFuel) (namedLowerBody generation) fuel
        (context whole.indexed named) (.initial whole.compatible.checked) source callScope callId callee ids
        instantiation reasonAt callCode),
      Nonempty (Port receipt headers))
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
      (namedLowerBody generation) fuel (context whole.indexed named) source scope id reasonAt = .ok lowered) :
    NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
      (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope id lowered := by
  induction nested generalizing node fuel lowered with
  | literal site atomic =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain generation rootFuel site (.literal site.found atomic)
      (by generalize form : site.node.form = actual at atomic ⊢; cases atomic <;> rfl) unique declarations typed
      accepted
  | read site form =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain generation rootFuel site (.read site.found form)
      (by simp [form, ExpressionForm.references]) unique declarations typed accepted
  | unary site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | @unary operator operand childCode otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique site.found form metadata.coercions
            metadata.requirements typed
        have childTree := ih childFound childTyped generated
        have lookupEq : _ = some childNode.type := congrArg (Option.map (·.type)) childFound
        have chosen := CompatibleExpressionConditionals.unary_selected profile (projected childTree childFound)
          lookupEq
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, native⟩ := childCode
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .unary metadata form childFound rfl rfl profile childTree
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | binary site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked
          rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique site.found form metadata.coercions
            metadata.requirements typed
        have firstTree := firstIH leftFound leftTyped firstGenerated
        have secondTree := secondIH rightFound rightTyped secondGenerated
        have lookupEq : _ = some leftNode.type := congrArg (Option.map (·.type)) leftFound
        have chosen := CompatibleExpressionConditionals.binary_selected profile (projected firstTree leftFound)
          lookupEq
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .binary metadata form leftFound rightFound rfl rfl rfl profile firstTree secondTree
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | conditional site form test yes no testIH thenIH elseIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | conditional otherForm metadata testGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨testNode, thenNode, elseNode, testFound, thenFound, elseFound,
            testType, thenType, elseType, testTyped, thenTyped, elseTyped⟩ :=
          CompatibleExpressionConditionals.conditional_source_types unique site.found form site.coercions typed
        exact .conditional metadata form testFound thenFound elseFound testType thenType elseType
          (testIH testFound testTyped testGenerated) (thenIH thenFound thenTyped thenGenerated)
          (elseIH elseFound elseTyped elseGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ =>
        simp [form] at otherForm
  | group site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | group otherForm metadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique site.found form site.coercions typed
        exact .group metadata form innerFound sourceType (ih innerFound childTyped generated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | pair site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (context := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
        accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        obtain ⟨rfl, rfl⟩ := by simpa using ExpressionForm.tuple.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique site.found form site.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (firstIH leftFound leftTyped firstGenerated) (secondIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | @call id callee ids instantiation site selected arguments ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation) (fuel := fuel)
        (compilation := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found site.form
        ((site.monomorphic.ordinary _).supported) (direct_special generation rootFuel site)
        (CellAwareInvocationAcceptedDirectSites.read generation site rootFuel) accepted
      obtain ⟨port⟩ := ports receipt
      have nodeEq : receipt.node = site.node := Option.some.inj (receipt.metadata.found.symm.trans site.found)
      obtain ⟨_types, _calleeValid, _application, typing⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique site.found site.form
          site.coercions typed
      have relation := argument_rel
        (relation := fun argument lowered => NestedTree whole headers called (context whole.indexed named)
          whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
          argument lowered)
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := nested_found (arguments argument member)
          exact ih argument member argumentFound
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
              argumentFound) generated)
        receipt.generated
      obtain ⟨lengths, each⟩ := zip_of_rel relation
      exact .call receipt port (nodeEq ▸ site.requirements) site.monomorphic selected lengths
        (fun argument member => nested_found (arguments argument member)) each
  | @conversion id callee argument function target site child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨argumentCode, metadata, generated, rfl⟩ :=
        CellAwareInvocationAcceptedConversionSites.of_accepted (policy := namedPolicy generation rootFuel)
          (body := namedLowerBody generation) (compilation := context whole.indexed named)
          (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
          site.found site.form site.conversion (conversion_special generation rootFuel site)
          (CellAwareInvocationAcceptedConversionSites.read generation site rootFuel) accepted
      obtain ⟨argumentNode, argumentFound⟩ := nested_found child
      obtain ⟨argumentsTyped, _resultType⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types unique site.found site.form
          site.coercions typed
      exact .conversion metadata site.form site.conversion ⟨_, argumentFound⟩
        (ih argumentFound (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique
          argumentsTyped (List.mem_singleton_self _) argumentFound) generated)
  | index site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨keyType, baseTyped, keyTyped⟩ :=
        CompatibleExpressionIndices.index_source_types unique site.found form site.coercions typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨keyNode, keyContains, keyNodeType⟩ := keyTyped.stored_type
      have baseFound := lookupExpression?_complete unique baseContains
      have keyFound := lookupExpression?_complete unique keyContains
      rw [← baseType] at baseTyped
      rw [← keyNodeType] at keyTyped
      obtain ⟨layout, comparison, firstCode, secondCode, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions (policy := namedPolicy generation rootFuel)
          (body := namedLowerBody generation) (context := context whole.indexed named)
          (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
          site.found baseFound form (site_special generation rootFuel site) (CellAwareNamedExpressionPolicies.read generation site rootFuel)
          (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer accepted
      exact .index header keyFound form (by rw [baseType, keyNodeType])
        (firstIH baseFound baseTyped firstGenerated) (secondIH keyFound keyTyped secondGenerated)
  | builtinValue site form =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    obtain ⟨⟨header⟩, metadata⟩ :=
      CellAwareInvocationAcceptedBuiltinSites.value_of_accepted generation site rootFuel form accepted
    have nodeEq : header.node = site.node := Option.some.inj (header.found.symm.trans site.found)
    exact .builtinValue header (nodeEq ▸ metadata)
  | @builtin id callee ids function site arguments ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := CellAwareInvocationAcceptedBuiltinSites.of_accepted generation site rootFuel accepted
      obtain ⟨typing, _resultType⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types unique site.found site.form
          site.coercions typed
      have relation := argument_rel
        (relation := fun argument lowered => NestedTree whole headers called (context whole.indexed named)
          whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
          argument lowered)
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := nested_found (arguments argument member)
          exact ih argument member argumentFound
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
              argumentFound) generated)
        receipt.generated
      obtain ⟨lengths, each⟩ := zip_of_rel relation
      have projectedTypes := projected_codes unique typing lengths each
      rw [CompatibleBuiltinMeaning.argumentTypes_project function site.closure] at projectedTypes
      exact .builtin receipt (Except.ok.inj projectedTypes).symm lengths
        (fun argument member => nested_found (arguments argument member)) each
  | @tuple id ids site elements ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨codes, generated, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
        (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
        (compilation := context whole.indexed named) (values := .initial whole.compatible.checked)
        (scope := scope) (reasonAt := reasonAt) site.found site.form
        (fun child budget => CellAwareInvocationAcceptedTupleSites.special generation site rootFuel child budget
          scope reasonAt)
        (CellAwareInvocationAcceptedTupleSites.read generation site rootFuel)
        (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer accepted
      obtain ⟨_types, typing, _sourceType⟩ :=
        CompatibleExpressionTuples.source_types unique site.found site.form site.coercions typed
      have relation := argument_rel
        (relation := fun element lowered => NestedTree whole headers called (context whole.indexed named)
          whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
          element lowered)
        (fun element member {lowered} generated => by
          obtain ⟨elementNode, elementFound⟩ := nested_found (elements element member)
          exact ih element member elementFound
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
              elementFound) generated)
        generated
      obtain ⟨lengths, each⟩ := zip_of_rel relation
      exact .tuple metadata site.form site.beyond lengths (fun element member => nested_found (elements element member))
        each
  | @constructor id instantiation ids site arguments ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨tag, header, codes, rfl, receipt, count, generated⟩ :=
        CompatibleExpressionConstructors.constructor_of_functions
          (policy := namedPolicy generation rootFuel) (body := namedLowerBody generation)
          (context := context whole.indexed named) (values := .initial whole.compatible.checked)
          (scope := scope) (reasonAt := reasonAt) site.found site.form
          (fun child budget => CellAwareInvocationAcceptedConstructorSites.special generation site rootFuel child
            budget scope reasonAt)
          (CellAwareInvocationAcceptedConstructorSites.read generation site rootFuel)
          (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer accepted
      obtain ⟨_admissible, typing, _sourceType⟩ :=
        CompatibleExpressionConstructors.constructor_source_types unique site.found site.form site.coercions typed
      have relation := constructor_rel
        (relation := fun argument lowered => NestedTree whole headers called (context whole.indexed named)
          whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
          argument lowered)
        count
        (fun argument member {lowered} generated => by
          obtain ⟨argumentNode, argumentFound⟩ := nested_found (arguments argument member)
          exact ih argument member argumentFound
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
              argumentFound) generated)
        generated
      obtain ⟨lengths, each⟩ := zip_of_rel relation
      exact .constructor receipt site.form site.ranges lengths
        (fun argument member => nested_found (arguments argument member)) each
  | @array id form site children ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have special := fun child budget =>
        CellAwareInvocationAcceptedArraySites.special generation site rootFuel child budget scope reasonAt
      have read := CellAwareInvocationAcceptedArraySites.read generation site rootFuel
      have leaf := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer
      have formEq := site.formEq
      have lift : ∀ {child : ExpressionId} {childType : TypeSystem.Ty} {code : SourceCoreBasic.LoweredExpr},
          child ∈ (Staging.Recursive.arrayChildren form).getD [] →
          ExpressionHasType source sourceContext child childType →
          SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel) (namedLowerBody generation)
            fuel (context whole.indexed named) source scope child reasonAt = .ok code →
          ∃ childNode, source.lookupExpression? child = some childNode ∧
            NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
              (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope child code := by
        intro child childType code member childTyped generated
        obtain ⟨childNode, contains, nodeType⟩ := childTyped.stored_type
        have childFound := lookupExpression?_complete unique contains
        rw [← nodeType] at childTyped
        exact ⟨childNode, childFound, ih child member childFound childTyped generated⟩
      cases site.shape with
      | arrayLength base =>
        obtain ⟨first, metadata, firstGenerated, code⟩ :=
          CompatibleExpressionArrays.arrayLength_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, _, _, baseTyped, _⟩ :=
          CellAwareInvocationArrayBounds.length_source_types unique site.found formEq site.coercions typed
        obtain ⟨_, baseFound, baseTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) baseTyped firstGenerated
        exact .arrayLength metadata formEq baseFound code baseTree
      | arrayIndex base subscript =>
        obtain ⟨depth, layout, comparison, first, second, rfl, metadata, firstGenerated, shaped, secondGenerated,
            _, prepared⟩ :=
          CompatibleExpressionArrays.arrayIndex_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, _, baseTyped, _, subscriptTyped, _⟩ :=
          CellAwareInvocationArrayBounds.index_source_types unique site.found formEq site.coercions typed
        obtain ⟨_, baseFound, baseTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) baseTyped firstGenerated
        obtain ⟨_, subscriptFound, subscriptTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) subscriptTyped secondGenerated
        exact .arrayIndex metadata formEq baseFound subscriptFound shaped prepared baseTree subscriptTree
      | arraySlice base start stop =>
        obtain ⟨depth, layout, first, starts, stops, rfl, metadata, firstGenerated, shaped, startsGenerated,
            stopsGenerated, _⟩ :=
          CompatibleExpressionArrays.arraySlice_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, _, _, baseTyped, boundsTyped⟩ :=
          CellAwareInvocationArrayBounds.slice_source_types unique site.found formEq site.coercions typed
        obtain ⟨_, baseFound, baseTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) baseTyped firstGenerated
        have bound : ∀ {bound : ExpressionId} {code : SourceCoreBasic.LoweredExpr},
            bound ∈ start.toList ++ stop.toList →
            SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy generation rootFuel)
              (namedLowerBody generation) fuel (context whole.indexed named) source scope bound reasonAt = .ok code →
            ∃ boundNode, source.lookupExpression? bound = some boundNode ∧
              NestedTree whole headers called (context whole.indexed named) whole.indexed.fuel
                (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope bound code := by
          intro bound code member generated
          obtain ⟨_, boundFound⟩ := nested_found (children bound (List.mem_cons_of_mem _ member))
          exact lift (List.mem_cons_of_mem _ member)
            (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique boundsTyped member
              boundFound) generated
        cases start with
        | none =>
          cases bound_none startsGenerated
          cases stop with
          | none =>
            cases bound_none stopsGenerated
            exact .sliceWhole metadata formEq baseFound shaped baseTree
          | some stop =>
            obtain ⟨stopCode, stopGenerated, rfl⟩ := bound_some stopsGenerated
            obtain ⟨_, stopFound, stopTree⟩ := bound (by simp) stopGenerated
            exact .sliceTo metadata formEq baseFound stopFound shaped baseTree stopTree
        | some start =>
          obtain ⟨startCode, startGenerated, rfl⟩ := bound_some startsGenerated
          obtain ⟨_, startFound, startTree⟩ := bound (by simp) startGenerated
          cases stop with
          | none =>
            cases bound_none stopsGenerated
            exact .sliceFrom metadata formEq baseFound startFound shaped baseTree startTree
          | some stop =>
            obtain ⟨stopCode, stopGenerated, rfl⟩ := bound_some stopsGenerated
            obtain ⟨_, stopFound, stopTree⟩ := bound (by simp) stopGenerated
            exact .sliceRange metadata formEq baseFound startFound stopFound shaped baseTree startTree stopTree
      | @newArray element length layouts =>
        obtain ⟨payload, identity, default, first, rfl, metadata, projectedArray, defined, firstGenerated, _⟩ :=
          CompatibleExpressionArrays.newArray_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, _, lengthTyped⟩ :=
          CellAwareInvocationArrayBounds.new_source_types unique site.found formEq site.coercions typed
        obtain ⟨_, lengthFound, lengthTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) lengthTyped firstGenerated
        exact .newArray metadata formEq lengthFound projectedArray defined
          (layouts.extend (CallableIndexedAmbient.ambientDefinitions whole.indexed).basePrefix) lengthTree
      | @arrayLiteral element elements short layouts =>
        obtain ⟨payload, identity, default, codes, rfl, metadata, projectedArray, defined, generated, codeTypes⟩ :=
          CompatibleExpressionArrays.arrayLiteral_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, typing⟩ :=
          CellAwareInvocationArrayBounds.literal_source_types unique site.found formEq site.coercions typed
        have relation := argument_rel
          (relation := fun value lowered => NestedTree whole headers called (context whole.indexed named)
            whole.indexed.fuel (context whole.indexed named).solvedRequirements source sourceContext reasonAt scope
            value lowered)
          (fun value member {lowered} valueGenerated => by
            obtain ⟨_, valueFound⟩ := nested_found (children value member)
            obtain ⟨_, _, tree⟩ := lift member
              (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member
                valueFound) valueGenerated
            exact tree)
          generated
        obtain ⟨lengths, each⟩ := zip_of_rel relation
        exact .arrayLiteral metadata formEq lengths (fun value member => nested_found (children value member))
          codeTypes short projectedArray defined
          (layouts.extend (CallableIndexedAmbient.ambientDefinitions whole.indexed).basePrefix) each
      | @toArray element arrayElement slice sliceBase sliceStart sliceStop sliceNode sliceFound sliceForm
          sliceType =>
        obtain ⟨depth, layout, comparison, first, rfl, metadata, firstGenerated, shaped, prepared⟩ :=
          CompatibleExpressionArrays.toArray_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt)
            site.found special read leaf accepted formEq
        obtain ⟨_, _, sliceTyped, _⟩ :=
          CellAwareInvocationArrayBounds.copy_source_types unique site.found formEq site.coercions typed
        obtain ⟨_, sliceFound', sliceTree⟩ :=
          lift (by simp [Staging.Recursive.arrayChildren]) sliceTyped firstGenerated
        cases Option.some.inj (sliceFound'.symm.trans sliceFound)
        have sliceProjected := projected sliceTree sliceFound
        rw [sliceType] at sliceProjected
        obtain ⟨rfl, valueType, dataType, rfl⟩ := slice_shape sliceProjected shaped
        exact .copy metadata formEq sliceFound sliceForm shaped prepared sliceTree
  | @memrefLoad id reference site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨layout, comparison, referenceCode, rfl, metadata, referenceGenerated, memrefShaped, prepared⟩ :=
        CompatibleExpressionArrays.memrefLoad_of_functions (policy := namedPolicy generation rootFuel)
          (body := namedLowerBody generation) (context := context whole.indexed named)
          (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt) site.found
          (fun child budget => CellAwareInvocationAcceptedMemrefSites.special generation site form (.load _) rootFuel
            child budget scope reasonAt)
          (CellAwareInvocationAcceptedMemrefSites.read generation site form (.load _) rootFuel)
          (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer accepted form
      cases fuel with
      | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at referenceGenerated
      | succ fuel =>
        obtain ⟨layout', firstCode, secondCode, rfl, referenceMetadata, firstGenerated, shaped, secondGenerated, _⟩ :=
          CompatibleExpressionArrays.elementRef_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt) site.referenceFound
            (fun child budget => CellAwareInvocationAcceptedMemrefSites.reference_special generation site rootFuel
              child budget scope reasonAt)
            (CellAwareInvocationAcceptedMemrefSites.reference_read generation site rootFuel)
            (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer
            referenceGenerated site.referenceForm
        obtain rfl := memref_layout shaped memrefShaped
        have referenceTyped := CellAwareInvocationArrayBounds.load_source_types unique site.found form site.coercions
          typed
        obtain ⟨baseTyped, _, subscriptTyped, _⟩ := CellAwareInvocationArrayBounds.reference_source_types unique
          site.referenceFound site.referenceForm site.referenceCoercions referenceTyped
        obtain ⟨baseNode, baseContains, baseNodeType⟩ := baseTyped.stored_type
        obtain ⟨subscriptNode, subscriptContains, subscriptNodeType⟩ := subscriptTyped.stored_type
        have baseFound := lookupExpression?_complete unique baseContains
        have subscriptFound := lookupExpression?_complete unique subscriptContains
        rw [← baseNodeType] at baseTyped
        rw [← subscriptNodeType] at subscriptTyped
        exact .memrefLoad metadata form referenceMetadata site.referenceForm baseFound subscriptFound shaped prepared
          (firstIH baseFound baseTyped firstGenerated) (secondIH subscriptFound subscriptTyped secondGenerated)
  | @memrefStore id reference value site form first second third firstIH secondIH thirdIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨layout, comparison, referenceCode, valueCode, rfl, metadata, referenceGenerated, memrefShaped,
          valueGenerated, valueType, prepared⟩ :=
        CompatibleExpressionArrays.memrefStore_of_functions (policy := namedPolicy generation rootFuel)
          (body := namedLowerBody generation) (context := context whole.indexed named)
          (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt) site.found
          (fun child budget => CellAwareInvocationAcceptedMemrefSites.special generation site form (.store _ _)
            rootFuel child budget scope reasonAt)
          (CellAwareInvocationAcceptedMemrefSites.read generation site form (.store _ _) rootFuel)
          (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer accepted form
      obtain ⟨_, _, referenceTyped, valueTyped⟩ := CellAwareInvocationArrayBounds.store_source_types unique site.found
        form site.coercions typed
      obtain ⟨valueNode, valueContains, valueNodeType⟩ := valueTyped.stored_type
      have valueFound := lookupExpression?_complete unique valueContains
      rw [← valueNodeType] at valueTyped
      have valueTree := thirdIH valueFound valueTyped valueGenerated
      cases fuel with
      | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at referenceGenerated
      | succ fuel =>
        obtain ⟨layout', firstCode, secondCode, rfl, referenceMetadata, firstGenerated, shaped, secondGenerated, _⟩ :=
          CompatibleExpressionArrays.elementRef_of_functions (policy := namedPolicy generation rootFuel)
            (body := namedLowerBody generation) (context := context whole.indexed named)
            (values := .initial whole.compatible.checked) (scope := scope) (reasonAt := reasonAt) site.referenceFound
            (fun child budget => CellAwareInvocationAcceptedMemrefSites.reference_special generation site rootFuel
              child budget scope reasonAt)
            (CellAwareInvocationAcceptedMemrefSites.reference_read generation site rootFuel)
            (GeneralizedLocalInitializerCompilation.namedPolicy_recipe generation rootFuel).leafLowerer
            referenceGenerated site.referenceForm
        obtain rfl := memref_layout shaped memrefShaped
        obtain ⟨baseTyped, _, subscriptTyped, _⟩ := CellAwareInvocationArrayBounds.reference_source_types unique
          site.referenceFound site.referenceForm site.referenceCoercions referenceTyped
        obtain ⟨baseNode, baseContains, baseNodeType⟩ := baseTyped.stored_type
        obtain ⟨subscriptNode, subscriptContains, subscriptNodeType⟩ := subscriptTyped.stored_type
        have baseFound := lookupExpression?_complete unique baseContains
        have subscriptFound := lookupExpression?_complete unique subscriptContains
        rw [← baseNodeType] at baseTyped
        rw [← subscriptNodeType] at subscriptTyped
        exact .memrefStore metadata form referenceMetadata site.referenceForm baseFound subscriptFound valueFound shaped
          valueType prepared (firstIH baseFound baseTyped firstGenerated)
          (secondIH subscriptFound subscriptTyped secondGenerated) valueTree

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedTrees
end

section
/-! Meaning of the nested receipt trees. The first subset's forms use their
existing heads with the meaning of their own children, by structural
recursion on the tree; a call uses the direct-call head, with the meaning of
its argument receipts and its evidence from the call's empty requirements; a
conversion uses the conversion head, with the dirty-integer token law; an index
uses the index head, with the key equality of the function model and the
missing-default fault of its header (`MissingDefaults`); a reference to a
builtin closure uses the builtin value bounds, with the function model's
inclusion of the builtin values; a call of a builtin closure uses the
contracted builtin head, with the meaning of its argument receipts; and a tuple
uses the tuple head, with the meaning of its element receipts. The application of
each admitted callee header below the grade is the input that the row lemma
supplies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedNestedTrees (NestedTree)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)
open DataPatternValues (ListRel)
universe u

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) :
    stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

/-- The arguments of one call, each at its lowered code. -/
private def Arguments (scope : SourceCoreLocalCell.Scope) (ids : List ExpressionId)
    (codes : List SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ (child, code) ∈ ids.zip codes

private theorem rel_of_zip {α β : Type} {relation : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length → (∀ pair ∈ xs.zip ys, relation pair.1 pair.2) →
      ListRel relation xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | x :: xs, y :: ys, lengths, each =>
    .cons (each (x, y) (by rw [List.zip_cons_cons]; exact List.mem_cons_self))
      (rel_of_zip (by simpa using lengths)
        (fun pair member => each pair (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ member)))

private theorem arguments_rel {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {codes : List SourceCoreBasic.LoweredExpr} (lengths : ids.length = codes.length)
    (found : ∀ argument ∈ ids, ∃ node, source.lookupExpression? argument = some node) :
    ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ Arguments scope ids codes scope id code)
      ids codes :=
  rel_of_zip lengths fun pair member => by
    obtain ⟨node, nodeFound⟩ := found pair.1 (List.of_mem_zip member).1
    exact ⟨node, nodeFound, rfl, member⟩

/-- The missing-default fault of every index header of a Source, at its
reason, as a fault relation decodes it. -/
def MissingDefaults (compiled : SourceCoreUnifiedCompilation.Compiled) (registry : SourceCoreRawMetadata.Registry)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (source : TypedSource) (reasonAt : ExpressionId → Word) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  ∀ {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {first second : SourceCoreBasic.LoweredExpr}
    (header : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked) source id base node baseNode
      layout comparison first second),
    source.lookupExpression? key = some keyNode → node.form = .index base key →
    ∀ mapping world baseSource keySource baseValue,
      CompatibleExpressionIndices.MissingPolicy (keyNode := keyNode) (registry := registry) header functions mapping
        world baseSource keySource baseValue (reasonAt id) (fun error token => faults (.semantic error) token)

/-- A named row's issuer and the public receiver give the missing-default
fault of every index header of the row's Source. -/
theorem missingDefaults {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {reasonAt : ExpressionId → Word}
    (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named reasonAt)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key =
      .ok named.specialized)
    {source : TypedSource} (sourceEq : source = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique source)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
      completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :
    MissingDefaults compiled completion.result.context.registry functions source reasonAt
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  intro id base key node baseNode keyNode layout comparison first second header keyFound form mapping world
    baseSource keySource baseValue
  obtain ⟨port⟩ := CellAwareNamedIndexDiagnostics.ready issuer record sourceEq unique header
  exact port.missing receiver functions keyFound form mapping world baseSource keySource baseValue

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : OwnedKey keys) {compilation : SourceCoreFunctions.Context}
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun current => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix current.scope current.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (cache : ∀ {current}, callerProtocol.State current →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled current.mapping current.store)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (included : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functions)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (missing : MissingDefaults compiled rawRegistry functions invocation.source reasonAt faults)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram)
    registry)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  {called : DeclarationInstantiation → Prop}

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include callerBridge keyPhysical cache faithful functionLeaves functionTypes included extension sameLedger uninitialized
  missing
  selectedBodies wellFormed runtime covers in
/-- Every nested receipt tree preserves its staged Source execution at every
grade, given the application of every admitted callee header below the
grade. -/
theorem preserves_nested_tree [RecursiveStageMeaning.FaultTokens faults]
    [CellAwareInvocationAcceptedConversionFaults.DirtyToken faults] {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : NestedTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) :
    ∀ size, (∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) →
    PreservesAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree with
  | plain receipt =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.preserves callerBridge.forgetSlots functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope inner lowered) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_preserves callerBridge.forgetSlots unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope left right first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_preserves callerBridge.forgetSlots unique (product_values functions) size
      children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH
      rightIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; intro _; exact testIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; intro _; exact yesIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; intro _; exact noIH childSize below ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call policy body fuel id callee ids instantiation lowered receipt port requirements monomorphic selected
      lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := rows.1 ▸ stored ▸ sequence
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.preserves owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ nodeFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
  | @conversion id node callee argument function target argumentCode metadata form conversion argumentFound
      child ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope argument ⟨.word, argumentCode⟩) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedConversions.preserves callerBridge.forgetSlots functions
      ⟨metadata.found, form, metadata.coercions, metadata.requirements, conversion, argumentFound⟩
      unique selectedBodies runtime covers size children ⟨rfl, rfl, rfl⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      baseTree keyTree baseIH keyIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base key first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact keyIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationIndexBounds.preserves_selected callerBridge.forgetSlots functions faults unique
      selectedBodies runtime covers header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ (missing header keyFound form) size children ⟨rfl, rfl, rfl⟩
  | builtinValue header _ =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationBuiltinValueBounds.preserves callerBridge.forgetSlots functions profile included faults
      unique size ⟨header⟩
  | @builtin policy body fuel id callee ids function lowered receipt nativeTypes lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨typing, _sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types unique
      receipt.metadata.found receipt.form receipt.metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    exact CellAwareInvocationAcceptedBuiltins.preserves callerBridge.forgetSlots functions functionLeaves faults
      unique selectedBodies runtime covers (receipt.result ▸ receipt.metadata) receipt.form nativeTypes size ordered
      childMeaning ⟨rfl, rfl, receipt.output⟩ nodeFound typed environments heaps locals agrees actualTyped
      initial admitted authority physical frameOwner ownerFrame trace
  | @tuple id node ids codes metadata form _ lengths found elements ih =>
    intro size applications current child code point actualNode nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans metadata.found)
    obtain ⟨types, typing, sourceType⟩ :=
      CompatibleExpressionTuples.source_types unique metadata.found form metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids codes) faults size := by
      intro smaller less current element elementCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (element, elementCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    exact CellAwareInvocationTupleBounds.tuple_preserves callerBridge.forgetSlots functions faults unique
      selectedBodies runtime covers size childMeaning ⟨_, ids, types, codes, rfl,
        ⟨metadata, form, sourceType⟩, ordered⟩ nodeFound typed
  | @constructor id node instantiation ids tag header codes receipt form ranges lengths found arguments ih =>
    intro size applications current child code point actualNode nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame trace
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
      unique receipt.metadata.found form receipt.metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    exact CellAwareInvocationAcceptedConstructors.preserves callerBridge.forgetSlots functions extension faults
      unique selectedBodies runtime covers receipt form ranges size ordered childMeaning ⟨rfl, rfl, rfl⟩ nodeFound
      typed environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame
      trace
  | @arrayLength id node base baseNode first lowered metadata form baseFound code baseTree ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope base first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.length_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      ⟨rfl, rfl, rfl⟩ code size children ⟨rfl, rfl, rfl⟩
  | @arrayIndex id node base subscript baseNode subscriptNode depth fuel layout comparison first second metadata
      form baseFound subscriptFound shaped prepared baseTree subscriptTree baseIH subscriptIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base subscript first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.index_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      subscriptFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceRange id node base start stop baseNode startNode stopNode depth layout first startCode stopCode metadata
      form baseFound startFound stopFound shaped baseTree startTree stopTree baseIH startIH stopIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope base start stop first startCode stopCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with left | middle | right
      · obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := middle; intro _; exact startIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := right; intro _; exact stopIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_range_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      startFound stopFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ shaped
      rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceFrom id node base bound baseNode boundNode depth layout first boundCode metadata form baseFound
      boundFound shaped baseTree boundTree baseIH boundIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base bound first boundCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact boundIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_from_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      boundFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceTo id node base bound baseNode boundNode depth layout first boundCode metadata form baseFound
      boundFound shaped baseTree boundTree baseIH boundIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base bound first boundCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact boundIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_to_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      boundFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceWhole id node base baseNode depth layout first metadata form baseFound shaped baseTree ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope base first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_whole_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      ⟨rfl, rfl, rfl⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @newArray id node element length lengthNode payload identity default first metadata form lengthFound projected
      defined layouts lengthTree ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope length first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.new_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form lengthFound
      ⟨rfl, rfl, rfl⟩ projected defined layouts rfl size children ⟨rfl, rfl, rfl⟩
  | @arrayLiteral id node element elements payload identity default codes metadata form lengths found codeTypes
      short projected defined layouts elementTrees ih =>
    intro size applications
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have childMeaning : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope elements codes) faults size := by
      intro smaller less current member memberCode inside _
      obtain ⟨currentEq, inside⟩ := inside
      subst current
      exact ih (member, memberCode) inside smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.literal_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form sequence
      codeTypes short projected defined layouts rfl size childMeaning ⟨rfl, rfl, rfl⟩
  | @copy id node element slice sliceNode sliceBase sliceStart sliceStop valueType dataType comparison fuel first
      metadata form sliceFound sliceForm shaped prepared sliceTree ih =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope slice first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.copy_preserves callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form sliceFound
      ⟨rfl, rfl, rfl⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @memrefLoad id node reference referenceNode base subscript baseNode subscriptNode layout comparison fuel first
      second metadata form referenceMetadata referenceForm baseFound subscriptFound shaped prepared baseTree
      subscriptTree baseIH subscriptIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base subscript first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.load_preserves callerBridge.forgetSlots functions faults unique selectedBodies
      runtime covers metadata form referenceMetadata referenceForm baseFound subscriptFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩
      ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @memrefStore id node reference value referenceNode base subscript baseNode subscriptNode valueNode layout
      comparison fuel first second third metadata form referenceMetadata referenceForm baseFound subscriptFound
      valueFound shaped valueType prepared baseTree subscriptTree valueTree baseIH subscriptIH valueIH =>
    intro size applications
    have children : PreservesBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope base subscript value first second third) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with left | middle | right
      · obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := middle; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := right; intro _; exact valueIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.store_preserves callerBridge.forgetSlots functions faults unique selectedBodies
      runtime covers metadata form referenceMetadata referenceForm baseFound subscriptFound valueFound
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ shaped valueType prepared
      rfl size children ⟨rfl, rfl, rfl⟩

include callerBridge keyPhysical cache faithful functionLeaves functionTypes included extension sameLedger uninitialized
  missing
  selectedBodies wellFormed runtime covers in
/-- Native completion of every nested receipt tree reconstructs its staged
Source execution, given the native application of every admitted callee
header below the grade. -/
theorem reflects_nested_tree [RecursiveStageMeaning.FaultTokens faults]
    [CellAwareInvocationAcceptedConversionFaults.DirtyToken faults] {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : NestedTree compiled headers called compilation readFuel solved invocation.source context reasonAt scope id
      lowered) :
    ∀ size, (∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
        (keys := keys) valueModel registry faults header size) →
    ReflectsAt (attachment := attachment) callerBridge.forgetSlots context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree with
  | plain receipt =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.reflects callerBridge.forgetSlots functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro size applications current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_reflects callerBridge.forgetSlots unique size (ih size applications)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope left right first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_reflects callerBridge.forgetSlots unique (product_values functions) size
      children size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType amountType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH
      rightIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact leftIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact rightIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; intro _; exact testIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; intro _; exact yesIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; intro _; exact noIH childSize below ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected callerBridge.forgetSlots functions size size
      (Nat.le_refl _) unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)
  | @call policy body fuel id callee ids instantiation lowered receipt port requirements monomorphic selected
      lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_sourceTypes, _calleeValid, application, typing⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
        receipt.form receipt.metadata.coercions typed
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types receipt port.toReady
      wellFormed runtime.signatures application
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := rows.1 ▸ stored ▸ sequence
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    have evidenceAt := CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence receipt port
      (monomorphic.ordinary _) requirements context invocation.evidence
    exact CellAwareInvocationAcceptedDirectCalls.reflects owner receipt port evidenceAt callerBridge keyPhysical cache
      valueModel index registry faults unique wellFormed runtime covers size ordered childMeaning
      (applications port.header port.member (port.metadata ▸ selected)) ⟨rfl, rfl, rfl⟩ nodeFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
  | @conversion id node callee argument function target argumentCode metadata form conversion argumentFound
      child ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope argument ⟨.word, argumentCode⟩) faults (size + 1) :=
      fun childSize within => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_of_lt_of_le less (Nat.le_of_lt_succ within)))
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationAcceptedConversions.reflects callerBridge.forgetSlots functions
      ⟨metadata.found, form, metadata.coercions, metadata.requirements, conversion, argumentFound⟩
      unique selectedBodies runtime covers size children ⟨rfl, rfl, rfl⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType
      baseTree keyTree baseIH keyIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base key first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; intro _; exact keyIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationIndexBounds.reflects_selected callerBridge.forgetSlots functions faults unique
      selectedBodies runtime covers header keyFound form sourceType faithful functionLeaves functionTypes
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ (missing header keyFound form) size children ⟨rfl, rfl, rfl⟩
  | builtinValue header _ =>
    intro size _ current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationBuiltinValueBounds.reflects callerBridge.forgetSlots functions profile included faults
      size ⟨header⟩
  | @builtin policy body fuel id callee ids function lowered receipt nativeTypes lengths found arguments ih =>
    intro size applications current child code point node nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨typing, _sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types unique
      receipt.metadata.found receipt.form receipt.metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids receipt.codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    exact CellAwareInvocationAcceptedBuiltins.reflects callerBridge.forgetSlots functions functionLeaves faults
      unique selectedBodies runtime covers (receipt.result ▸ receipt.metadata) receipt.form nativeTypes size ordered
      childMeaning ⟨rfl, rfl, receipt.output⟩ nodeFound typed environments heaps locals agrees actualTyped
      initial admitted authority physical frameOwner ownerFrame completed
  | @tuple id node ids codes metadata form _ lengths found elements ih =>
    intro size applications current child code point
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids codes) faults (size + 1) := by
      intro smaller less current element elementCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (element, elementCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below
            (Nat.lt_of_lt_of_le belowLess (Nat.le_of_lt_succ less)))
        ⟨rfl, rfl, rfl⟩
    intro actualNode nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    cases Option.some.inj (nodeFound.symm.trans metadata.found)
    obtain ⟨types, typing, sourceType⟩ :=
      CompatibleExpressionTuples.source_types unique metadata.found form metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    exact CellAwareInvocationTupleBounds.tuple_reflects callerBridge.forgetSlots functions faults unique
      selectedBodies runtime covers size childMeaning ⟨_, ids, types, codes, rfl,
        ⟨metadata, form, sourceType⟩, ordered⟩ nodeFound typed
  | @constructor id node instantiation ids tag header codes receipt form ranges lengths found arguments ih =>
    intro size applications current child code point actualNode nodeFound typed
      mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame completed
    obtain ⟨currentEq, childEq, codeEq⟩ := point
    subst current child code
    cases Option.some.inj (nodeFound.symm.trans receipt.metadata.found)
    obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
      unique receipt.metadata.found form receipt.metadata.coercions typed
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have stored := tree_types sequence unique typing
    have ordered := stored ▸ sequence
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope ids codes) faults size := by
      intro smaller less current argument argumentCode member _
      obtain ⟨currentEq, member⟩ := member
      subst current
      exact ih (argument, argumentCode) member smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    exact CellAwareInvocationAcceptedConstructors.reflects callerBridge.forgetSlots functions extension faults
      unique selectedBodies runtime covers receipt form ranges size ordered childMeaning ⟨rfl, rfl, rfl⟩ nodeFound
      typed environments heaps locals agrees actualTyped initial admitted authority physical frameOwner ownerFrame
      completed
  | @arrayLength id node base baseNode first lowered metadata form baseFound code baseTree ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope base first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.length_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      ⟨rfl, rfl, rfl⟩ code size children ⟨rfl, rfl, rfl⟩
  | @arrayIndex id node base subscript baseNode subscriptNode depth fuel layout comparison first second metadata
      form baseFound subscriptFound shaped prepared baseTree subscriptTree baseIH subscriptIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base subscript first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.index_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      subscriptFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceRange id node base start stop baseNode startNode stopNode depth layout first startCode stopCode metadata
      form baseFound startFound stopFound shaped baseTree startTree stopTree baseIH startIH stopIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope base start stop first startCode stopCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with left | middle | right
      · obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := middle; intro _; exact startIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := right; intro _; exact stopIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_range_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      startFound stopFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ shaped
      rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceFrom id node base bound baseNode boundNode depth layout first boundCode metadata form baseFound
      boundFound shaped baseTree boundTree baseIH boundIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base bound first boundCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact boundIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_from_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      boundFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceTo id node base bound baseNode boundNode depth layout first boundCode metadata form baseFound
      boundFound shaped baseTree boundTree baseIH boundIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base bound first boundCode) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact boundIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_to_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      boundFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @sliceWhole id node base baseNode depth layout first metadata form baseFound shaped baseTree ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope base first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.slice_whole_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form baseFound
      ⟨rfl, rfl, rfl⟩ shaped rfl size children ⟨rfl, rfl, rfl⟩
  | @newArray id node element length lengthNode payload identity default first metadata form lengthFound projected
      defined layouts lengthTree ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope length first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.new_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form lengthFound
      ⟨rfl, rfl, rfl⟩ projected defined layouts rfl size children ⟨rfl, rfl, rfl⟩
  | @arrayLiteral id node element elements payload identity default codes metadata form lengths found codeTypes
      short projected defined layouts elementTrees ih =>
    intro size applications
    obtain ⟨_storedTypes, sequence⟩ := DataExpressionSequence.Tree.of_children
      (arguments_rel (source := invocation.source) (scope := scope) lengths found)
    have childMeaning : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Arguments scope elements codes) faults size := by
      intro smaller less current member memberCode inside _
      obtain ⟨currentEq, inside⟩ := inside
      subst current
      exact ih (member, memberCode) inside smaller
        (fun header headerMember headerAdmitted below belowLess =>
          applications header headerMember headerAdmitted below (Nat.lt_trans belowLess less))
        ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.literal_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form sequence
      codeTypes short projected defined layouts rfl size childMeaning ⟨rfl, rfl, rfl⟩
  | @copy id node element slice sliceNode sliceBase sliceStart sliceStop valueType dataType comparison fuel first
      metadata form sliceFound sliceForm shaped prepared sliceTree ih =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Point scope slice first) faults size :=
      fun childSize smaller => ih childSize (fun header member admitted below less =>
        applications header member admitted below (Nat.lt_trans less smaller))
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.copy_reflects callerBridge.forgetSlots functions faults unique selectedBodies runtime covers metadata form sliceFound sliceForm
      ⟨rfl, rfl, rfl⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @memrefLoad id node reference referenceNode base subscript baseNode subscriptNode layout comparison fuel first
      second metadata form referenceMetadata referenceForm baseFound subscriptFound shaped prepared baseTree
      subscriptTree baseIH subscriptIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Two scope base subscript first second) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.load_reflects callerBridge.forgetSlots functions faults unique selectedBodies
      runtime covers metadata form referenceMetadata referenceForm baseFound subscriptFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩
      ⟨rfl, .inr ⟨rfl, rfl⟩⟩ shaped prepared rfl size children ⟨rfl, rfl, rfl⟩
  | @memrefStore id node reference value referenceNode base subscript baseNode subscriptNode valueNode layout
      comparison fuel first second third metadata form referenceMetadata referenceForm baseFound subscriptFound
      valueFound shaped valueType prepared baseTree subscriptTree valueTree baseIH subscriptIH valueIH =>
    intro size applications
    have children : ReflectsBelow (attachment := attachment) callerBridge.forgetSlots context valueModel index
        registry invocation (Three scope base subscript value first second third) faults size := by
      intro childSize smaller current child code point
      have below : ∀ header, header ∈ headers → called header.instantiation →
          CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := attachment) (headers := headers)
            (keys := keys) valueModel registry faults header childSize :=
        fun header member admitted below less => applications header member admitted below (Nat.lt_trans less smaller)
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with left | middle | right
      · obtain ⟨rfl, rfl⟩ := left; intro _; exact baseIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := middle; intro _; exact subscriptIH childSize below ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := right; intro _; exact valueIH childSize below ⟨rfl, rfl, rfl⟩
    intro current expression code' point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationArrayBounds.store_reflects callerBridge.forgetSlots functions faults unique selectedBodies
      runtime covers metadata form referenceMetadata referenceForm baseFound subscriptFound valueFound
      ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩ shaped valueType prepared
      rfl size children ⟨rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedBounds
end

section
/-! The expression closure with direct calls at every expression position of a
named-row body. `ClosedNested` states that every expression the compiler
accepts for the body is a nested site. The receipt tree of each accepted
expression is extracted from the compiler's own acceptance and closed by the
nested bounds; the inputs are the call authority of the body's call receipts
and the application of every admitted callee header below the budget, as for
`CellAwareInvocationAcceptedCallExpressions`. A row whose accepted expressions
are extended roots is closed in this sense too (`closedNested_of_closedCalls`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedCallExpressions (ClosedCalls Ports)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (called : DeclarationInstantiation → Prop)

/-- The nested sites as a predicate on the actual accepted receipts of the
named row. -/
def Accepted (fuel : Nat) : GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children (rowIndex generation record) fuel scope expression lowered ∧
    Nested whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- Every expression the compiler accepts for the named row, at any fuel and
scope, is a nested site. -/
def ClosedNested : Prop :=
  ∀ fuel scope expression lowered, children (rowIndex generation record) fuel scope expression lowered →
    Nested whole.indexed named (CallableIndexedNamedGeneration.source named) called expression

/-- A row whose accepted expressions are extended roots is closed with nested
calls. -/
theorem closedNested_of_closedCalls (closed : ClosedCalls generation record called) :
    ClosedNested generation record called :=
  fun fuel scope expression lowered accepted =>
    CellAwareInvocationAcceptedNestedTrees.of_call_subset (closed fuel scope expression lowered accepted)

variable {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (owner : OwnedKey keys) (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context (rowIndex generation record).reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location))
        ((rowIndex generation record).reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted nested site of the named row preserves its staged Source
execution at every grade, given the call authority and the application of
every admitted callee header below the grade. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults]
    [CellAwareInvocationAcceptedConversionFaults.DirtyToken faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (profile : whole.compatible.checked.catalog.callableContracts = true)
    (included : (CallableIndexedBuiltinValues.model whole.indexed profile).Includes functions)
    (missing : CellAwareInvocationAcceptedNestedBounds.MissingDefaults whole receiving functions invocation.source
      (rowIndex generation record).reasonAt faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header size) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context
      model (rowIndex generation record) registry invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, nested⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedNestedTrees.of_nested (headers := headers) generation rootFuel nested
      unique physical.declarations ports found typed generated
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedNestedBounds.preserves_nested_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions faithful functionLeaves functionTypes profile included extension
      sameLedger faults
      uninitialized missing selectedBodies wellFormed sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩
      found typed environments heaps locals agrees actualTyped initial admitted authority physical

/-- Every completed native run of an accepted nested site reconstructs an
independent Source grade, outcome and reached heap. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults]
    [CellAwareInvocationAcceptedConversionFaults.DirtyToken faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (profile : whole.compatible.checked.catalog.callableContracts = true)
    (included : (CallableIndexedBuiltinValues.model whole.indexed profile).Includes functions)
    (missing : CellAwareInvocationAcceptedNestedBounds.MissingDefaults whole receiving functions invocation.source
      (rowIndex generation record).reasonAt faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context
      (rowIndex generation record).source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (rowIndex generation record).compilation.solvedRequirements)
    (ports : Ports (headers := headers) generation record) (size : Nat)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header size) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := fun _ _ _ => True)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots context
      model (rowIndex generation record) registry invocation (Accepted generation record called fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) context invocation.source :=
    sourceEq ▸ runtime
  have uninitialized := reads_lowered generation record invocation faults (fuel := whole.indexed.fuel)
    (context := context) sourceEq reads
  intro scope id lowered accepted node found typed mapping world administrative environment canonical
    actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
    initial admitted authority physical
  obtain ⟨generated, nested⟩ := accepted
  have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
  change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
  | succ rootFuel =>
    rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
    have unique := sourceRuntime.graph.nodeOccurrencesUnique
    rw [sourceNamed] at unique found typed
    have tree := CellAwareInvocationAcceptedNestedTrees.of_nested (headers := headers) generation rootFuel nested
      unique physical.declarations ports found typed generated
    rw [← sourceNamed] at tree found typed
    exact CellAwareInvocationAcceptedNestedBounds.reflects_nested_tree (attachment := fun _ _ _ => True)
      (compilation := CallableIndexedNamedGeneration.context whole.indexed named) owner
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations) keyPhysical
      (fun state => state.physical) functions faithful functionLeaves functionTypes profile included extension
      sameLedger faults
      uninitialized missing selectedBodies wellFormed sourceRuntime covers tree size applications ⟨rfl, rfl, rfl⟩
      found typed environments heaps locals agrees actualTyped initial admitted authority physical

/-- A named row whose accepted expressions are all nested sites discharges the
accepted-expression input of the statement closure on the slot-retaining
protocol at a budget, given the call authority and the application of every
admitted callee header below the budget. -/
theorem expressions [RecursiveStageMeaning.FaultTokens faults]
    [CellAwareInvocationAcceptedConversionFaults.DirtyToken faults] (closed : ClosedNested generation record called)
    (budget : Nat)
    (sourceEq : invocation.source = (rowIndex generation record).source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record) faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : CompatibleEquality.FunctionObservations whole.compatible.checked.catalog functions identities)
    (functionTypes : FunctionRuntimeViews functions)
    (profile : whole.compatible.checked.catalog.callableContracts = true)
    (included : (CallableIndexedBuiltinValues.model whole.indexed profile).Includes functions)
    (missing : CellAwareInvocationAcceptedNestedBounds.MissingDefaults whole receiving functions invocation.source
      (rowIndex generation record).reasonAt faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked whole.sourceProgram)
      registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    (ports : Ports (headers := headers) generation record)
    (applications : ∀ header, header ∈ headers → called header.instantiation →
      CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header budget ∧
      CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True) (headers := headers)
        (keys := keys) model registry faults header budget) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True) (receiving := receiving)
      (functions := functions)
      (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
      (rowIndex generation record) registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size smaller scope id lowered generated
    exact preserves generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads faithful functionLeaves functionTypes profile included missing selectedBodies wellFormed runtime covers
      sameLedger ports
      size
      (fun header member admitted below less => (applications header member admitted).1 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩
  · intro size smaller scope id lowered generated
    exact reflects generation record called owner keyPhysical registry invocation faults fuel sourceEq extension
      reads faithful functionLeaves functionTypes profile included missing selectedBodies wellFormed runtime covers
      sameLedger ports
      size
      (fun header member admitted below less => (applications header member admitted).2 below
        (Nat.lt_trans less smaller))
      ⟨generated, closed fuel scope id lowered generated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
/-! The size induction across bodies for direct calls. A family of rows is
given by the instantiations it admits (`called`): every catalog header with an
admitted instantiation has the receipts of a named row whose accepted
expressions are nested sites calling only admitted instantiations (`Row`).
One strong induction on the grade gives the accepted-expression meaning of
every family body on the slot-retaining protocol: at a call of a given grade
the direct-call head needs the callee's application below that grade, and the
row lemma gives it from the callee body's expressions below it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CellAwareInvocationAcceptedNamedInvocation (rowIndex)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (Key whole (Program.ofChecked whole.sourceProgram))}

/-- The receipts of one family row, as the public named root takes them, with
the nested closure and call authority of its body and its own registry
scope. -/
structure Row (called : DeclarationInstantiation → Prop)
    (header : Header whole (Program.ofChecked whole.sourceProgram)) where
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Expr
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code
  record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized
  sameNamed : header.named = named
  sameLayouts : header.layouts = whole.indexed.layouts
  sameGlobals : header.globals = whole.indexed.base.globals.length
  sameBindings : header.bindings = named.inputs
  sameBody : header.body = generation.body
  sameSolved : header.solved = named.specialized.function.solvedRequirements
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics
  assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments
  body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body
  covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True) (rowIndex generation record))
    body.tree
  native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key)
  closed : CellAwareInvocationAcceptedNestedExpressions.ClosedNested generation record called
  ports : CellAwareInvocationAcceptedCallExpressions.Ports (headers := headers) generation record
  bodyScope : Staging.Recursive.Scope
  bodySelected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function bodyScope

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (support : SelectedCompilationNamedSupport.Support whole)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
  {called : DeclarationInstantiation → Prop}
  (rows : ∀ header, header ∈ headers → called header.instantiation → Row (headers := headers) called header)

local notation "rootFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry rootFunctions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem row_source {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) {child : Staging.Recursive.Scope}
    (selected : (stages).Closure header.function child) :
    child.source = (rowIndex row.generation row.record).source := by
  show child.source = CallableIndexedNamedGeneration.source row.named
  rw [← row.sameNamed]
  exact ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source

include support in
private theorem row_unique {header : Header whole (Program.ofChecked whole.sourceProgram)}
    (row : Row (headers := headers) called header) :
    NodeOccurrencesUnique (CallableIndexedNamedGeneration.source row.named) := by
  obtain ⟨_facts, certificate⟩ := support.certified header
  have functionUnique : NodeOccurrencesUnique header.function.source := by
    rw [header.frame.source]
    exact certificate.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [← row.sameNamed]
  simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using functionUnique

include profile receiver support artifact checked wellFormed rows in
/-- Every family body has its accepted-expression meaning on the
slot-retaining protocol at every grade, for every owner key with physical
locations and every registry scope of its function. -/
theorem expressions (size : Nat) :
    ∀ header (member : header ∈ headers) (admitted : called header.instantiation) (owner : OwnedKey keys)
      (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
      {child : Staging.Recursive.Scope}, (stages).Closure header.function child →
      CellAwareInvocationAcceptedInputs.Expressions (attachment := fun _ _ _ => True)
        (receiving := completion.result.context.registry) (functions := rootFunctions)
        (CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller owner 1 keyPhysical.locations).forgetSlots
        (rowIndex (rows header member admitted).generation (rows header member admitted).record) stages child faults
        size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree whole receiver)
  haveI := CellAwareInvocationAcceptedConversionFaults.dirtyToken
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree whole receiver)
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member admitted owner keyPhysical child selected
    have applications : ∀ callee, callee ∈ headers → called callee.instantiation →
        CellAwareInvocationAcceptedDirectCalls.PreservesBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size ∧
        CellAwareInvocationAcceptedDirectCalls.ReflectsBelow (attachment := fun _ _ _ => True)
          (headers := headers) (keys := keys) model stages faults callee size := by
      intro callee calleeMember calleeAdmitted
      let row := rows callee calleeMember calleeAdmitted
      refine ⟨fun smaller less => ?_, fun smaller less => ?_⟩
      · exact CellAwareInvocationAcceptedNamedApplication.preserves profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed smaller
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
      · exact CellAwareInvocationAcceptedNamedApplication.reflects profile receiver callee row.generation row.record
          row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
          support row.issued row.assignments artifact checked row.body row.covered row.native smaller row.bodySelected
          (fun calleeOwner calleeKey _ calleeSelected =>
            ih smaller less callee calleeMember calleeAdmitted calleeOwner calleeKey calleeSelected)
    let row := rows header member admitted
    exact CellAwareInvocationAcceptedNestedExpressions.expressions row.generation row.record called owner keyPhysical
      stages child faults row.closed size (row_source row selected) completion.result.extension
      (CellAwareInvocationAcceptedNamedInvocation.reads row.generation row.record row.issuer receiver
        (row_unique support row))
      (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
      (CellAwarePhysicalFunctionOrigins.runtime_views profile) profile (CellAwareBuiltinValueOrigins.included profile)
      (CellAwareInvocationAcceptedNestedBounds.missingDefaults row.issuer row.record (row_source row selected)
        ((row_source row selected) ▸ row_unique support row) receiver rootFunctions)
      support.registryBodies wellFormed row.ports applications

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's application input holds for every admitted header
at every Source grade. -/
theorem preserves (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.PreservesAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.preserves profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native wellFormed size
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

include profile receiver support artifact checked wellFormed rows in
/-- The direct-call head's native application input holds for every admitted
header at every native grade. -/
theorem reflects (header : Header whole (Program.ofChecked whole.sourceProgram)) (member : header ∈ headers)
    (admitted : called header.instantiation) (size : Nat) :
    CellAwareInvocationAcceptedDirectCalls.ReflectsAt (attachment := fun _ _ _ => True) (headers := headers)
      (keys := keys) model stages faults header size :=
  let row := rows header member admitted
  CellAwareInvocationAcceptedNamedApplication.reflects profile receiver header row.generation row.record
    row.sameNamed row.sameLayouts row.sameGlobals row.sameBindings row.sameBody row.sameSolved row.projection
    support row.issued row.assignments artifact checked row.body row.covered row.native size row.bodySelected
    (fun owner keyPhysical _ selected =>
      expressions profile receiver support artifact checked wellFormed rows size header member admitted owner
        keyPhysical selected)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedCallFamily
end

section
/-! A finite check of the nested sites, as
`CellAwareInvocationAcceptedCallSubsetCheck` checks the extended roots. It
reads only a row's Source nodes, the prepared local inventory, the row's
evidence assumptions and the plan's reference edges, so it runs on an actually
compiled program. Its result is a proof that every expression node of the row
is a nested site, a declaration reference that the plan records no reference
edge for, or the callee of a conversion; the compiler lowers neither reference
on its own, so `closedNested` turns the check into `ClosedNested`. A reference
to a builtin closure is a nested site of its own, since the compiler lowers it
to the closure's value. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedCheck
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)
open CellAwareInvocationAcceptedNestedTrees (Nested)
open CellAwareInvocationAcceptedDirectSites (DirectSite)
open CellAwareInvocationAcceptedCallSubsetCheck (ReferenceSite directSite? referenceSite?)
open CellAwareInvocationAcceptedConversionSites (ConversionReference conversionSite? conversionReference?)
open CellAwareInvocationAcceptedBuiltinSites (builtinSite?)

private def all? {P : ExpressionId → Prop} (check : (id : ExpressionId) → Option (PLift (P id))) :
    (ids : List ExpressionId) → Option (PLift (∀ argument ∈ ids, P argument))
  | [] => some ⟨by intro argument member; cases member⟩
  | id :: rest => do
    let ⟨head⟩ ← check id
    let ⟨tail⟩ ← all? check rest
    pure ⟨by
      intro argument member
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact head
      · exact tail argument member⟩

/-- Proof-producing recognition of one nested site and its children. -/
def nested? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Nested prepared named source called id))
  | 0, _ => none
  | fuel + 1, id =>
    match site? prepared named source id with
    | some site =>
      match form : site.node.form with
      | .integerLiteral literal resolution => some ⟨.literal site (form ▸ .integer literal resolution)⟩
      | .reference name (.builtinBoolean value) => some ⟨.literal site (form ▸ .bool name value)⟩
      | .literal literal => some ⟨.literal site (form ▸ .word literal)⟩
      | .tuple [] => some ⟨.literal site (form ▸ .unit)⟩
      | .reference _name (.local _binder) => some ⟨.read site form⟩
      | .unary _operator operand => do
        let ⟨child⟩ ← nested? prepared named source called fuel operand
        pure ⟨.unary site form child⟩
      | .binary left _operator right => do
        let ⟨first⟩ ← nested? prepared named source called fuel left
        let ⟨second⟩ ← nested? prepared named source called fuel right
        pure ⟨.binary site form first second⟩
      | .conditional condition thenId elseId => do
        let ⟨test⟩ ← nested? prepared named source called fuel condition
        let ⟨yes⟩ ← nested? prepared named source called fuel thenId
        let ⟨no⟩ ← nested? prepared named source called fuel elseId
        pure ⟨.conditional site form test yes no⟩
      | .group inner => do
        let ⟨child⟩ ← nested? prepared named source called fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← nested? prepared named source called fuel left
        let ⟨second⟩ ← nested? prepared named source called fuel right
        pure ⟨.pair site form first second⟩
      | .index base key => do
        let ⟨first⟩ ← nested? prepared named source called fuel base
        let ⟨second⟩ ← nested? prepared named source called fuel key
        pure ⟨.index site form first second⟩
      | .reference _name (.builtinFunction function) =>
        match function.conversion? with
        | none => some ⟨.builtinValue site form⟩
        | some _ => none
      | _ => none
    | none =>
      match directSite? prepared named source id with
      | some ⟨_callee, ids, instantiation, site⟩ =>
        if selected : called instantiation then
          match all? (nested? prepared named source called fuel) ids with
          | some ⟨arguments⟩ => some ⟨.call site selected arguments⟩
          | none => none
        else none
      | none =>
        match conversionSite? prepared named source id with
        | some ⟨_callee, argument, _function, _target, site⟩ => do
          let ⟨child⟩ ← nested? prepared named source called fuel argument
          pure ⟨.conversion site child⟩
        | none =>
          match builtinSite? prepared named source id with
          | some ⟨_callee, ids, _function, site⟩ => do
            let ⟨arguments⟩ ← all? (nested? prepared named source called fuel) ids
            pure ⟨.builtin site arguments⟩
          | none =>
            match CellAwareInvocationAcceptedTupleSites.tupleSite? prepared named source id with
            | some ⟨ids, site⟩ => do
              let ⟨elements⟩ ← all? (nested? prepared named source called fuel) ids
              pure ⟨.tuple site elements⟩
            | none =>
              match CellAwareInvocationAcceptedConstructorSites.constructorSite? prepared named source id with
              | some ⟨_instantiation, ids, site⟩ => do
                let ⟨arguments⟩ ← all? (nested? prepared named source called fuel) ids
                pure ⟨.constructor site arguments⟩
              | none =>
                match CellAwareInvocationAcceptedArraySites.arraySite? prepared named source id with
                | some ⟨form, site⟩ => do
                  let ⟨children⟩ ← all? (nested? prepared named source called fuel)
                    ((Staging.Recursive.arrayChildren form).getD [])
                  pure ⟨.array site children⟩
                | none =>
                  match found : source.lookupExpression? id with
                  | none => none
                  | some node =>
                    match form : node.form with
                    | .memrefLoad reference =>
                      match CellAwareInvocationAcceptedMemrefSites.memrefSite? prepared named source id reference with
                      | none => none
                      | some site => do
                        let ⟨first⟩ ← nested? prepared named source called fuel site.base
                        let ⟨second⟩ ← nested? prepared named source called fuel site.subscript
                        pure ⟨.memrefLoad site
                          ((congrArg ExpressionNode.form (Option.some.inj (site.found.symm.trans found))).trans form)
                          first second⟩
                    | .memrefStore reference value =>
                      match CellAwareInvocationAcceptedMemrefSites.memrefSite? prepared named source id reference with
                      | none => none
                      | some site => do
                        let ⟨first⟩ ← nested? prepared named source called fuel site.base
                        let ⟨second⟩ ← nested? prepared named source called fuel site.subscript
                        let ⟨third⟩ ← nested? prepared named source called fuel value
                        pure ⟨.memrefStore site
                          ((congrArg ExpressionNode.form (Option.some.inj (site.found.symm.trans found))).trans form)
                          first second third⟩
                    | _ => none

/-- An expression node of the check: a nested site, a reference site, or the
callee of a conversion. -/
def Checked {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) (called : DeclarationInstantiation → Prop)
    (id : ExpressionId) : Prop :=
  Nested prepared named source called id ∨ Nonempty (ReferenceSite prepared named source id) ∨
    Nonempty (ConversionReference prepared named source id)

private def checkedNode? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] (fuel : Nat) (id : ExpressionId) :
    Option (PLift (Checked prepared named source called id)) :=
  match nested? prepared named source called fuel id with
  | some ⟨nested⟩ => some ⟨.inl nested⟩
  | none =>
    match referenceSite? prepared named source id with
    | some site => some ⟨.inr (.inl ⟨site⟩)⟩
    | none =>
      match conversionReference? prepared named source id with
      | some reference => some ⟨.inr (.inr ⟨reference⟩)⟩
      | none => none

private def sweep? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] (fuel : Nat) :
    (nodes : List Node) →
      Option (PLift (∀ node, Node.expression node ∈ nodes → Checked prepared named source called node.id))
  | [] => some ⟨by intro node member; cases member⟩
  | .expression node :: rest => do
    let ⟨head⟩ ← checkedNode? prepared named source called fuel node.id
    let ⟨tail⟩ ← sweep? prepared named source called fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact head
      · exact tail other member⟩
  | .statement _ :: rest => do
    let ⟨tail⟩ ← sweep? prepared named source called fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
      · exact tail other member⟩

/-- Every expression node of the Source is a nested site, a reference site or
a conversion's callee.
The fuel bounds the depth of the expression graph, which the node count
bounds. -/
def nodes? {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (called : DeclarationInstantiation → Prop) [DecidablePred called] :
    Option (PLift (∀ id node, source.lookupExpression? id = some node →
      Checked prepared named source called id)) := do
  let ⟨all⟩ ← sweep? prepared named source called (source.nodes.length + 1) source.nodes
  pure ⟨by
    intro id node found
    obtain ⟨member, same⟩ := lookupExpression?_sound found
    exact same ▸ all node member⟩

/-- `Nested` depends on its row only through the row's key and its empty
assumptions. -/
theorem transport {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : TypedSource} {first second : SourceCoreGeneralFunctions.Function}
    (keyEq : first.signature.key = second.signature.key) (assumptions : second.specialized.assumptions = [])
    {called : DeclarationInstantiation → Prop} {id : ExpressionId}
    (nested : Nested prepared first source called id) : Nested prepared second source called id := by
  induction nested with
  | literal site atomic => exact .literal (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) atomic
  | read site form => exact .read (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form
  | unary site form _ child =>
    exact .unary (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form child
  | binary site form _ _ left right =>
    exact .binary (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form left right
  | conditional site form _ _ _ test yes no =>
    exact .conditional (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form test yes no
  | group site form _ child =>
    exact .group (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form child
  | pair site form _ _ left right =>
    exact .pair (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form left right
  | call site selected _ arguments =>
    exact .call (CellAwareInvocationAcceptedCallSubsetCheck.transportDirect keyEq assumptions site) selected
      arguments
  | conversion site _ child =>
    exact .conversion (CellAwareInvocationAcceptedConversionSites.transport keyEq assumptions site) child
  | index site form _ _ first second =>
    exact .index (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form first second
  | builtinValue site form =>
    exact .builtinValue (CellAwareInvocationAcceptedSubsetCheck.transportSite keyEq site) form
  | builtin site _ arguments =>
    exact .builtin (CellAwareInvocationAcceptedBuiltinSites.transport keyEq assumptions site) arguments
  | tuple site _ elements =>
    exact .tuple (CellAwareInvocationAcceptedTupleSites.transport keyEq assumptions site) elements
  | constructor site _ arguments =>
    exact .constructor (CellAwareInvocationAcceptedConstructorSites.transport keyEq assumptions site) arguments
  | array site _ children =>
    exact .array (CellAwareInvocationAcceptedArraySites.transport keyEq assumptions site) children
  | memrefLoad site form _ _ first second =>
    exact .memrefLoad (CellAwareInvocationAcceptedMemrefSites.transport keyEq assumptions site) form first second
  | memrefStore site form _ _ _ first second third =>
    exact .memrefStore (CellAwareInvocationAcceptedMemrefSites.transport keyEq assumptions site) form first second
      third

/-- A named row whose every expression node is a nested site, a reference site
or a conversion's callee has every accepted expression a nested site. -/
theorem closedNested {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
      .ok named.specialized)
    {called : DeclarationInstantiation → Prop}
    (nodes : ∀ id node, (CallableIndexedNamedGeneration.source named).lookupExpression? id = some node →
      Checked whole.indexed named (CallableIndexedNamedGeneration.source named) called id) :
    CellAwareInvocationAcceptedNestedExpressions.ClosedNested generation record called := by
  intro fuel scope expression lowered generated
  obtain ⟨node, found⟩ := CellAwareInvocationAcceptedExpressions.found_of_children
    (ActualBodyInvocation.Index.named generation record :
      ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView) generated
  rcases nodes expression node found with nested | rejected | rejected
  · exact nested
  · obtain ⟨site⟩ := rejected
    exfalso
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
      exact CellAwareInvocationAcceptedCallSubsetCheck.reference_rejected generation site rootFuel generated
  · obtain ⟨reference⟩ := rejected
    exfalso
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual generation record] at generated
      exact CellAwareInvocationAcceptedConversionSites.reference_rejected generation reference rootFuel generated

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNestedCheck
end
