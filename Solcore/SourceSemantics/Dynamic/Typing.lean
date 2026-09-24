import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.Heap

/-!
Deep, declarative typing for source-level values and heaps.

Unlike the executable runtime's shallow type projection, these judgments
validate nominal constructor provenance, every mapping entry, closure code and
captures, and exact top-level declaration instantiations.  Heap dependence is
limited to the declared types of captured cells.  This makes the invariant
stable under allocation and type-preserving writes, including cyclic heaps of
closures.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- A closure points at an actual lambda occurrence whose form-level typing
checks monomorphic parameters, the complete statement body, and ordinary
completion at the retained result type.  The enclosing expression judgment
separately validates occurrence membership, retained types, and requirements. -/
structure ClosureCodeValid (context : Context) (function : Closure) : Prop where
  owner : context.currentDeclaration = some function.source.owner
  closed : function.context.typeParameters = []
  variables_closed : function.context.typeVariables = []
  residual_variables_open : function.context.residualTypeVariables = true
  graph : OccurrenceGraphWellFormed function.source
  occurrence :
    ∃ id node,
      ContainsExpression function.source id node ∧
      node.form = .lambda function.parameters function.resultType function.body ∧
      node.rawType = .function
        (Ty.productMany (function.parameters.map (fun binder => binder.scheme.body)))
        function.resultType ∧
      ExpressionFormHasRawType function.source context node.form
        (.function
          (Ty.productMany
            (function.parameters.map (fun binder => binder.scheme.body)))
          function.resultType) (.ordinary [])

/-- Principal code for a generalized direct-lambda local is tied to the exact
initializer occurrence and to the context in which its scheme was formed.
The empty retained requirement and coercion lists are intentional: runtime
materialization produces the lambda closure directly rather than replaying
initializer-level evidence or coercion evaluation. -/
structure GeneralizedClosureCodeValid
    (function : GeneralizedClosure) : Prop where
  owner : function.definitionContext.currentDeclaration =
    some function.source.owner
  closed : function.definitionContext.typeParameters = []
  variables_closed : function.definitionContext.typeVariables = []
  residual_variables_open :
    function.definitionContext.residualTypeVariables = true
  polymorphic : function.binder.scheme.quantified ≠ []
  binder_well_formed : BinderWellFormed function.definitionContext
    function.source.owner function.binder
  requirements_well_formed : LocalSchemeRequirementsWellFormed
    function.definitionContext function.binder
  generalizes : SchemeGeneralizesExcept function.definitionContext
    (localSchemeTemplateIds function.binder) function.binder.scheme
  graph : OccurrenceGraphWellFormed function.source
  occurrence :
    ∃ node,
      ContainsExpression function.source function.initializer node ∧
      node.form = .lambda function.parameters function.resultType
        function.body ∧
      node.rawType = function.binder.scheme.body ∧
      node.type = function.binder.scheme.body ∧
      node.requirements = [] ∧
      node.coercions = [] ∧
      ExpressionFormHasRawType function.source
        (localSchemeInitializerContext function.definitionContext
          function.binder)
        node.form function.binder.scheme.body (.ordinary [])

/-- Exact agreement between a lexical type scope, its location environment,
and the declared types of those locations.  Initialized values are checked by
`HeapWellTyped`; keeping the two concerns separate permits cyclic closures. -/
inductive EnvironmentAgrees (heap : Heap) :
    Resolved.LocalScope Scheme → Environment → Prop where
  | nil : EnvironmentAgrees heap [] []
  | cons
      {scope : Resolved.LocalScope Scheme} {environment : Environment}
      {id : Resolved.LocalId} {scheme : Scheme} {location : Location}
      {cell : Cell}
      (read : Heap.Reads heap location cell)
      (cell_type : cell.type = scheme.body)
      (monomorphic : scheme.quantified = [])
      (tail : EnvironmentAgrees heap scope environment) :
      EnvironmentAgrees heap ((id, scheme) :: scope)
        ((id, location) :: environment)

/-- A stored generalized closure has valid principal code and its captured
locations agree with the lexical scope of its definition.  The ambient heap
context contributes only the whole-program signature catalog: cells remain in
the global heap while evaluation crosses function contexts. -/
structure GeneralizedClosureWellTyped (context : Context) (heap : Heap)
    (function : GeneralizedClosure) : Prop where
  same_signatures :
    function.definitionContext.signatures = context.signatures
  code : GeneralizedClosureCodeValid function
  captures : EnvironmentAgrees heap function.definitionContext.locals
    function.captured

mutual

  /-- Mathematical source values have source types independently of any
  executable type projection or evaluator result. -/
  inductive ValueHasType (context : Context) (heap : Heap) : Value → Ty → Prop where
    | unit : ValueHasType context heap .unit .unit
    | bool (value : Bool) : ValueHasType context heap (.bool value) .bool
    | word (value : Core.Word) : ValueHasType context heap (.word value) .word
    | integer (value : Int) : ValueHasType context heap (.integer value) .integer
    | product
        {left right : Value} {leftType rightType : Ty}
        (left_typed : ValueHasType context heap left leftType)
        (right_typed : ValueHasType context heap right rightType) :
        ValueHasType context heap (.product left right)
          (.product leftType rightType)
    | proxy (inner : Ty) :
        ValueHasType context heap (.proxy inner) (.proxy inner)
    | constructed
        {instantiation : DataConstructorInstantiation}
        {arguments : List Value}
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (arguments_typed :
          ValuesHaveTypes context heap arguments instantiation.payloadTypes) :
        ValueHasType context heap (.constructed instantiation arguments)
          instantiation.resultType
    | mapping
        {keyType valueType : Ty} {entries : List (Value × Value)}
        (entries_typed :
          MappingEntriesHaveTypes context heap entries keyType valueType) :
        ValueHasType context heap (.mapping keyType valueType entries)
          (.mapping keyType valueType)
    | closure
        {function : Closure}
        (same_signatures : function.context.signatures = context.signatures)
        (code : ClosureCodeValid function.context function)
        (evidence_covers : function.evidence.Covers function.context)
        (captures :
          EnvironmentAgrees heap function.context.locals function.captured) :
        ValueHasType context heap (.closure function)
          (.function
            (Ty.productMany
              (function.parameters.map (fun binder => binder.scheme.body)))
            function.resultType)
    | global
        {function : GlobalFunction}
        (valid : DeclarationInstantiation.Valid context function.instantiation)
        (evidence_covers : function.evidence.Covers
          ((Context.ofSignatures context.signatures).withAssumptions
            function.instantiation.predicates)) :
        ValueHasType context heap (.global function) function.instantiation.type
    | builtin (function : BuiltinFunction) :
        ValueHasType context heap (.builtin function) function.id.type
    | comptime
        {value : Value} {inner : Ty}
        (inner_typed : ValueHasType context heap value inner) :
        ValueHasType context heap value (.comptime inner)

  /-- Pointwise typing for constructor payloads and other fixed-shape value
  sequences. -/
  inductive ValuesHaveTypes (context : Context) (heap : Heap) :
      List Value → List Ty → Prop where
    | nil : ValuesHaveTypes context heap [] []
    | cons
        {value : Value} {values : List Value} {type : Ty} {types : List Ty}
        (head : ValueHasType context heap value type)
        (tail : ValuesHaveTypes context heap values types) :
        ValuesHaveTypes context heap (value :: values) (type :: types)

  /-- Every mathematical mapping entry has the mapping's declared key and
  value type. -/
  inductive MappingEntriesHaveTypes (context : Context) (heap : Heap) :
      List (Value × Value) → Ty → Ty → Prop where
    | nil (keyType valueType : Ty) :
        MappingEntriesHaveTypes context heap [] keyType valueType
    | cons
        {key value : Value} {entries : List (Value × Value)}
        {keyType valueType : Ty}
        (key_typed : ValueHasType context heap key keyType)
        (value_typed : ValueHasType context heap value valueType)
        (tail : MappingEntriesHaveTypes context heap entries keyType valueType) :
        MappingEntriesHaveTypes context heap ((key, value) :: entries)
          keyType valueType

end

/-- Source-ordered binder/value pairs agree with every binder's monomorphic
runtime body type in one heap world. -/
inductive BindingValuesHaveTypes (context : Context) (heap : Heap) :
    List (TypedBinder × Value) → Prop where
  | nil : BindingValuesHaveTypes context heap []
  | cons
      {binder : TypedBinder} {value : Value}
      {bindings : List (TypedBinder × Value)}
      (head : ValueHasType context heap value binder.scheme.body)
      (tail : BindingValuesHaveTypes context heap bindings) :
      BindingValuesHaveTypes context heap ((binder, value) :: bindings)

/-- Positive structural weight for source types, used only to justify
heap-world transport over the mutually inductive typing judgments. -/
def typeWeight : Ty → Nat
  | .variable _ | .parameter _ | .constructor _ | .error => 1
  | .application left right | .function left right | .product left right
  | .mapping left right => typeWeight left + typeWeight right + 1
  | .proxy inner | .comptime inner => typeWeight inner + 1

def typesWeight : List Ty → Nat
  | [] => 0
  | type :: types => typeWeight type + typesWeight types + 1

mutual

  /-- Structural weight which counts every recursively contained value and
  the type metadata that a value-typing derivation may traverse. -/
  def valueWeight : Value → Nat
    | .unit | .bool _ | .word _ | .integer _ | .proxy _
    | .closure _ | .global _ | .builtin _ => 1
    | .product left right => valueWeight left + valueWeight right + 1
    | .constructed instantiation arguments =>
        valuesWeight arguments + typesWeight instantiation.payloadTypes + 1
    | .mapping keyType valueType entries =>
        mappingEntriesWeight entries + typeWeight keyType + typeWeight valueType + 1

  def valuesWeight : List Value → Nat
    | [] => 0
    | value :: values => valueWeight value + valuesWeight values + 1

  def mappingEntriesWeight : List (Value × Value) → Nat
    | [] => 0
    | (key, value) :: entries =>
        valueWeight key + valueWeight value + mappingEntriesWeight entries + 1

end

/-- An absent cell value is valid at every retained type; an initialized cell
must contain a value of that exact type. -/
inductive OptionalValueHasType (context : Context) (heap : Heap) :
    Option Value → Ty → Prop where
  | none (type : Ty) : OptionalValueHasType context heap none type
  | some {value : Value} {type : Ty}
      (typed : ValueHasType context heap value type) :
      OptionalValueHasType context heap (some value) type

/-- Optional generalized-cell metadata agrees with the cell's principal type.
The `none` case covers every ordinary mutable cell. -/
inductive OptionalGeneralizedClosureWellTyped
    (context : Context) (heap : Heap) :
    Option GeneralizedClosure → Ty → Prop where
  | none (type : Ty) :
      OptionalGeneralizedClosureWellTyped context heap none type
  | some {function : GeneralizedClosure}
      (typed : GeneralizedClosureWellTyped context heap function) :
      OptionalGeneralizedClosureWellTyped context heap (some function)
        function.binder.scheme.body

/-- One cell agrees with its retained annotation in the current heap world. -/
structure CellWellTyped (context : Context) (heap : Heap) (cell : Cell) : Prop where
  value : OptionalValueHasType context heap cell.value cell.type
  generalized : OptionalGeneralizedClosureWellTyped context heap
    cell.generalized cell.type

/-- Every cell is deeply typed in the same heap world. -/
def HeapWellTyped (context : Context) (heap : Heap) : Prop :=
  ∀ cell, cell ∈ heap.cells → CellWellTyped context heap cell

/-- A later heap preserves every old location and its declared type.  Cell
values may change. -/
def HeapTypesExtend (before after : Heap) : Prop :=
  ∀ location cell, Heap.Reads before location cell →
    ∃ updatedCell,
      Heap.Reads after location updatedCell ∧ updatedCell.type = cell.type

namespace HeapMetadataExtend

/-- Forget generalized-cell metadata preservation while retaining the type
extension interface consumed by existing value-typing proofs. -/
theorem toTypes {before after : Heap}
    (extension : HeapMetadataExtend before after) :
    HeapTypesExtend before after := by
  intro location cell read
  rcases extension location cell read with
    ⟨updatedCell, updatedRead, updatedType, _⟩
  exact ⟨updatedCell, updatedRead, updatedType⟩

end HeapMetadataExtend

/-- A directional inclusion between the type worlds of two source contexts.
Lexical locals, trait assumptions, and solved requirements are deliberately
absent.  Closed declaration and constructor instances depend on the catalog
and rigid parameters; symbolic closures and proxies may additionally retain
lexical or body-wide residual inference variables. -/
structure TypeContextSupports (source target : Context) : Prop where
  signatures : target.signatures = source.signatures
  parameters : ∀ parameter, parameter ∈ source.typeParameters →
    parameter ∈ target.typeParameters
  parameterOwners : ∀ parameter, parameter ∈ source.typeParameters →
    target.currentDeclaration = some parameter.owner
  variables : ∀ metavariable, metavariable ∈ source.typeVariables →
    metavariable ∈ target.typeVariables
  residualVariables : source.residualTypeVariables = true →
    target.residualTypeVariables = true
  targetBinders : TypeParameterBindersWellFormed target

namespace TypeContextSupports

/-- Runtime contexts with the same declaration catalog support transport when
the source has no lexical flexible variables, both sides are closed with
respect to rigid declaration parameters, and the target admits residual
inference variables.  This is the cross-function runtime case after structural
generic instantiation. -/
theorem ofClosed
    {source target : Context}
    (signatures : target.signatures = source.signatures)
    (sourceClosed : source.typeParameters = [])
    (targetClosed : target.typeParameters = [])
    (sourceVariablesClosed : source.typeVariables = [])
    (targetResidualVariablesOpen : target.residualTypeVariables = true) :
    TypeContextSupports source target := by
  refine {
    signatures
    parameters := ?_
    parameterOwners := ?_
    variables := ?_
    residualVariables := ?_
    targetBinders := ?_
  }
  · intro parameter member
    simp [sourceClosed] at member
  · intro parameter member
    simp [sourceClosed] at member
  · intro metavariable member
    simp [sourceVariablesClosed] at member
  · intro sourceOpen
    exact targetResidualVariablesOpen
  · constructor
    · simp [targetClosed]
    · intro parameter member
      simp [targetClosed] at member

/-- Adding one lexical binder leaves the source type world unchanged. -/
theorem ofBinderExtendsForward
    {owner : Resolved.DeclarationId} {source target : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner source binder target) :
    TypeContextSupports source target := by
  cases extension with
  | intro wellFormed fresh =>
      exact {
        signatures := rfl
        parameters := fun _ member => member
        parameterOwners := fun parameter member =>
          wellFormed.scheme.binders.2 parameter member
        variables := fun _ member => member
        residualVariables := fun sourceOpen => sourceOpen
        targetBinders := wellFormed.scheme.binders
      }

/-- Removing the most recent lexical binder also leaves the source type world
unchanged. -/
theorem ofBinderExtendsBackward
    {owner : Resolved.DeclarationId} {source target : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner source binder target) :
    TypeContextSupports target source := by
  cases extension with
  | intro wellFormed fresh =>
      exact {
        signatures := rfl
        parameters := fun _ member => member
        parameterOwners := fun parameter member =>
          wellFormed.scheme.binders.2 parameter member
        variables := fun _ member => member
        residualVariables := fun sourceOpen => sourceOpen
        targetBinders := wellFormed.scheme.binders
      }

/-- Every flexible variable admitted by the source occurrence scope is also
admitted by a supporting target context. -/
theorem admissibleVariables
    {source target : Context} (supports : TypeContextSupports source target)
    {type : Ty} {metavariable : TypeVarId}
    (member : metavariable ∈ admissibleTypeVariables source type) :
    metavariable ∈ admissibleTypeVariables target type := by
  cases sourceOpen : source.residualTypeVariables with
  | false =>
      have sourceMember : metavariable ∈ source.typeVariables := by
        simpa [admissibleTypeVariables, sourceOpen] using member
      exact List.mem_append_left _
        (supports.variables metavariable sourceMember)
  | true =>
      have targetOpen := supports.residualVariables sourceOpen
      simp only [admissibleTypeVariables, sourceOpen, ↓reduceIte, targetOpen,
        List.mem_append] at member ⊢
      exact member.elim (fun sourceMember =>
        .inl (supports.variables metavariable sourceMember)) .inr

end TypeContextSupports

/-- Well-scoped types can be moved into any context which supports their
catalog and rigid binders. -/
theorem TypeWellScoped.transportContext
    {source target : Context} {flexible : List TypeVarId} {type : Ty}
    (supports : TypeContextSupports source target)
    (wellScoped : TypeWellScoped source flexible type) :
    TypeWellScoped target flexible type := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexible type)
    (motive_2 := fun types _ => TypesWellScoped target flexible types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound owned
    exact .parameter (supports.parameters parameter bound)
      (supports.parameterOwners parameter bound)
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [supports.signatures] using cataloged) arity
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

theorem TypesWellScoped.transportContext
    {source target : Context} {flexible : List TypeVarId} {types : List Ty}
    (supports : TypeContextSupports source target)
    (wellScoped : TypesWellScoped source flexible types) :
    TypesWellScoped target flexible types := by
  refine TypesWellScoped.rec
    (motive_1 := fun type _ => TypeWellScoped target flexible type)
    (motive_2 := fun types _ => TypesWellScoped target flexible types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ wellScoped
  · intro metavariable bound
    exact .variable bound
  · intro parameter bound owned
    exact .parameter (supports.parameters parameter bound)
      (supports.parameterOwners parameter bound)
  · intro builtin
    exact .builtin builtin
  · intro dataType arguments cataloged arity _ argumentsInduction
    exact .nominal dataType arguments
      (by simpa [supports.signatures] using cataloged) arity
      argumentsInduction
  · intro parameter result _ _ parameterInduction resultInduction
    exact .function parameterInduction resultInduction
  · intro left right _ _ leftInduction rightInduction
    exact .product leftInduction rightInduction
  · intro key value _ _ keyInduction valueInduction
    exact .mapping keyInduction valueInduction
  · intro inner _ innerInduction
    exact .proxy innerInduction
  · intro inner _ innerInduction
    exact .comptime innerInduction
  · exact .nil
  · intro head tail _ _ headInduction tailInduction
    exact .cons headInduction tailInduction

namespace TypeWellFormed

theorem transportContext
    {source target : Context} {type : Ty}
    (supports : TypeContextSupports source target)
    (wellFormed : TypeWellFormed source type) :
    TypeWellFormed target type := {
  binders := supports.targetBinders
  typeWellScoped := TypeWellScoped.transportContext supports
    wellFormed.typeWellScoped
}

end TypeWellFormed

namespace TypeAdmissible

/-- Occurrence types, including residual symbolic types, transport only to a
context which supports their complete flexible-variable scope. -/
theorem transportContext
    {source target : Context} {type : Ty}
    (supports : TypeContextSupports source target)
    (admissible : TypeAdmissible source type) :
    TypeAdmissible target type := {
  binders := supports.targetBinders
  typeWellScoped := TypeWellScoped.weakenTo
    (fun _ member => supports.admissibleVariables member)
    (TypeWellScoped.transportContext supports admissible.typeWellScoped)
}

end TypeAdmissible

namespace DeclarationInstantiation.Valid

theorem transportContext
    {source target : Context}
    {instantiation : DeclarationInstantiation}
    (supports : TypeContextSupports source target)
    (valid : DeclarationInstantiation.Valid source instantiation) :
    DeclarationInstantiation.Valid target instantiation := by
  cases valid with
  | intro signature signature_mem declaration_eq substitution_exact
      substitution_range type_eq predicates_eq parameterComptime_eq
      returnComptime_eq =>
      exact .intro signature
        (by simpa [supports.signatures] using signature_mem)
        declaration_eq substitution_exact
        (fun parameter replacement member =>
          TypeWellFormed.transportContext supports
            (substitution_range parameter replacement member))
        type_eq predicates_eq parameterComptime_eq returnComptime_eq

end DeclarationInstantiation.Valid

namespace DataConstructorInstantiation.Valid

theorem transportContext
    {source target : Context}
    {instantiation : DataConstructorInstantiation}
    (supports : TypeContextSupports source target)
    (valid : DataConstructorInstantiation.Valid source instantiation) :
    DataConstructorInstantiation.Valid target instantiation := by
  cases valid with
  | intro dataType signature dataType_mem signature_mem signature_owner
      constructor_eq substitution_exact substitution_range payloadTypes_eq
      resultType_eq =>
      exact .intro dataType signature
        (by simpa [supports.signatures] using dataType_mem)
        signature_mem signature_owner constructor_eq substitution_exact
        (fun parameter replacement member =>
          TypeWellFormed.transportContext supports
            (substitution_range parameter replacement member))
        payloadTypes_eq resultType_eq

end DataConstructorInstantiation.Valid

namespace EnvironmentAgrees

/-- Agreement exposes a readable cell for every first-match lexical lookup. -/
theorem lookup
    {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : Environment}
    (agrees : EnvironmentAgrees heap scope environment)
    {id : Resolved.LocalId} {scheme : Scheme}
    (staticLookup : Resolved.LocalScope.Lookup scope id scheme) :
    ∃ location cell,
      Environment.LooksUp environment id location ∧
      Heap.Reads heap location cell ∧
      cell.type = scheme.body := by
  induction agrees with
  | nil => cases staticLookup
  | @cons scope environment headId headScheme location cell read cell_type
      monomorphic tail ih =>
      cases staticLookup with
      | head => exact ⟨location, cell, .head, read, cell_type⟩
      | tail different found =>
          rcases ih found with ⟨foundLocation, foundCell, envLookup, heapRead, typeEq⟩
          exact ⟨foundLocation, foundCell, .tail different envLookup, heapRead, typeEq⟩

/-- Every reachable runtime local is backed by a monomorphic lexical scheme. -/
theorem lookup_monomorphic
    {heap : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : Environment}
    (agrees : EnvironmentAgrees heap scope environment)
    {id : Resolved.LocalId} {scheme : Scheme}
    (staticLookup : Resolved.LocalScope.Lookup scope id scheme) :
    scheme.quantified = [] := by
  induction agrees with
  | nil => cases staticLookup
  | cons _ _ monomorphic _ inductionHypothesis =>
      cases staticLookup with
      | head => exact monomorphic
      | tail _ found => exact inductionHypothesis found

/-- Preserving location types preserves lexical/heap agreement. -/
theorem mono
    {before after : Heap} {scope : Resolved.LocalScope Scheme}
    {environment : Environment}
    (extension : HeapTypesExtend before after)
    (agrees : EnvironmentAgrees before scope environment) :
    EnvironmentAgrees after scope environment := by
  induction agrees with
  | nil => exact .nil
  | cons read cell_type monomorphic _ ih =>
      rcases extension _ _ read with ⟨updatedCell, updatedRead, updatedType⟩
      exact .cons updatedRead (updatedType.trans cell_type) monomorphic ih

end EnvironmentAgrees

namespace HeapTypesExtend

theorem refl (heap : Heap) : HeapTypesExtend heap heap := by
  intro location cell read
  exact ⟨cell, read, rfl⟩

theorem trans {first middle last : Heap}
    (left : HeapTypesExtend first middle)
    (right : HeapTypesExtend middle last) :
    HeapTypesExtend first last := by
  intro location cell read
  rcases left location cell read with ⟨middleCell, middleRead, middleType⟩
  rcases right location middleCell middleRead with
    ⟨lastCell, lastRead, lastType⟩
  exact ⟨lastCell, lastRead, lastType.trans middleType⟩

theorem of_allocation
    {before after : Heap} {type : Ty} {value : Option Value}
    {location : Location}
    (allocation : Heap.Allocates before type value location after) :
    HeapTypesExtend before after := by
  intro oldLocation cell read
  exact ⟨cell, allocation.preserves_read read, rfl⟩

theorem of_generalized_allocation
    {before after : Heap} {function : GeneralizedClosure}
    {location : Location}
    (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapTypesExtend before after :=
  (HeapMetadataExtend.of_generalized_allocation allocation).toTypes

theorem of_write
    {before after : Heap} {writtenLocation : Location}
    {value : Option Value}
    (write : Heap.Writes before writtenLocation value after) :
    HeapTypesExtend before after := by
  intro location cell read
  by_cases same : location = writtenLocation
  · subst location
    rcases write.reads_updated with ⟨previous, previousRead, updatedRead⟩
    have cell_eq : cell = previous := read.functional previousRead
    subst cell
    exact ⟨{ previous with value := value }, updatedRead, rfl⟩
  · exact ⟨cell, write.preserves_other same read, rfl⟩

end HeapTypesExtend

namespace GeneralizedClosureWellTyped

/-- Principal closure typing is stable under a supported change of the
ambient static type world.  Its definition context and captured scope remain
unchanged. -/
theorem transportContext
    {source target : Context} {heap : Heap}
    {function : GeneralizedClosure}
    (supports : TypeContextSupports source target)
    (typed : GeneralizedClosureWellTyped source heap function) :
    GeneralizedClosureWellTyped target heap function := {
  same_signatures := typed.same_signatures.trans supports.signatures.symm
  code := typed.code
  captures := typed.captures
}

/-- Generalized closure typing depends on captured cell types, so it is
monotone under the same heap extension as ordinary closure typing. -/
theorem mono
    {context : Context} {before after : Heap}
    {function : GeneralizedClosure}
    (extension : HeapTypesExtend before after)
    (typed : GeneralizedClosureWellTyped context before function) :
    GeneralizedClosureWellTyped context after function := {
  same_signatures := typed.same_signatures
  code := typed.code
  captures := typed.captures.mono extension
}

end GeneralizedClosureWellTyped

mutual

  /-- Value typing depends only on retained cell types, so it is monotone under
  a heap extension which preserves those types. -/
  theorem ValueHasType.mono
      {context : Context} {before after : Heap} {value : Value} {type : Ty}
      (extension : HeapTypesExtend before after)
      (typed : ValueHasType context before value type) :
      ValueHasType context after value type := by
    cases typed with
    | unit => exact .unit
    | bool value => exact .bool value
    | word value => exact .word value
    | integer value => exact .integer value
    | product left_typed right_typed =>
        exact .product (ValueHasType.mono extension left_typed)
          (ValueHasType.mono extension right_typed)
    | proxy inner => exact .proxy inner
    | constructed valid arguments_typed =>
        exact .constructed valid (ValuesHaveTypes.mono extension arguments_typed)
    | mapping entries_typed =>
        exact .mapping (MappingEntriesHaveTypes.mono extension entries_typed)
    | closure same_signatures code evidence_covers captures =>
        exact .closure same_signatures code evidence_covers
          (captures.mono extension)
    | global valid evidence_covers => exact .global valid evidence_covers
    | builtin function => exact .builtin function
    | comptime inner_typed =>
        exact .comptime (ValueHasType.mono extension inner_typed)
    termination_by valueWeight value + typeWeight type
    decreasing_by
      all_goals
        simp_all [valueWeight, typeWeight] <;> omega

  theorem ValuesHaveTypes.mono
      {context : Context} {before after : Heap}
      {values : List Value} {types : List Ty}
      (extension : HeapTypesExtend before after)
      (typed : ValuesHaveTypes context before values types) :
      ValuesHaveTypes context after values types := by
    cases typed with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (ValueHasType.mono extension head)
          (ValuesHaveTypes.mono extension tail)
    termination_by valuesWeight values + typesWeight types
    decreasing_by
      all_goals
        simp_all [valuesWeight, typesWeight] <;> omega

  theorem MappingEntriesHaveTypes.mono
      {context : Context} {before after : Heap}
      {entries : List (Value × Value)} {keyType valueType : Ty}
      (extension : HeapTypesExtend before after)
      (typed : MappingEntriesHaveTypes context before entries keyType valueType) :
      MappingEntriesHaveTypes context after entries keyType valueType := by
    cases typed with
    | nil keyType valueType => exact .nil keyType valueType
    | cons key_typed value_typed tail =>
        exact .cons (ValueHasType.mono extension key_typed)
          (ValueHasType.mono extension value_typed)
          (MappingEntriesHaveTypes.mono extension tail)
    termination_by
      mappingEntriesWeight entries + typeWeight keyType + typeWeight valueType
    decreasing_by
      all_goals
        simp_all [mappingEntriesWeight] <;> omega

end

mutual

  /-- Deep value typing is invariant under a supported change of static type
  context.  The heap itself is unchanged. -/
  theorem ValueHasType.transportContext
      {source target : Context} {heap : Heap} {value : Value} {type : Ty}
      (supports : TypeContextSupports source target)
      (typed : ValueHasType source heap value type) :
      ValueHasType target heap value type := by
    cases typed with
    | unit => exact .unit
    | bool value => exact .bool value
    | word value => exact .word value
    | integer value => exact .integer value
    | product left_typed right_typed =>
        exact .product
          (ValueHasType.transportContext supports left_typed)
          (ValueHasType.transportContext supports right_typed)
    | proxy inner => exact .proxy inner
    | constructed valid arguments_typed =>
        exact .constructed
          (DataConstructorInstantiation.Valid.transportContext supports valid)
          (ValuesHaveTypes.transportContext supports arguments_typed)
    | mapping entries_typed =>
        exact .mapping
          (MappingEntriesHaveTypes.transportContext supports entries_typed)
    | closure same_signatures code evidence_covers captures =>
        exact .closure (same_signatures.trans supports.signatures.symm) code
          evidence_covers captures
    | global valid evidence_covers =>
        exact .global
          (DeclarationInstantiation.Valid.transportContext supports valid)
          (by simpa [supports.signatures] using evidence_covers)
    | builtin function => exact .builtin function
    | comptime inner_typed =>
        exact .comptime (ValueHasType.transportContext supports inner_typed)
    termination_by valueWeight value + typeWeight type
    decreasing_by
      all_goals
        simp_all [valueWeight, typeWeight] <;> omega

  theorem ValuesHaveTypes.transportContext
      {source target : Context} {heap : Heap}
      {values : List Value} {types : List Ty}
      (supports : TypeContextSupports source target)
      (typed : ValuesHaveTypes source heap values types) :
      ValuesHaveTypes target heap values types := by
    cases typed with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (ValueHasType.transportContext supports head)
          (ValuesHaveTypes.transportContext supports tail)
    termination_by valuesWeight values + typesWeight types
    decreasing_by
      all_goals
        simp_all [valuesWeight, typesWeight] <;> omega

  theorem MappingEntriesHaveTypes.transportContext
      {source target : Context} {heap : Heap}
      {entries : List (Value × Value)} {keyType valueType : Ty}
      (supports : TypeContextSupports source target)
      (typed : MappingEntriesHaveTypes source heap entries keyType valueType) :
      MappingEntriesHaveTypes target heap entries keyType valueType := by
    cases typed with
    | nil keyType valueType => exact .nil keyType valueType
    | cons key_typed value_typed tail =>
        exact .cons
          (ValueHasType.transportContext supports key_typed)
          (ValueHasType.transportContext supports value_typed)
          (MappingEntriesHaveTypes.transportContext supports tail)
    termination_by
      mappingEntriesWeight entries + typeWeight keyType + typeWeight valueType
    decreasing_by
      all_goals
        simp_all [mappingEntriesWeight] <;> omega

end

namespace BindingValuesHaveTypes

theorem transportContext
    {source target : Context} {heap : Heap}
    {bindings : List (TypedBinder × Value)}
    (supports : TypeContextSupports source target)
    (typed : BindingValuesHaveTypes source heap bindings) :
    BindingValuesHaveTypes target heap bindings := by
  induction typed with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons (ValueHasType.transportContext supports head) induction

theorem transportClosed
    {source target : Context} {heap : Heap}
    {bindings : List (TypedBinder × Value)}
    (signatures : target.signatures = source.signatures)
    (sourceClosed : source.typeParameters = [])
    (targetClosed : target.typeParameters = [])
    (sourceVariablesClosed : source.typeVariables = [])
    (targetResidualVariablesOpen : target.residualTypeVariables = true)
    (typed : BindingValuesHaveTypes source heap bindings) :
    BindingValuesHaveTypes target heap bindings :=
  typed.transportContext
    (TypeContextSupports.ofClosed signatures sourceClosed targetClosed
      sourceVariablesClosed targetResidualVariablesOpen)

theorem mono
    {context : Context} {before after : Heap}
    {bindings : List (TypedBinder × Value)}
    (extension : HeapTypesExtend before after)
    (typed : BindingValuesHaveTypes context before bindings) :
    BindingValuesHaveTypes context after bindings := by
  induction typed with
  | nil => exact .nil
  | cons head _ induction => exact .cons (head.mono extension) induction

end BindingValuesHaveTypes

namespace OptionalValueHasType

theorem transportContext
    {source target : Context} {heap : Heap}
    {value : Option Value} {type : Ty}
    (supports : TypeContextSupports source target)
    (typed : OptionalValueHasType source heap value type) :
    OptionalValueHasType target heap value type := by
  cases typed with
  | none type => exact .none type
  | some typed =>
      exact .some (ValueHasType.transportContext supports typed)

theorem mono
    {context : Context} {before after : Heap}
    {value : Option Value} {type : Ty}
    (extension : HeapTypesExtend before after)
    (typed : OptionalValueHasType context before value type) :
    OptionalValueHasType context after value type := by
  cases typed with
  | none type => exact .none type
  | some typed => exact .some (typed.mono extension)

end OptionalValueHasType

namespace OptionalGeneralizedClosureWellTyped

theorem transportContext
    {source target : Context} {heap : Heap}
    {function : Option GeneralizedClosure} {type : Ty}
    (supports : TypeContextSupports source target)
    (typed : OptionalGeneralizedClosureWellTyped source heap function type) :
    OptionalGeneralizedClosureWellTyped target heap function type := by
  cases typed with
  | none type => exact .none type
  | some typed => exact .some (typed.transportContext supports)

theorem mono
    {context : Context} {before after : Heap}
    {function : Option GeneralizedClosure} {type : Ty}
    (extension : HeapTypesExtend before after)
    (typed : OptionalGeneralizedClosureWellTyped context before function type) :
    OptionalGeneralizedClosureWellTyped context after function type := by
  cases typed with
  | none type => exact .none type
  | some typed => exact .some (typed.mono extension)

/-- A present descriptor exposes both its principal cell type and its deep
typing witness. -/
theorem some_inv
    {context : Context} {heap : Heap}
    {function : GeneralizedClosure} {type : Ty}
    (typed : OptionalGeneralizedClosureWellTyped context heap
      (Option.some function) type) :
    type = function.binder.scheme.body ∧
      GeneralizedClosureWellTyped context heap function := by
  cases typed with
  | some functionTyped => exact ⟨rfl, functionTyped⟩

end OptionalGeneralizedClosureWellTyped

namespace CellWellTyped

theorem transportContext
    {source target : Context} {heap : Heap} {cell : Cell}
    (supports : TypeContextSupports source target)
    (typed : CellWellTyped source heap cell) :
    CellWellTyped target heap cell :=
  ⟨typed.value.transportContext supports,
    typed.generalized.transportContext supports⟩

theorem mono
    {context : Context} {before after : Heap} {cell : Cell}
    (extension : HeapTypesExtend before after)
    (typed : CellWellTyped context before cell) :
    CellWellTyped context after cell :=
  ⟨typed.value.mono extension, typed.generalized.mono extension⟩

/-- Reading present generalized metadata from a typed cell recovers its
principal type and deep descriptor typing. -/
theorem generalized_inv
    {context : Context} {heap : Heap} {cell : Cell}
    {function : GeneralizedClosure}
    (typed : CellWellTyped context heap cell)
    (present : cell.generalized = Option.some function) :
    cell.type = function.binder.scheme.body ∧
      GeneralizedClosureWellTyped context heap function := by
  have metadata : OptionalGeneralizedClosureWellTyped context heap
      (Option.some function) cell.type := by
    simpa [present] using typed.generalized
  exact metadata.some_inv

end CellWellTyped

namespace ValuesHaveTypes

theorem transportClosed
    {source target : Context} {heap : Heap}
    {values : List Value} {types : List Ty}
    (signatures : target.signatures = source.signatures)
    (sourceClosed : source.typeParameters = [])
    (targetClosed : target.typeParameters = [])
    (sourceVariablesClosed : source.typeVariables = [])
    (targetResidualVariablesOpen : target.residualTypeVariables = true)
    (typed : ValuesHaveTypes source heap values types) :
    ValuesHaveTypes target heap values types :=
  ValuesHaveTypes.transportContext
    (TypeContextSupports.ofClosed signatures sourceClosed targetClosed
      sourceVariablesClosed targetResidualVariablesOpen) typed

theorem length_eq
    {context : Context} {heap : Heap}
    {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes context heap values types) :
    values.length = types.length := by
  cases typed with
  | nil => rfl
  | cons _ tail => simp [length_eq tail]

theorem member
    {context : Context} {heap : Heap}
    {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes context heap values types)
    {index : Nat} {value : Value} {type : Ty}
    (value_at : values[index]? = some value)
    (type_at : types[index]? = some type) :
    ValueHasType context heap value type := by
  cases typed with
  | nil => simp at value_at
  | cons head tail =>
      cases index with
      | zero =>
          simp at value_at type_at
          subst value
          subst type
          exact head
      | succ index =>
          simp only [List.getElem?_cons_succ] at value_at type_at
          exact member tail value_at type_at

end ValuesHaveTypes

namespace ValueHasType

theorem transportClosed
    {source target : Context} {heap : Heap} {value : Value} {type : Ty}
    (signatures : target.signatures = source.signatures)
    (sourceClosed : source.typeParameters = [])
    (targetClosed : target.typeParameters = [])
    (sourceVariablesClosed : source.typeVariables = [])
    (targetResidualVariablesOpen : target.residualTypeVariables = true)
    (typed : ValueHasType source heap value type) :
    ValueHasType target heap value type :=
  ValueHasType.transportContext
    (TypeContextSupports.ofClosed signatures sourceClosed targetClosed
      sourceVariablesClosed targetResidualVariablesOpen) typed

theorem iff_of_binderExtends
    {owner : Resolved.DeclarationId} {source target : Context}
    {binder : TypedBinder} {heap : Heap} {value : Value} {type : Ty}
    (extension : BinderExtends owner source binder target) :
    ValueHasType source heap value type ↔
      ValueHasType target heap value type := by
  constructor
  · exact ValueHasType.transportContext
      (TypeContextSupports.ofBinderExtendsForward extension)
  · exact ValueHasType.transportContext
      (TypeContextSupports.ofBinderExtendsBackward extension)

theorem product_inv
    {context : Context} {heap : Heap}
    {left right : Value} {leftType rightType : Ty}
    (typed : ValueHasType context heap (.product left right)
      (.product leftType rightType)) :
    ValueHasType context heap left leftType ∧
      ValueHasType context heap right rightType := by
  cases typed with
  | product left_typed right_typed => exact ⟨left_typed, right_typed⟩

theorem constructed_inv
    {context : Context} {heap : Heap}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Value} {type : Ty}
    (typed : ValueHasType context heap
      (.constructed instantiation arguments) type) :
    (type = instantiation.resultType ∧
      DataConstructorInstantiation.Valid context instantiation ∧
      ValuesHaveTypes context heap arguments instantiation.payloadTypes) ∨
    (∃ inner, type = .comptime inner ∧
      ValueHasType context heap (.constructed instantiation arguments) inner) := by
  cases typed with
  | constructed valid arguments_typed =>
      exact .inl ⟨rfl, valid, arguments_typed⟩
  | comptime inner_typed => exact .inr ⟨_, rfl, inner_typed⟩

theorem mapping_inv
    {context : Context} {heap : Heap}
    {keyType valueType : Ty} {entries : List (Value × Value)}
    {type : Ty}
    (typed : ValueHasType context heap
      (.mapping keyType valueType entries) type) :
    type = .mapping keyType valueType ∨
      ∃ inner, type = .comptime inner ∧
        ValueHasType context heap (.mapping keyType valueType entries) inner := by
  cases typed with
  | mapping _ => exact .inl rfl
  | comptime inner_typed => exact .inr ⟨_, rfl, inner_typed⟩

theorem closure_inv
    {context : Context} {heap : Heap}
    {function : Closure} {type : Ty}
    (typed : ValueHasType context heap (.closure function) type) :
    (type = .function
        (Ty.productMany
          (function.parameters.map (fun binder => binder.scheme.body)))
        function.resultType ∧
      function.context.signatures = context.signatures ∧
      ClosureCodeValid function.context function ∧
      function.evidence.Covers function.context ∧
      EnvironmentAgrees heap function.context.locals function.captured) ∨
    (∃ inner, type = .comptime inner ∧
      ValueHasType context heap (.closure function) inner) := by
  cases typed with
  | closure same_signatures code evidence_covers captures =>
      exact .inl ⟨rfl, same_signatures, code, evidence_covers, captures⟩
  | comptime inner_typed => exact .inr ⟨_, rfl, inner_typed⟩

/-- At its ordinary function type a closure exposes exact code provenance and
capture agreement; a staging wrapper cannot inhabit this outer type. -/
theorem closure_function_inv
    {context : Context} {heap : Heap} {function : Closure}
    {parameter result : Ty}
    (typed : ValueHasType context heap (.closure function)
      (.function parameter result)) :
    parameter = Ty.productMany
        (function.parameters.map (fun binder => binder.scheme.body)) ∧
      result = function.resultType ∧
      function.context.signatures = context.signatures ∧
      ClosureCodeValid function.context function ∧
      function.evidence.Covers function.context ∧
      EnvironmentAgrees heap function.context.locals function.captured := by
  cases typed with
  | closure same_signatures code evidence_covers captures =>
      exact ⟨rfl, rfl, same_signatures, code, evidence_covers, captures⟩

/-- Mapping values expose the typing of every retained entry. -/
theorem mapping_exact_inv
    {context : Context} {heap : Heap}
    {keyType valueType : Ty} {entries : List (Value × Value)}
    (typed : ValueHasType context heap (.mapping keyType valueType entries)
      (.mapping keyType valueType)) :
    MappingEntriesHaveTypes context heap entries keyType valueType := by
  cases typed with
  | mapping entries_typed => exact entries_typed

theorem global_inv
    {context : Context} {heap : Heap}
    {function : GlobalFunction} {type : Ty}
    (typed : ValueHasType context heap (.global function) type) :
    (type = function.instantiation.type ∧
      DeclarationInstantiation.Valid context function.instantiation ∧
      function.evidence.Covers
        ((Context.ofSignatures context.signatures).withAssumptions
          function.instantiation.predicates)) ∨
    (∃ inner, type = .comptime inner ∧
      ValueHasType context heap (.global function) inner) := by
  cases typed with
  | global valid evidence_covers =>
      exact .inl ⟨rfl, valid, evidence_covers⟩
  | comptime inner_typed => exact .inr ⟨_, rfl, inner_typed⟩

theorem builtin_inv
    {context : Context} {heap : Heap}
    {function : BuiltinFunction} {type : Ty}
    (typed : ValueHasType context heap (.builtin function) type) :
    type = function.id.type ∨
      (∃ inner, type = .comptime inner ∧
        ValueHasType context heap (.builtin function) inner) := by
  cases typed with
  | builtin function => exact .inl rfl
  | comptime inner_typed => exact .inr ⟨_, rfl, inner_typed⟩

end ValueHasType

namespace Heap.CellsWrite

/-- Every cell in a written list is either the replacement or an old cell. -/
theorem member_updated
    {cells updated : List Cell} {index : Nat} {replacement selected : Cell}
    (write : CellsWrite cells index replacement updated)
    (member : selected ∈ updated) :
    selected = replacement ∨ selected ∈ cells := by
  induction write with
  | head =>
      simp only [List.mem_cons] at member ⊢
      rcases member with equal | old
      · exact .inl equal
      · exact .inr (.inr old)
  | tail write ih =>
      simp only [List.mem_cons] at member ⊢
      rcases member with head | tailMember
      · exact .inr (.inl head)
      · rcases ih tailMember with replacement | old
        · exact .inl replacement
        · exact .inr (.inr old)

end Heap.CellsWrite

namespace HeapWellTyped

private theorem cellAt_mem
    {cells : List Cell} {index : Nat} {cell : Cell}
    (selected : Heap.CellAt cells index cell) : cell ∈ cells := by
  induction selected with
  | head => simp
  | tail _ induction => exact List.mem_cons_of_mem _ induction

private theorem read_mem
    {heap : Heap} {location : Location} {cell : Cell}
    (read : Heap.Reads heap location cell) : cell ∈ heap.cells := by
  cases read with
  | intro selected =>
      exact cellAt_mem selected

theorem transportContext
    {source target : Context} {heap : Heap}
    (supports : TypeContextSupports source target)
    (typed : HeapWellTyped source heap) :
    HeapWellTyped target heap := by
  intro cell member
  exact (typed cell member).transportContext supports

theorem transportClosed
    {source target : Context} {heap : Heap}
    (signatures : target.signatures = source.signatures)
    (sourceClosed : source.typeParameters = [])
    (targetClosed : target.typeParameters = [])
    (sourceVariablesClosed : source.typeVariables = [])
    (targetResidualVariablesOpen : target.residualTypeVariables = true)
    (typed : HeapWellTyped source heap) :
    HeapWellTyped target heap :=
  typed.transportContext
    (TypeContextSupports.ofClosed signatures sourceClosed targetClosed
      sourceVariablesClosed targetResidualVariablesOpen)

theorem iff_of_binderExtends
    {owner : Resolved.DeclarationId} {source target : Context}
    {binder : TypedBinder} {heap : Heap}
    (extension : BinderExtends owner source binder target) :
    HeapWellTyped source heap ↔ HeapWellTyped target heap := by
  constructor
  · exact transportContext
      (TypeContextSupports.ofBinderExtendsForward extension)
  · exact transportContext
      (TypeContextSupports.ofBinderExtendsBackward extension)

/-- A fresh allocation preserves deep heap typing. -/
theorem allocate
    {context : Context} {before after : Heap}
    {location : Location} {type : Ty} {value : Option Value}
    (heap_typed : HeapWellTyped context before)
    (value_typed : OptionalValueHasType context before value type)
    (allocation : Heap.Allocates before type value location after) :
    HeapWellTyped context after := by
  have extension := HeapTypesExtend.of_allocation allocation
  cases allocation
  intro cell member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with old | fresh
  · exact (heap_typed cell old).mono extension
  · subst cell
    exact ⟨value_typed.mono extension, .none type⟩

/-- Allocating a typed principal generalized closure preserves deep heap
typing.  The new cell has no ordinary value and retains the scheme body as its
principal type. -/
theorem allocateGeneralized
    {context : Context} {before after : Heap}
    {location : Location} {function : GeneralizedClosure}
    (heap_typed : HeapWellTyped context before)
    (function_typed : GeneralizedClosureWellTyped context before function)
    (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapWellTyped context after := by
  have extension := HeapTypesExtend.of_generalized_allocation allocation
  cases allocation
  intro cell member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with old | fresh
  · exact (heap_typed cell old).mono extension
  · subst cell
    exact ⟨.none _, .some (function_typed.mono extension)⟩

/-- Replacing one cell by a value of its retained type preserves deep heap
typing. -/
theorem write
    {context : Context} {before after : Heap}
    {location : Location} {value : Option Value} {previous : Cell}
    (heap_typed : HeapWellTyped context before)
    (read : Heap.Reads before location previous)
    (value_typed : OptionalValueHasType context before value previous.type)
    (write : Heap.Writes before location value after) :
    HeapWellTyped context after := by
  have extension := HeapTypesExtend.of_write write
  cases write with
  | @intro writePrevious updatedCells writeRead cellsWrite =>
      have previous_eq : previous = writePrevious := read.functional writeRead
      have replacement_typed :
          OptionalValueHasType context before value writePrevious.type := by
        simpa [previous_eq] using value_typed
      intro cell member
      by_cases replacement : cell = { writePrevious with value := value }
      · subst cell
        exact ⟨replacement_typed.mono extension,
          (heap_typed writePrevious (read_mem writeRead)).generalized.mono
            extension⟩
      · rcases cellsWrite.member_updated member with same | oldMember
        · exact (replacement same).elim
        · exact (heap_typed cell oldMember).mono extension

/-- Allocating a typed source-ordered binding vector preserves the deep heap
invariant. -/
theorem bind
    {context : Context}
    {environment finalEnvironment : Environment}
    {before after : Heap} {bindings : List (TypedBinder × Value)}
    (heap_typed : HeapWellTyped context before)
    (bindings_typed : BindingValuesHaveTypes context before bindings)
    (bound : BindingsBind environment before bindings finalEnvironment after) :
    HeapWellTyped context after := by
  induction bound generalizing context with
  | nil => exact heap_typed
  | cons head tail induction =>
      cases bindings_typed with
      | cons value_typed remaining_typed =>
          cases head with
          | intro allocation =>
              have middle_typed := heap_typed.allocate
                (.some value_typed) allocation
              have extension := HeapTypesExtend.of_allocation allocation
              exact induction middle_typed (remaining_typed.mono extension)

end HeapWellTyped

end Solcore.SourceSemantics.Dynamic
