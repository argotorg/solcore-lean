import Solcore.SourceSemantics.CoreLowering.CompatiblePatternLeaves
import Solcore.SourceSemantics.CoreLowering.DataPatternExecution
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates

/-! Pure execution of the actual compatible matcher combinators. Child bundles
retain general typed payloads, remain lexical, and never change the store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
open Core Frontend SourceInference DataEquality
open DataPatternValues DataPatternExecution CompatiblePayload CompatiblePatternLeaves SourceCoreCompatibleDataMatches
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : GeneralHeap.LocationMap} {world : StoreTyping}

theorem bindings_length {binders : List (TypedBinder × Ty)} {sources : List (TypedBinder × Dynamic.Value)} {values : List Value}
    (represented : BindingsRep checked registry functions mapping world binders sources values) : binders.length = values.length := by
  induction represented with
  | nil => rfl
  | cons head tail ih => simp [ih]

theorem bindings_append {a c : List (TypedBinder × Ty)} {b d : List (TypedBinder × Dynamic.Value)} {v w : List Value}
    (left : BindingsRep checked registry functions mapping world a b v)
    (right : BindingsRep checked registry functions mapping world c d w) :
    BindingsRep checked registry functions mapping world (a ++ c) (b ++ d) (v ++ w) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem bundle_evaluates {environment : Environment} {store : Store} {expressions : List Expr} {values : List Value}
    (evaluations : ListRel (fun expression value => Evaluates environment store expression value store) expressions values) :
    Evaluates environment store (bundle expressions) (packValues values) store := by
  induction evaluations with
  | nil => exact .unit
  | cons head tail ih =>
    cases tail with
    | nil => exact head
    | cons second rest => exact .pair head ih

/-- The same closed matcher can be applied in any surrounding environment;
the input expression is a pure projection path. -/
def MatcherRuns (pattern : Pattern) (input : Value) (bindings : List Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inRight .unit (packValues bindings)) store

/-- A child vector extends an already selected binding accumulated in source order. -/
def ChildrenRun (patterns : List Pattern) (inputs bindings : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inRight .unit (packValues (accumulatedValues ++ bindings))) store

theorem ChildrenRun.nil : ChildrenRun [] [] [] := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected
  simpa [matchChildren] using Evaluates.inRight
    (leftType := Ty.unit) (bundle_evaluates (ListRel.map previous fun _ _ path => path.evaluates store))

theorem ChildrenRun.cons {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs headBindings tailBindings : List Value}
    (length : pattern.bindingTypes.length = headBindings.length)
    (head : MatcherRuns pattern input headBindings) (tail : ChildrenRun patterns inputs tailBindings) :
    ChildrenRun (pattern :: patterns) (input :: inputs) (headBindings ++ tailBindings) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues headBindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := headBindings) (.var rfl) length
    have result := tail (packValues headBindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)
    simpa [List.append_assoc] using result

def MatcherFails (pattern : Pattern) (input : Value) : Prop :=
  ∀ environment store expression, Selects environment expression input →
    Evaluates environment store (.apply pattern.matcher expression)
      (.inLeft (bundleType pattern.bindingTypes) .unit) store

def ChildrenFail (patterns : List Pattern) (inputs : List Value) : Prop :=
  ∀ environment store expressions accumulated accumulatedValues outputType,
    ListRel (Selects environment) expressions inputs →
    ListRel (Selects environment) accumulated accumulatedValues →
    Evaluates environment store (matchChildren outputType patterns expressions accumulated)
      (.inLeft outputType .unit) store

theorem ChildrenFail.head {pattern : Pattern} {patterns : List Pattern} {input : Value} {inputs : List Value}
    (failed : MatcherFails pattern input) : ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected => exact .caseLeft (failed _ _ _ inputSelected) (.inLeft .unit)

theorem ChildrenFail.tail {pattern : Pattern} {patterns : List Pattern} {input : Value}
    {inputs bindings : List Value} (length : pattern.bindingTypes.length = bindings.length)
    (head : MatcherRuns pattern input bindings) (tail : ChildrenFail patterns inputs) :
    ChildrenFail (pattern :: patterns) (input :: inputs) := by
  intro environment store expressions accumulated accumulatedValues outputType selected previous
  cases selected with
  | cons inputSelected restSelected =>
    apply Evaluates.caseRight (head environment store _ inputSelected)
    have projections := projectionList_selects (environment := packValues bindings :: environment)
      (expression := .var 0) (types := pattern.bindingTypes) (values := bindings) (.var rfl) length
    exact tail (packValues bindings :: environment) store _ _ _ outputType
      (selects_weaken_list restSelected _) (ListRel.append (selects_weaken_list previous _) projections)


theorem projectedList_catalog {compilation : CompatiblePatternCertificates.Compilation} {source : TypedSource}
    {types : List TypeSystem.Ty} {coreTypes : List Ty}
    (projected : types.mapM (SourceCoreCompatibleDataMatches.projected compilation source) = .ok coreTypes) :
    types.mapM compilation.checked.catalog.project = .ok coreTypes := by
  induction types generalizing coreTypes with
  | nil => simp [List.mapM_nil, pure, Except.pure] at projected; subst coreTypes; rfl
  | cons type types ih =>
    cases head : SourceCoreCompatibleDataMatches.projected compilation source type with
    | error error => simp [List.mapM_cons, head, bind, Except.bind] at projected
    | ok native =>
      cases tail : types.mapM (SourceCoreCompatibleDataMatches.projected compilation source) with
      | error error => simp [List.mapM_cons, head, tail, bind, Except.bind] at projected
      | ok natives =>
        simp [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure] at projected
        subst coreTypes
        have first := CompatibleExpressionReads.projectType_of_accepted head
        simp [List.mapM_cons, first, ih tail, bind, Except.bind, pure, Except.pure]
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternExecution
