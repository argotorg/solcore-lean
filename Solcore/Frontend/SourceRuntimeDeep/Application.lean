import Solcore.Frontend.SourceRuntimeDeep.ValueEnvironment

/-! Deep typing for graph arguments, function dispatch, and application. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- A deeply typed embedded Core closure runs in a typed Core state.  On
success both its result and the final heap re-enter the graph relation.  This
is the Core-callback branch needed by the graph evaluator preservation proof. -/
theorem Value.coreClosure_application_preserves_result_type
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameterType resultType : Core.Ty}
    {body : Core.Expr} {captured : Core.Environment}
    {argument value : Core.Value}
    {initialStore finalStore : Core.Store} {fuel : Nat}
    (closureTyping : Core.RuntimeValueHasType world
      (.closure parameterType resultType body captured)
      (.function parameterType resultType) definitions)
    (argumentTyping : Core.RuntimeValueHasType world argument parameterType
      definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : Core.runStateful fuel
      (Core.State.initial body (argument :: captured) initialStore) =
        .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld (Value.ofCore value) resultType
        definitions := by
  cases closureTyping with
  | closure capturedTyping bodyTyping =>
      have evaluation := Core.runStateful_evaluation_sound completed
      obtain ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩ :=
        Core.evaluation_preserves_type evaluation bodyTyping
          (Core.RuntimeEnvironmentHasTypes.cons argumentTyping capturedTyping)
          storeTyping
      exact ⟨finalWorld, extension, finalStoreTyping,
        Value.GraphHasType.ofCore resultTyping⟩

/-- Preservation for the actual `applyValue` Core-closure branch: a graph
argument assembled from deeply typed pieces can cross into Core, and a
successful callback returns a deeply typed graph value and final heap. -/
theorem applyValue_coreClosure_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameterType resultType : Core.Ty}
    {body : Core.Expr} {captured : Core.Environment}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (functionTyping : Value.GraphHasType program world
      (.coreClosure parameterType resultType body captured)
      (.function parameterType resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) parameterType definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel
      (.coreClosure parameterType resultType body captured)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  cases functionTyping with
  | core projection coreTyping _ =>
      simp [Value.toCore?] at projection
      cases projection
      have argumentTag := argumentTyping.hasType
      simp only [Value.HasType] at argumentTag
      cases argumentProjection : (packValues arguments).toCore? with
      | none =>
          simp [applyValue, argumentTag, argumentProjection] at completed
          split at completed <;> contradiction
      | some coreArgument =>
          have coreArgumentTyping :=
            argumentTyping.toCore argumentProjection
          cases coreRun : Core.runStateful coreFuel
              (Core.State.initial body (coreArgument :: captured)
                initialStore) with
          | outOfFuel state =>
              simp [applyValue, argumentTag, argumentProjection, coreRun]
                at completed
              split at completed <;> contradiction
          | fault error state =>
              simp [applyValue, argumentTag, argumentProjection, coreRun]
                at completed
              split at completed <;> contradiction
          | done coreValue coreStore =>
              have coreClosureTyping : Core.RuntimeValueHasType world
                  (.closure parameterType resultType body captured)
                  (.function parameterType resultType) definitions :=
                coreTyping
              obtain ⟨finalWorld, extension, finalStoreTyping,
                resultTyping⟩ :=
                Value.coreClosure_application_preserves_result_type
                  (program := program) coreClosureTyping coreArgumentTyping
                  storeTyping coreRun
              have coreResultTyping := resultTyping.toCore
                (Value.toCore?_ofCore coreValue)
              have resultTag : coreValue.type = resultType :=
                coreResultTyping.type_eq
              simp [applyValue, argumentTag, argumentProjection, coreRun,
                resultTag] at completed
              split at completed
              · contradiction
              cases completed
              exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- Deep Core argument typing transfers to the source runtime's named binder
environment when the selected definition's parameter types agree. -/
theorem EnvironmentGraphHasTypes.ofCoreParameters
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {arguments : List Core.Value} {types : List Core.Ty}
    (typing : Core.RuntimeEnvironmentHasTypes world arguments types
      definitions) :
    ∀ (parameters : List Parameter),
      parameters.map Prod.snd = types →
      EnvironmentGraphHasTypes program world
        (List.zip (parameters.map Prod.fst) (arguments.map Value.ofCore))
        (parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)) definitions := by
  apply Core.RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun environment context relationDefinitions _ =>
        ∀ parameters : List Parameter,
          parameters.map Prod.snd = context →
          EnvironmentGraphHasTypes program world
            (List.zip (parameters.map Prod.fst)
              (environment.map Value.ofCore))
            (parameters.map fun parameter =>
              (parameter.1, StaticType.value parameter.2))
            relationDefinitions)
      (t := typing)
  case unit => intros; trivial
  case bool => intros; trivial
  case word => intros; trivial
  case pair => intros; trivial
  case inLeft => intros; trivial
  case inRight => intros; trivial
  case closure => intros; trivial
  case cellRef => intros; trivial
  case constructed => intros; trivial
  case nil =>
      intro _ parameters parameterTypesEqual
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters => simp at parameterTypesEqual
  case cons =>
      intro _ _ expectedType _ tailContext head _ _ tailIH
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => simp at parameterTypesEqual
      | cons parameter parameters =>
          have headMatch : parameter.2 = expectedType := by
            exact (List.cons.inj parameterTypesEqual).1
          have tailMatch : parameters.map Prod.snd = tailContext :=
            (List.cons.inj parameterTypesEqual).2
          cases parameter with
          | mk id parameterType =>
              cases headMatch
              simpa only [List.map_cons, List.zip_cons_cons] using
                (EnvironmentGraphHasTypes.cons
                  (Value.GraphHasType.ofCore head)
                  (tailIH parameters tailMatch))

/-- The existing deep entry-input certificate supplies the graph evaluator's
named, deeply typed initial parameter environment. -/
theorem CheckedProgram.RuntimeInputsHaveType.boundArgumentsGraph
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions) :
    EnvironmentGraphHasTypes checked.program world
      (List.zip (definition.parameters.map Prod.fst)
        (arguments.map Value.ofCore))
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2)) definitions := by
  exact EnvironmentGraphHasTypes.ofCoreParameters
    typing.argumentsTyping definition.parameters rfl

/-- For an honestly checked program, the same selected definition has a
checked body under the parameter context supplied by the deep input bridge. -/
theorem CheckedProgram.RuntimeInputsHaveType.selectedBodyHasType
    {checked : CheckedProgram} {entry : Key}
    {arguments : List Core.Value} {store : Core.Store}
    {definition : Definition} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments store definition
      world definitions)
    (checkedBy : checked.program.check = .ok checked) :
    Expr.InfersType checked.program
      (definition.parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2))
      definition.body definition.resultType :=
  Program.IsWellTyped.foundDefinition_hasType
    ⟨checked, checkedBy⟩ typing.found

/-- Ordered deep argument typing before the graph runtime's structural
argument bundling. -/
inductive GraphArgumentsHaveTypes
    (program : Program) (world : Core.StoreTyping) :
    List Value → List Core.Ty →
    (definitions : Core.DataEnvironment := []) → Prop where
  | nil {definitions : Core.DataEnvironment} :
      GraphArgumentsHaveTypes program world [] [] definitions
  | cons {definitions : Core.DataEnvironment}
      {value : Value} {type : Core.Ty}
      {values : List Value} {types : List Core.Ty} :
      Value.GraphHasType program world value type definitions →
      GraphArgumentsHaveTypes program world values types definitions →
      GraphArgumentsHaveTypes program world (value :: values)
        (type :: types) definitions

/-- Packing individually deep arguments preserves their structural bundle
type, including the zero- and one-argument conventions. -/
theorem GraphArgumentsHaveTypes.packValues
    {program : Program} {world : Core.StoreTyping}
    {values : List Value} {types : List Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : GraphArgumentsHaveTypes program world values types
      definitions) :
    Value.GraphHasType program world (packValues values)
      (bundleType types) definitions := by
  induction typing with
  | nil =>
      rename_i relationDefinitions
      simpa [SourceRuntime.packValues, bundleType] using
        (Value.GraphHasType.unit program world relationDefinitions)
  | cons head tail tailIH =>
      cases tail with
      | nil =>
          simpa [SourceRuntime.packValues, bundleType] using head
      | cons next rest =>
          simpa [SourceRuntime.packValues, bundleType] using
            (Value.GraphHasType.pair head tailIH)

/-- Repartitioning a deeply typed structural argument bundle according to a
callee's source binder list preserves deep typing of every extracted value.
This covers the runtime's intentional zero/unit and product/arity erasure. -/
theorem GraphArgumentsHaveTypes.ofUnpackValues
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (parameters : List Parameter) (bundle : Value) (values : List Value)
    (typing : Value.GraphHasType program world bundle
      (parameterType parameters) definitions)
    (unpacked : unpackValues? parameters bundle = some values) :
    GraphArgumentsHaveTypes program world values
      (parameters.map Prod.snd) definitions := by
  induction parameters generalizing bundle values with
  | nil =>
      cases bundle <;> simp [unpackValues?] at unpacked
      cases unpacked
      exact .nil
  | cons parameter parameters ih =>
      cases parameters with
      | nil =>
          simp [unpackValues?] at unpacked
          cases unpacked
          exact .cons (by simpa [parameterType] using typing) .nil
      | cons next rest =>
          cases bundle <;> simp [unpackValues?] at unpacked
          rename_i first remaining
          cases remainingResult : unpackValues? (next :: rest) remaining with
          | none => simp [remainingResult] at unpacked
          | some remainingValues =>
              simp [remainingResult] at unpacked
              cases unpacked
              have pairTyping : Value.GraphHasType program world
                  (.pair first remaining)
                  (.product parameter.2
                    (parameterType (next :: rest))) definitions := by
                simpa [parameterType] using typing
              obtain ⟨firstTyping, remainingTyping⟩ :=
                pairTyping.pairComponents
              exact .cons firstTyping
                (ih remaining remainingValues remainingTyping remainingResult)

/-- Deeply typed normalized arguments supply the callee's named parameter
environment; their source-local identities are recovered from the binder
list. -/
theorem GraphArgumentsHaveTypes.toNamedEnvironment
    {program : Program} {world : Core.StoreTyping}
    {values : List Value} {types : List Core.Ty}
    {definitions : Core.DataEnvironment}
    (typing : GraphArgumentsHaveTypes program world values types
      definitions) :
    ∀ (parameters : List Parameter),
      parameters.map Prod.snd = types →
      EnvironmentGraphHasTypes program world
        (List.zip (parameters.map Prod.fst) values)
        (parameters.map fun parameter =>
          (parameter.1, StaticType.value parameter.2)) definitions := by
  induction typing with
  | nil =>
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => exact .nil
      | cons parameter parameters => simp at parameterTypesEqual
  | cons head tail tailIH =>
      intro parameters parameterTypesEqual
      cases parameters with
      | nil => simp at parameterTypesEqual
      | cons parameter parameters =>
          have headMatch : parameter.2 = _ :=
            (List.cons.inj parameterTypesEqual).1
          have tailMatch : parameters.map Prod.snd = _ :=
            (List.cons.inj parameterTypesEqual).2
          cases parameter with
          | mk id parameterType =>
              cases headMatch
              simpa only [List.map_cons, List.zip_cons_cons] using
                (EnvironmentGraphHasTypes.cons head
                  (tailIH parameters tailMatch))

/-- A freshly bound parameter prefix can be added to the closure's already
deeply typed lexical environment. -/
theorem EnvironmentGraphHasTypes.append
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {front : Environment} {frontContext : StaticContext}
    (frontTyping : EnvironmentGraphHasTypes program world front
      frontContext definitions) :
    ∀ {back : Environment} {backContext : StaticContext},
      EnvironmentGraphHasTypes program world back backContext definitions →
      EnvironmentGraphHasTypes program world (front ++ back)
        (frontContext ++ backContext) definitions := by
  induction front generalizing frontContext with
  | nil =>
      cases frontTyping
      intro _ _ backTyping
      exact backTyping
  | cons entry rest ih =>
      cases frontTyping with
      | cons head tail =>
          intro _ _ backTyping
          exact .cons head (ih tail backTyping)

/-- The complete lexical environment used by a successful source-closure
call is deeply typed after structural unpacking and parameter binding. -/
theorem EnvironmentGraphHasTypes.ofUnpackedCall
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameters : List Parameter} {bundle : Value}
    {values : List Value} {captured : Environment}
    {context : StaticContext}
    (bundleTyping : Value.GraphHasType program world bundle
      (parameterType parameters) definitions)
    (unpacked : unpackValues? parameters bundle = some values)
    (capturedTyping : EnvironmentGraphHasTypes program world captured
      context definitions) :
    EnvironmentGraphHasTypes program world
      (List.zip (parameters.map Prod.fst) values ++ captured)
      ((parameters.map fun parameter =>
        (parameter.1, StaticType.value parameter.2)) ++ context)
      definitions := by
  have argumentsTyping := GraphArgumentsHaveTypes.ofUnpackValues
    parameters bundle values bundleTyping unpacked
  have boundTyping := argumentsTyping.toNamedEnvironment parameters rfl
  exact EnvironmentGraphHasTypes.append boundTyping capturedTyping

/-- Looking up a statically typed local in a deeply typed lexical
environment returns a deeply typed runtime value at the erased type. -/
theorem EnvironmentGraphHasTypes.lookup
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    (typing : EnvironmentGraphHasTypes program world environment context
      definitions)
    {id : Resolved.LocalId} {staticType : StaticType}
    (found : lookupStatic? context id = some staticType) :
    ∃ value,
      lookupValue? environment id = some value ∧
      Value.GraphHasType program world value staticType.erase definitions := by
  induction environment generalizing context with
  | nil =>
      cases typing
      simp [lookupStatic?] at found
  | cons entry rest ih =>
      cases typing with
      | cons head tail =>
          rename_i headId headValue headType tailContext
          by_cases same : headId = id
          · subst id
            simp [lookupStatic?] at found
            cases found
            exact ⟨headValue, by simp [lookupValue?], head⟩
          · have tailFound : lookupStatic? tailContext id =
                some staticType := by
              simpa [lookupStatic?, same] using found
            obtain ⟨value, valueFound, valueTyping⟩ :=
              ih tail tailFound
            exact ⟨value,
              by simpa [lookupValue?, same] using valueFound,
              valueTyping⟩

/-- The evaluator induction hypothesis required at a source body call.  It is
separate from the application dispatcher so the closure and global cases can
be proved once and reused by the eventual whole-evaluator induction. -/
def BodyPreservesGraphTyping
    (program : Program)
    (evaluateBody : Environment → Core.Store → Expr → RunResult) : Prop :=
  ∀ {world : Core.StoreTyping} {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store : Core.Store} {expression : Expr} {expected : Core.Ty}
    {value : Value} {finalStore : Core.Store},
    EnvironmentGraphHasTypes program world environment context definitions →
    Expr.InfersType program context expression expected →
    Core.StoreHasTypes world store →
    evaluateBody environment store expression = .done value finalStore →
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions

/-- Pointwise static typing for an ordered expression list, used by the
argument evaluator's sequential preservation proof. -/
inductive ExpressionsHaveTypes (program : Program) (context : StaticContext) :
    List Expr → List Core.Ty → Prop where
  | nil : ExpressionsHaveTypes program context [] []
  | cons {expression : Expr} {type : Core.Ty}
      {expressions : List Expr} {types : List Core.Ty} :
      Expr.InfersType program context expression type →
      ExpressionsHaveTypes program context expressions types →
      ExpressionsHaveTypes program context
        (expression :: expressions) (type :: types)

/-- The executable checker returns precisely the ordered per-expression
certificates consumed by sequential argument preservation. -/
theorem ExpressionsHaveTypes.ofInferList
    (program : Program) (context : StaticContext) :
    ∀ (expressions : List Expr) (staticTypes : List StaticType),
      inferList program context expressions = .ok staticTypes →
      ExpressionsHaveTypes program context expressions
        (staticTypes.map StaticType.erase) := by
  intro expressions
  induction expressions with
  | nil =>
      intro staticTypes success
      simp [inferList] at success
      cases success
      exact .nil
  | cons expression expressions ih =>
      intro staticTypes success
      obtain ⟨head, tail, headOk, tailOk, typesEq⟩ :=
        inferList_cons_ok program context expression expressions
          staticTypes success
      subst staticTypes
      exact .cons ⟨head, headOk, rfl⟩ (ih tail tailOk)

/-- Sequential argument evaluation preserves every deep argument type and
threads a monotone typed heap through each successful expression. -/
theorem ExpressionsHaveTypes.evaluateArguments_done_deep
    {program : Program} {context : StaticContext}
    {expressions : List Expr} {types : List Core.Ty}
    (typing : ExpressionsHaveTypes program context expressions types)
    (evaluateOne : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateOne) :
    ∀ {world : Core.StoreTyping}
      {definitions : Core.DataEnvironment}
      {environment : Environment} {store : Core.Store}
      {values : List Value} {finalStore : Core.Store},
      EnvironmentGraphHasTypes program world environment context definitions →
      Core.StoreHasTypes world store →
      evaluateArguments (evaluateOne environment) store expressions =
        .done values finalStore →
      ∃ finalWorld,
        Core.WorldExtends world finalWorld ∧
        Core.StoreHasTypes finalWorld finalStore ∧
        GraphArgumentsHaveTypes program finalWorld values types definitions := by
  induction typing with
  | nil =>
      intro world definitions environment store values finalStore
        environmentTyping storeTyping completed
      have completed' : ArgumentsResult.done [] store =
          .done values finalStore := by
        simpa [evaluateArguments] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping, .nil⟩
  | cons expressionTyping tailTyping tailIH =>
      intro world definitions environment store values finalStore
        environmentTyping storeTyping completed
      rename_i headExpression headType tailExpressions tailTypes
      cases headRun : evaluateOne environment store headExpression with
      | outOfFuel nextStore =>
          unfold evaluateArguments at completed
          rw [headRun] at completed
          cases completed
      | fault error nextStore =>
          unfold evaluateArguments at completed
          rw [headRun] at completed
          cases completed
      | done headValue nextStore =>
          obtain ⟨middleWorld, firstExtension, nextStoreTyping,
            headTyping⟩ :=
            bodyPreservation environmentTyping expressionTyping
              storeTyping headRun
          have nextEnvironmentTyping :=
            EnvironmentGraphHasTypes.weaken firstExtension
              environmentTyping
          cases tailRun : evaluateArguments (evaluateOne environment)
              nextStore tailExpressions with
          | outOfFuel doneStore =>
              unfold evaluateArguments at completed
              rw [headRun] at completed
              dsimp at completed
              rw [tailRun] at completed
              cases completed
          | fault error doneStore =>
              unfold evaluateArguments at completed
              rw [headRun] at completed
              dsimp at completed
              rw [tailRun] at completed
              cases completed
          | done tailValues doneStore =>
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                tailValuesTyping⟩ :=
                tailIH nextEnvironmentTyping nextStoreTyping tailRun
              have completed' : ArgumentsResult.done
                  (headValue :: tailValues) doneStore =
                  .done values finalStore := by
                simpa only [evaluateArguments, headRun, tailRun]
                  using completed
              cases completed'
              exact ⟨finalWorld, firstExtension.trans secondExtension,
                finalStoreTyping,
                .cons (headTyping.weaken secondExtension) tailValuesTyping⟩

/-- Source-closure application preserves deep result and heap typing assuming
the recursive body evaluator satisfies its induction contract. -/
theorem applyValue_sourceClosure_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {parameters : List Parameter} {resultType : Core.Ty}
    {body : Expr} {captured : Environment}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (functionTyping : Value.GraphHasType program world
      (.closure parameters resultType body captured)
      (.function (parameterType parameters) resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) (parameterType parameters) definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel
      (.closure parameters resultType body captured)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  cases functionTyping with
  | core projection _ _ =>
      simp [Value.toCore?] at projection
  | sourceClosure capturedTyping bodyTyping =>
      rename_i context
      have argumentTag := argumentTyping.hasType
      simp only [Value.HasType] at argumentTag
      cases unpacked : unpackValues? parameters (packValues arguments) with
      | none =>
          simp [applyValue, argumentTag, unpacked] at completed
          split at completed <;> contradiction
      | some normalized =>
          have environmentTyping : EnvironmentGraphHasTypes program world
              (bindParameters parameters normalized captured)
              ((parameters.map fun parameter =>
                (parameter.1, StaticType.value parameter.2)) ++ context)
              definitions := by
            simpa [bindParameters] using
              (EnvironmentGraphHasTypes.ofUnpackedCall argumentTyping
                unpacked capturedTyping)
          cases bodyRun : evaluateBody
              (bindParameters parameters normalized captured)
              initialStore body with
          | outOfFuel store =>
              simp [applyValue, argumentTag, unpacked, bodyRun]
                at completed
              split at completed <;> contradiction
          | fault error store =>
              simp [applyValue, argumentTag, unpacked, bodyRun]
                at completed
              split at completed <;> contradiction
          | done bodyValue bodyStore =>
              obtain ⟨finalWorld, extension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation environmentTyping bodyTyping storeTyping
                  bodyRun
              have resultTag := resultTyping.hasType
              simp only [Value.HasType] at resultTag
              simp [applyValue, argumentTag, unpacked, bodyRun,
                resultTag] at completed
              split at completed
              · contradiction
              cases completed
              exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- The named-global application branch uses the checker-certified selected
body and a deeply typed fresh parameter environment. -/
theorem applyValue_global_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {key : Key} {definition : Definition}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (wellTyped : program.IsWellTyped)
    (found : program.findDefinition? key = some definition)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) (parameterType definition.parameters)
      definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel (.global key)
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value definition.resultType
        definitions := by
  have bodyTyping := wellTyped.foundDefinition_hasType found
  have argumentTag := argumentTyping.hasType
  simp only [Value.HasType] at argumentTag
  cases unpacked : unpackValues? definition.parameters
      (packValues arguments) with
  | none =>
      simp [applyValue, found, argumentTag, unpacked] at completed
      split at completed <;> contradiction
  | some normalized =>
      have environmentTyping : EnvironmentGraphHasTypes program world
          (bindParameters definition.parameters normalized [])
          (definition.parameters.map fun parameter =>
            (parameter.1, StaticType.value parameter.2)) definitions := by
        simpa [bindParameters] using
          (EnvironmentGraphHasTypes.ofUnpackedCall argumentTyping
            unpacked (EnvironmentGraphHasTypes.nil
              (program := program) (world := world)))
      cases bodyRun : evaluateBody
          (bindParameters definition.parameters normalized [])
          initialStore definition.body with
      | outOfFuel store =>
          simp [applyValue, found, argumentTag, unpacked, bodyRun]
            at completed
          split at completed <;> contradiction
      | fault error store =>
          simp [applyValue, found, argumentTag, unpacked, bodyRun]
            at completed
          split at completed <;> contradiction
      | done bodyValue bodyStore =>
          obtain ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩ :=
            bodyPreservation environmentTyping bodyTyping storeTyping bodyRun
          have resultTag := resultTyping.hasType
          simp only [Value.HasType] at resultTag
          simp [applyValue, found, argumentTag, unpacked, bodyRun,
            resultTag] at completed
          split at completed
          · contradiction
          cases completed
          exact ⟨finalWorld, extension, finalStoreTyping, resultTyping⟩

/-- All successful graph application dispatch branches preserve deep typing.
The source-body contract is used only for source closures and named globals;
embedded Core closures use Core's own preservation theorem. -/
theorem applyValue_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {functionValue : Value} {argumentType resultType : Core.Ty}
    {arguments : List Value}
    {initialStore finalStore : Core.Store} {value : Value}
    {coreFuel : Nat}
    (evaluateBody : Environment → Core.Store → Expr → RunResult)
    (bodyPreservation : BodyPreservesGraphTyping program evaluateBody)
    (wellTyped : program.IsWellTyped)
    (functionTyping : Value.GraphHasType program world functionValue
      (.function argumentType resultType) definitions)
    (argumentTyping : Value.GraphHasType program world
      (packValues arguments) argumentType definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : applyValue program evaluateBody coreFuel functionValue
      arguments initialStore = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value resultType definitions := by
  have functionTag := functionTyping.hasType
  simp only [Value.HasType] at functionTag
  cases functionValue with
  | closure parameters declaredResult body captured =>
      change some (Core.Ty.function (parameterType parameters)
        declaredResult) =
        some (Core.Ty.function argumentType resultType) at functionTag
      have functionEq := Option.some.inj functionTag
      cases functionEq
      exact applyValue_sourceClosure_done_deep evaluateBody
        bodyPreservation functionTyping argumentTyping storeTyping completed
  | global key =>
      cases found : program.findDefinition? key with
      | none => simp [applyValue, found] at completed
      | some definition =>
          change (program.findSignature? key).map Signature.toCoreType =
            some (.function argumentType resultType) at functionTag
          rw [Program.findSignature?, found] at functionTag
          simp only [Option.map_some] at functionTag
          have functionEq := Option.some.inj functionTag
          have functionEq' : Core.Ty.function
              (bundleType (definition.parameters.map Prod.snd))
              definition.resultType =
              .function argumentType resultType := by
            simpa [Definition.signature, Signature.toCoreType] using
              functionEq
          injection functionEq' with inputEq outputEq
          have parameterEq : parameterType definition.parameters =
              argumentType := by
            rw [parameterType_eq_bundleType_map]
            exact inputEq
          have resultEq : definition.resultType = resultType := by
            exact outputEq
          cases parameterEq
          cases resultEq
          exact applyValue_global_done_deep evaluateBody
            bodyPreservation wellTyped found argumentTyping storeTyping
            completed
  | coreClosure parameter declaredResult body captured =>
      change some (Core.Ty.function parameter declaredResult) =
        some (Core.Ty.function argumentType resultType) at functionTag
      have functionEq := Option.some.inj functionTag
      cases functionEq
      exact applyValue_coreClosure_done_deep evaluateBody functionTyping
        argumentTyping storeTyping completed
  | unit => simp [applyValue] at completed
  | bool _ => simp [applyValue] at completed
  | word _ => simp [applyValue] at completed
  | hostFunction _ => simp [applyValue] at completed
  | pair _ _ => simp [applyValue] at completed
  | inLeft _ _ => simp [applyValue] at completed
  | inRight _ _ => simp [applyValue] at completed
  | cellRef _ _ => simp [applyValue] at completed
  | constructed _ _ => simp [applyValue] at completed


end Solcore.Frontend.SourceRuntime
