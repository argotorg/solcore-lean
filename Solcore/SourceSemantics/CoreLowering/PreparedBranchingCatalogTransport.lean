import Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates

/-! Syntax weakening keeps the same prepared occurrences, keys and tokens.
The compiler certificates and original Source are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
open Core Frontend SourceInference
open GenericImperativeMatch GenericImperativeMatch.Structural
open PreparedBranchingCatalogSites
open CallableLambdaViewPreparedStaticTransport.Match
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
theorem catalog_algebra
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    PacketAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := definitions) (administrative := administrative) (expressionSyntax := expressionSyntax)
      (fun head => AssignmentSite invalidProjection missingDefault registry faults head) (fun head => head.Errors faults)
      (fun tree => HeaderSites invalidProjection missingDefault registry faults tree)
      (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
      (fun tree => CatalogSites invalidProjection missingDefault registry faults tree) := by
  refine {body := ?_, uninitialized := ?_, initialized := ?_, discard := ?_, block := ?_, ifThen := ?_, breaking := ?_, continuing := ?_, whileLoop := ?_, assign := ?_, bitNot := ?_, forLoop := ?_, initializersDone := ?_, initializerUninitialized := ?_, initializerInitialized := ?_, initializerDiscard := ?_, initializerAssign := ?_, initializerBitNot := ?_, matchWith := ?_, terminalBlock := ?_, terminalIf := ?_, terminalMatch := ?_}
  · intro context scope mode statements expected type code syntaxTree body
    apply CatalogSites.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
    all_goals assumption
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    apply CatalogSites.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    apply CatalogSites.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining _remainingErrors
    apply CatalogSites.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining _innerErrors _remainingErrors
    apply CatalogSites.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining _thenTreeErrors _elseTreeErrors _remainingErrors
    apply CatalogSites.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node rest expected type found form
    apply CatalogSites.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    all_goals assumption
  · intro context scope mode id node rest expected type found form
    apply CatalogSites.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
    all_goals assumption
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining _loopBodyErrors _remainingErrors
    apply CatalogSites.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining _remainingErrors _headErrors
    apply CatalogSites.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node assignment rest expected type body found form head remaining _remainingErrors _headErrors
    apply CatalogSites.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining _initialErrors _remainingErrors
    apply CatalogSites.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining)
    all_goals assumption
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped _loopErrors _postErrors
    apply CatalogSites.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped)
    all_goals assumption
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining _remainingErrors
    apply CatalogSites.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining _remainingErrors
    apply CatalogSites.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
    all_goals assumption
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining _remainingErrors
    apply CatalogSites.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining _remainingErrors _headErrors
    apply CatalogSites.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope assignment rest body condition post statements expected type head remaining _remainingErrors _headErrors
    apply CatalogSites.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining)
    all_goals assumption
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining _matchPayload _childErrors _remainingErrors
    apply CatalogSites.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining)
    all_goals first | assumption | exact _matchPayload.1 | exact _matchPayload.2
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued _innerErrors
    apply CatalogSites.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued)
    all_goals assumption
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued _thenErrors _elseErrors
    apply CatalogSites.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued)
    all_goals assumption
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued _matchPayload _childErrors
    apply CatalogSites.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued)
    all_goals first | assumption | exact _matchPayload.1 | exact _matchPayload.2

theorem eliminates
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope position expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope position expected type code}
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (definitions := definitions) (administrative := administrative)
      (fun head => AssignmentSite invalidProjection missingDefault registry faults head) (fun head => head.Errors faults)
      (fun postTree => HeaderSites invalidProjection missingDefault registry faults postTree)
      (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
      context scope position expected type code := by
  intro M algebra
  refine CatalogSites.rec (motive := fun {context scope position expected type code} _ _ =>
    M context scope position expected type code)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ sites
  · intro context scope mode statements expected type code syntaxTree body
    exact algebra.body (context := context) (scope := scope) (mode := mode) (statements := statements) (expected := expected) (type := type) (code := code) (syntaxTree := syntaxTree) (body := body)
  · intro context nextContext scope mode id node binder rest expected type body payload found form monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.uninitialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (rest := rest) (expected := expected) (type := type) (body := body) (payload := payload) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initialized (context := context) (nextContext := nextContext) (scope := scope) (mode := mode) (id := id) (node := node) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (expected := expected) (type := type) (found := found) (form := form) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining remainingErrors remainingErrorsIH
    exact algebra.discard (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (expression := expression) (expressionNode := expressionNode) (semicolon := semicolon) (rest := rest) (expected := expected) (lowered := lowered) (type := type) (body := body) (found := found) (form := form) (notTail := notTail) (expressionFound := expressionFound) (value := value) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerErrorsIH remainingErrorsIH
    exact algebra.block (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (body := body) (found := found) (form := form) (inner := inner) (remaining := remaining) (_innerErrors := innerErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenTreeErrorsIH elseTreeErrorsIH remainingErrorsIH
    exact algebra.ifThen (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (body := body) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining) (_thenTreeErrors := thenTreeErrorsIH) (_elseTreeErrors := elseTreeErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node rest expected type found form
    exact algebra.breaking (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node rest expected type found form
    exact algebra.continuing (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (rest := rest) (expected := expected) (type := type) (found := found) (form := form)
  · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopBodyErrors remainingErrors loopBodyErrorsIH remainingErrorsIH
    exact algebra.whileLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (statements := statements) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (loopCode := loopCode) (body := body) (selfReason := selfReason) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (nativeTyped := nativeTyped) (remaining := remaining) (_loopBodyErrors := loopBodyErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.assign (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.bitNot (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (assignment := assignment) (rest := rest) (expected := expected) (type := type) (body := body) (found := found) (form := form) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialErrors remainingErrors initialErrorsIH remainingErrorsIH
    exact algebra.forLoop (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (initializer := initializer) (condition := condition) (post := post) (statements := statements) (rest := rest) (expected := expected) (type := type) (initialCode := initialCode) (body := body) (found := found) (form := form) (initial := initial) (remaining := remaining) (_initialErrors := initialErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopBody postTree nativeTyped loopErrors postErrors loopErrorsIH
    exact algebra.initializersDone (context := context) (scope := scope) (condition := condition) (conditionNode := conditionNode) (post := post) (statements := statements) (expected := expected) (type := type) (conditionCode := conditionCode) (bodyCode := bodyCode) (postCode := postCode) (selfReason := selfReason) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (loopBody := loopBody) (postTree := postTree) (nativeTyped := nativeTyped) (_loopErrors := loopErrorsIH) (_postErrors := postErrors)
  · intro context nextContext scope binder rest body payload condition post statements expected type monomorphic extended ordinary projected allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initializerUninitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (rest := rest) (body := body) (payload := payload) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type monomorphic extended ordinary initializerFound sourceType initial allocation annotation same remaining remainingErrors remainingErrorsIH
    exact algebra.initializerInitialized (context := context) (nextContext := nextContext) (scope := scope) (binder := binder) (initializer := initializer) (initializerNode := initializerNode) (lowered := lowered) (body := body) (rest := rest) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (monomorphic := monomorphic) (extended := extended) (ordinary := ordinary) (initializerFound := initializerFound) (sourceType := sourceType) (initial := initial) (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope expression expressionNode rest lowered body condition post statements expected type found value remaining remainingErrors remainingErrorsIH
    exact algebra.initializerDiscard (context := context) (scope := scope) (expression := expression) (expressionNode := expressionNode) (rest := rest) (lowered := lowered) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (found := found) (value := value) (remaining := remaining) (_remainingErrors := remainingErrorsIH)
  · intro context scope assignment operator rhs rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.initializerAssign (context := context) (scope := scope) (assignment := assignment) (operator := operator) (rhs := rhs) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope assignment rest body condition post statements expected type head remaining remainingErrors headErrors remainingErrorsIH
    exact algebra.initializerBitNot (context := context) (scope := scope) (assignment := assignment) (rest := rest) (body := body) (condition := condition) (post := post) (statements := statements) (expected := expected) (type := type) (head := head) (remaining := remaining) (_remainingErrors := remainingErrorsIH) (_headErrors := headErrors)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining catalog patternContext childErrors remainingErrors childErrorsIH remainingErrorsIH
    exact algebra.matchWith (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (body := body) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (remaining := remaining) (_matchPayload := ⟨catalog, patternContext⟩) (_childErrors := childErrorsIH) (_remainingErrors := remainingErrorsIH)
  · intro context scope mode id node statements rest expected type innerCode suffix unique found form inner stops issued innerErrors innerErrorsIH
    exact algebra.terminalBlock (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (statements := statements) (rest := rest) (expected := expected) (type := type) (innerCode := innerCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (inner := inner) (stops := stops) (issued := issued) (_innerErrors := innerErrorsIH)
  · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenErrorsIH elseErrorsIH
    exact algebra.terminalIf (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (condition := condition) (conditionNode := conditionNode) (thenBody := thenBody) (elseBody := elseBody) (rest := rest) (expected := expected) (type := type) (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) (suffix := suffix) (unique := unique) (found := found) (form := form) (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops) (issued := issued) (_thenErrors := thenErrorsIH) (_elseErrors := elseErrorsIH)
  · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts unique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued catalog patternContext childErrors childErrorsIH
    exact algebra.terminalMatch (context := context) (scope := scope) (mode := mode) (id := id) (node := node) (resolution := resolution) (scrutineeNode := scrutineeNode) (rest := rest) (expected := expected) (type := type) (matched := matched) (suffix := suffix) (selfReason := selfReason) (control := control) (caseFacts := caseFacts) (unique := unique) (found := found) (form := form) (scrutineeFound := scrutineeFound) (scrutineeTyped := scrutineeTyped) (casesTyped := casesTyped) (defaultTyped := defaultTyped) (compilation := compilation) (sameValues := sameValues) (sameDefinitions := sameDefinitions) (allocator := allocator) (requests := requests) (receipt := receipt) (ordinary := ordinary) (children := children) (stops := stops) (issued := issued) (_matchPayload := ⟨catalog, patternContext⟩) (_childErrors := childErrorsIH)

theorem weaken {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {context scope mode statements expected type code}
    {tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code}
    (unique : NodeOccurrencesUnique source)
    (sites : CatalogSites invalidProjection missingDefault registry faults tree) :
    ∃ tree : Tree layouts owner active frame globals onError values source (fun _ => True) certificates definitions administrative
      context scope (.statements mode statements) expected type code,
      CatalogSites invalidProjection missingDefault registry faults tree := by
  exact CallableLambdaViewMatchRuntimeCertificates.transport_payload_with
    (CallableLambdaViewEdits.LocalView.refl source) (by intro id member; cases member) unique
    (fun _ _ _ => True.intro) (fun _ _ _ _ _ receipt => receipt)
    (fun head => AssignmentSite invalidProjection missingDefault registry faults head) (fun head => head.Errors faults)
    (fun tree => HeaderSites invalidProjection missingDefault registry faults tree)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
    (fun head => AssignmentSite invalidProjection missingDefault registry faults head) (fun head => head.Errors faults)
    (fun tree => HeaderSites invalidProjection missingDefault registry faults tree)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ Tree.MatchContextFields compilation context)
    (fun tree => CatalogSites invalidProjection missingDefault registry faults tree)
    catalog_algebra
    (fun _ _ receipt => receipt) (fun _ receipt => receipt)
    (fun tree receipt _ => ⟨tree, receipt⟩) (fun _ _ receipt => receipt)
    (eliminates sites) (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingCatalogTransport
