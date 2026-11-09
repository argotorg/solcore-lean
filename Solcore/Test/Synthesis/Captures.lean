import Solcore.Synthesis.Internal.Captures

/-!
# Tests: closure captures and closure factories

The profiles `runtime-closure-captures` and `runtime-closure-factories`.
-/

section
/-! The `runtime-closure-captures` and `runtime-closure-factories` profiles.
Their Core references capture by value: a closure loads snapshots of what it
captures when it is created and copies them into fresh cells at every call,
while the contract field and the fold are shared cells. They agree with the
plans' direct interpreter on generated plans, and four fixtures' sources and
results are golden, the results from the corpus validator's separate Python
model. Admission refuses undeclared locals, the forms the pin rejects with
`SC0422`, and factories, observations and loops outside each profile;
generation draws every shape and replays exactly; tampering is refused, and
reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceClosureCaptureCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Captures
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.Captures (Profile Observed)

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

/-- The eight boundary inputs, then four more. -/
private def inputs : List Nat :=
  Solcore.Synthesis.Core.Integers.boundaryWords ++
    [3, 7, 2 ^ 128 + 5, 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef]

private def observedText : Observed → String
  | .word word => toString word.val
  | .reverted data => Captures.hexBytes data

/-- The reference's outcome at an input. -/
private def referenceText (plan : Plan) (input : Nat) : String :=
  match (plan.applied (Word.ofNatModulo input)).toCore.runStateful fuel with
  | .done value _ => match Observed.ofValue? value with
      | some observed => observedText observed
      | none => "invalid-result"
  | .outOfFuel _ => "out-of-fuel"
  | .fault _ _ => "core-fault"

/-- The interpreter's outcome at an input, as revert data for a panic. -/
private def interpreterText (plan : Plan) (input : Nat) : String :=
  match plan.outcome input with
  | .word value => toString value
  | .panic code => Captures.hexBytes ([0x4e, 0x48, 0x7b, 0x71] ++ Captures.wordBytes code)

private def v (up index : Nat) : Solcore.Synthesis.Core.Captures.Term := .var (.value ⟨up, index⟩)
private def p (up : Nat) : Solcore.Synthesis.Core.Captures.Term := .var (.param up)
private def n : Solcore.Synthesis.Core.Captures.Term := .var .field
private def add (left right : Solcore.Synthesis.Core.Captures.Term) : Solcore.Synthesis.Core.Captures.Term := .op .add left right

/-! Fixtures. `captureA` writes a captured local in a body and calls that
closure once and twice, writes the local after the capture, and makes a lambda
whose body declares a local and a nested lambda that writes the field; a loop
calls it through `sc_apply`, and a checked sum of the field ends it. `captureB`
captures a closure, rebinds it to a lambda, aliases it, calls through
`sc_twice`, and makes a lambda whose body rebinds a captured closure and
writes the captured input, which `run` reads unchanged after a checked
division. `factoryA` has a free factory that writes its local after a lambda
captured it and returns that closure, and a method factory with a field
write and a checked sum that returns a lambda over its local; `run` makes
three closures, two of the same factory, calls one in a lambda body, discards
a call and reads the field. `factoryB` chains a factory through another and
calls the made closure in its body, remakes and realiases closures, and makes a
lambda that writes the field and divides by its argument. -/

private def captureA : Plan := {factories := [], steps := [
  .value (p 0),
  .lambda [.assign (.value ⟨1, 0⟩) (add (v 1 0) (p 0))] (v 1 0),
  .observe (.call .direct ⟨0, 0⟩ (.lit 1)),
  .observe (.call .twice ⟨0, 0⟩ (.lit 2)),
  .assign (.value ⟨0, 0⟩) (.op .mul (v 0 0) (.lit 3)),
  .lambda [.value (.op .xor (p 0) (v 1 0)), .lambda [.assign .field (add n (p 0))] (v 1 0)] (.call .direct ⟨0, 0⟩ (p 0)),
  .loop 2 [.observe (.call .apply ⟨0, 1⟩ (p 0)), .assign .field (add n (.lit 1))],
  .observe (.checked .add n (v 0 0)),
  .observe (v 0 0)]}

private def captureB : Plan := {factories := [], steps := [
  .lambda [] (add (p 0) (p 1)),
  .lambda [] (.op .mul (.call .direct ⟨1, 0⟩ (p 0)) (.lit 2)),
  .relambda ⟨0, 0⟩ [] (.op .sub (p 0) (.lit 1)),
  .alias ⟨0, 0⟩,
  .observe (.call .direct ⟨0, 1⟩ (.lit 5)),
  .observe (.call .twice ⟨0, 2⟩ (p 0)),
  .lambda [.realias ⟨1, 0⟩ ⟨1, 2⟩, .assign (.param 1) (add (p 1) (.lit 7))] (.call .direct ⟨1, 0⟩ (p 1)),
  .observe (.call .direct ⟨0, 3⟩ (.lit 0)),
  .observe (.checked .div (.lit 1000) (p 0)),
  .observe (p 0)]}

private def factoryA : Plan := {
  factories := [
    {method := false, body := [.value (.op .mul (p 0) (.lit 3)), .lambda [] (add (v 1 0) (p 0)),
      .assign (.value ⟨0, 0⟩) (add (v 0 0) (.lit 1))], returns := .closure 0},
    {method := true, body := [.assign .field (add n (.lit 1)), .value (.checked .add (p 0) n)],
      returns := .lambda [.assign (.value ⟨1, 0⟩) (add (v 1 0) (p 0))] (add (v 1 0) n)}],
  steps := [
    .make 0 (p 0),
    .make 1 (.lit 5),
    .make 1 (p 0),
    .observe (.call .direct ⟨0, 0⟩ (.lit 2)),
    .observe (.call .twice ⟨0, 1⟩ (.lit 1)),
    .lambda [.make 0 (p 0)] (.call .direct ⟨0, 0⟩ (p 1)),
    .observe (.call .apply ⟨0, 3⟩ n),
    .discard 1 (p 0),
    .observe (add (.call .direct ⟨0, 2⟩ (.lit 0)) n)]}

private def factoryB : Plan := {
  factories := [
    {method := false, body := [], returns := .lambda [] (.op .xor (p 0) (p 1))},
    {method := false, body := [.make 0 (add (p 0) (.lit 1)), .value (.call .direct ⟨0, 0⟩ (p 0))],
      returns := .lambda [] (add (p 1) (v 1 0))}],
  steps := [
    .make 1 (.lit 7),
    .make 0 (p 0),
    .observe (.call .direct ⟨0, 0⟩ (.lit 1)),
    .remake ⟨0, 1⟩ 1 (p 0),
    .realias ⟨0, 0⟩ ⟨0, 1⟩,
    .lambda [.assign .field (add n (p 0)), .value (.checked .div n (p 0))] (v 0 0),
    .observe (.call .direct ⟨0, 2⟩ (p 0)),
    .observe (.call .direct ⟨0, 0⟩ n),
    .observe (.op .sub n (.call .twice ⟨0, 1⟩ (.lit 3)))]}

private def captureASource : String :=
  "import * from std;\nimport * from std.dispatch;\n\nfunction sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(x);\n}\n\nfunction sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(f(x));\n}\n\ncontract SynthesizedClosureCaptures {\n    sc_n: word;\n\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_r: word = 0;\n        let sc_v0: word = sc_x;\n        let sc_f0: function (word) returns (word) = lam (sc_a: word) -> word {\n            sc_v0 = (sc_v0 + sc_a);\n            return sc_v0;\n        };\n        sc_r = ((sc_r * 1099511628211) ^ sc_f0(1));\n        sc_r = ((sc_r * 1099511628211) ^ sc_twice(sc_f0, 2));\n        sc_v0 = (sc_v0 * 3);\n        let sc_f1: function (word) returns (word) = lam (sc_a: word) -> word {\n            let sc_w0: word = (sc_a ^ sc_v0);\n            let sc_g0: function (word) returns (word) = lam (sc_b: word) -> word {\n                sc_n = (sc_n + sc_b);\n                return sc_w0;\n            };\n            return sc_g0(sc_a);\n        };\n        let sc_i0: word = 0;\n        while (sc_i0 < 2) {\n            sc_r = ((sc_r * 1099511628211) ^ sc_apply(sc_f1, sc_x));\n            sc_n = (sc_n + 1);\n            sc_i0 = sc_i0 + 1;\n        }\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(uint256(sc_n) + uint256(sc_v0)));\n        sc_r = ((sc_r * 1099511628211) ^ sc_v0);\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-closure-captures-corpus.py`. -/
private def captureAResults : List String := [
    "1606938047434833335972620096188801788358848000783666274102747",
    "3213876094869666671945237533921608854007411392590644407808148",
    "4820814142322038027593580087241319828230739493065170926446629",
    "411376140143317334008990066718054602290802472643883525066427678",
    "412983078192248745023957894019203209554830957844379036668572379",
    "2658455994722710284608987683256679454",
    "57896044618658099318723539939177289899255088521622070378576792787622838922715",
    "57896044618658097711785492504343953926637650788815004730013400991639821499422",
    "6427752189739333343890472409387222985304538176208998721731794",
    "12855504379478666687780942160318451209213165485149577849591046",
    "337680341109101764341094482397051414909904497408129784809310316777065952",
    "111870548103525490951846821082546005640018021717948715489006416942732379953710"]

private def captureBSource : String :=
  "import * from std;\nimport * from std.dispatch;\n\nfunction sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(f(x));\n}\n\ncontract SynthesizedClosureCaptures {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_r: word = 0;\n        let sc_f0: function (word) returns (word) = lam (sc_a: word) -> word {\n            return (sc_a + sc_x);\n        };\n        let sc_f1: function (word) returns (word) = lam (sc_a: word) -> word {\n            return (sc_f0(sc_a) * 2);\n        };\n        sc_f0 = lam (sc_a: word) -> word {\n            return (sc_a - 1);\n        };\n        let sc_f2: function (word) returns (word) = sc_f0;\n        sc_r = ((sc_r * 1099511628211) ^ sc_f1(5));\n        sc_r = ((sc_r * 1099511628211) ^ sc_twice(sc_f2, sc_x));\n        let sc_f3: function (word) returns (word) = lam (sc_a: word) -> word {\n            sc_f0 = sc_f2;\n            sc_x = (sc_x + 7);\n            return sc_f0(sc_x);\n        };\n        sc_r = ((sc_r * 1099511628211) ^ sc_f3(0));\n        sc_r = ((sc_r * 1099511628211) ^ Typedef.rep(uint256(1000) / uint256(sc_x)));\n        sc_r = ((sc_r * 1099511628211) ^ sc_x);\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-closure-captures-corpus.py`. -/
private def captureBResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "115792089237316195423570984991149888177543539850739298945253853506823501643279",
    "20461022955012634851387883665818928466087453824448",
    "759980852614687218137970850912710628351288386257160",
    "762903855893704904118990248467526051546605010046275",
    "11692013117154064741928032786676617172570489507925",
    "57896044618658097711785492489728937530194737554405640332843541396440159352822",
    "57896044618658097711785492516035967043789057074748314806405409176527054327893",
    "23384026234301483343869249126235147091343985517802",
    "35076039351456877313794633596647504253542716759847",
    "69203866767887991730708239088241510588253185550707381656835653605187506307379",
    "66590467137755711613137605763369559359066704555422729068136727793818960033221"]

private def factoryASource : String :=
  "import * from std;\nimport * from std.dispatch;\n\nfunction sc_apply<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(x);\n}\n\nfunction sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(f(x));\n}\n\nfunction sc_mk0(sc_p: word) returns (function (word) returns (word)) {\n    let sc_v0: word = (sc_p * 3);\n    let sc_f0: function (word) returns (word) = lam (sc_a: word) -> word {\n        return (sc_v0 + sc_a);\n    };\n    sc_v0 = (sc_v0 + 1);\n    return sc_f0;\n}\n\ncontract SynthesizedClosureFactories {\n    sc_n: word;\n\n    function sc_mk1(sc_p: word) returns (function (word) returns (word)) {\n        sc_n = (sc_n + 1);\n        let sc_v0: word = Typedef.rep(uint256(sc_p) + uint256(sc_n));\n        return lam (sc_a: word) -> word {\n            sc_v0 = (sc_v0 + sc_a);\n            return (sc_v0 + sc_n);\n        };\n    }\n\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_r: word = 0;\n        let sc_f0: function (word) returns (word) = sc_mk0(sc_x);\n        let sc_f1: function (word) returns (word) = sc_mk1(5);\n        let sc_f2: function (word) returns (word) = sc_mk1(sc_x);\n        sc_r = ((sc_r * 1099511628211) ^ sc_f0(2));\n        sc_r = ((sc_r * 1099511628211) ^ sc_twice(sc_f1, 1));\n        let sc_f3: function (word) returns (word) = lam (sc_a: word) -> word {\n            let sc_g0: function (word) returns (word) = sc_mk0(sc_a);\n            return sc_g0(sc_x);\n        };\n        sc_r = ((sc_r * 1099511628211) ^ sc_apply(sc_f3, sc_n));\n        sc_mk1(sc_x);\n        sc_r = ((sc_r * 1099511628211) ^ (sc_f2(0) + sc_n));\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-closure-captures-corpus.py`. -/
private def factoryAResults : List String := [
    "2658455994745679875199835067228688289",
    "6646139986792268601675609808846645438",
    "10633823978882378657691930312756729939",
    "1019517873977104774139231908522905933988",
    "1023505557969194884195248805170909201057",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "57896044618658097711785492504343953926637650788815027699603991839023793508257",
    "57896044618658097711785492504343953926633663104822937589547975505325743885220",
    "14621507970967653010425996785828162272",
    "30572243939318421827926735555419093244",
    "1356938547360336751235279819703705064233719612286739816042460870363168588970",
    "62238545955498807736148623264109886333879795877568360860714063096030990451764"]

private def factoryBSource : String :=
  "import * from std;\nimport * from std.dispatch;\n\nfunction sc_twice<a>(f: function (a) returns (a), x: a) returns (a) {\n    return f(f(x));\n}\n\nfunction sc_mk0(sc_p: word) returns (function (word) returns (word)) {\n    return lam (sc_a: word) -> word {\n        return (sc_a ^ sc_p);\n    };\n}\n\nfunction sc_mk1(sc_p: word) returns (function (word) returns (word)) {\n    let sc_f0: function (word) returns (word) = sc_mk0((sc_p + 1));\n    let sc_v0: word = sc_f0(sc_p);\n    return lam (sc_a: word) -> word {\n        return (sc_p + sc_v0);\n    };\n}\n\ncontract SynthesizedClosureFactories {\n    sc_n: word;\n\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_r: word = 0;\n        let sc_f0: function (word) returns (word) = sc_mk1(7);\n        let sc_f1: function (word) returns (word) = sc_mk0(sc_x);\n        sc_r = ((sc_r * 1099511628211) ^ sc_f0(1));\n        sc_f1 = sc_mk1(sc_x);\n        sc_f0 = sc_f1;\n        let sc_f2: function (word) returns (word) = lam (sc_a: word) -> word {\n            sc_n = (sc_n + sc_a);\n            let sc_w0: word = Typedef.rep(uint256(sc_n) / uint256(sc_a));\n            return sc_w0;\n        };\n        sc_r = ((sc_r * 1099511628211) ^ sc_f2(sc_x));\n        sc_r = ((sc_r * 1099511628211) ^ sc_f0(sc_n));\n        sc_r = ((sc_r * 1099511628211) ^ (sc_n - sc_twice(sc_f1, 3)));\n        return uint256(sc_r);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-closure-captures-corpus.py`. -/
private def factoryBResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "115792089237316195423570985008687907853240741649698586421033012037584448992090",
    "115792089237316195423570985008687907853240741649698586421033012040882983876721",
    "115792089237316195423570985008687907853240741649698586421033012448801797943076",
    "115792089237316195423570985008687907853240741649698586421033012324556983955159",
    "115792089237316195423570985008687907853240741649698586421033012041982495504932",
    "57896044618658097711785492504343953926605749316878304401304220039125442313175",
    "57896044618658097711785492504343953926605749316878304401304220038025930684964",
    "115792089237316195423570985008687907853240741649698586421033012048579565274192",
    "115792089237316195423570985008687907853240741649698586421033012052977611787052",
    "115792089237316195423570984634543488548506764978947037639096604786040685545406",
    "45802211550113947657339199261396042017200235157638602890856971726474902476692"]

private def fixtures : List (String × Profile × Plan × String × List String) := [
  ("captureA", ClosureCaptures.profile, captureA, captureASource, captureAResults),
  ("captureB", ClosureCaptures.profile, captureB, captureBSource, captureBResults),
  ("factoryA", ClosureFactories.profile, factoryA, factoryASource, factoryAResults),
  ("factoryB", ClosureFactories.profile, factoryB, factoryBSource, factoryBResults)]

private def fixtureChecks : IO Unit := do
  for (name, profile, plan, source, results) in fixtures do
    ensure (profile.admitted plan) (name ++ " is not admitted")
    ensure (plan.applied Word.zero).check (name ++ " failed the Core checker")
    ensure ((profile.emit plan).source == source) (name ++ " source differs from its golden text")
    ensure (results.length == inputs.length) (name ++ " golden results are incomplete")
    for (input, expected) in inputs.zip results do
      ensure (referenceText plan input == expected) s!"{name} reference differs at {input}"
      ensure (interpreterText plan input == expected) s!"{name} interpreter differs at {input}"
  let texts := fixtures.flatMap fun (_, _, _, _, results) => results
  for code in ["11", "12"] do
    ensure (texts.contains ("0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ code))
      ("the fixtures reach no Panic(0x" ++ code ++ ")")
  for (plan, site) in [(factoryA, "factory"), (factoryB, "body"), (captureB, "run")] do
    ensure (plan.boundaryRuns.any (·.2 == some site)) s!"no fixture panics in its {site}"

/-! Admission. -/

private def observe : Stmt := .observe (p 0)
private def lam : Stmt := .lambda [] (p 0)
/-- A lambda that captures the closure before it. -/
private def holder : Stmt := .lambda [] (.call .direct ⟨1, 0⟩ (p 0))
private def free : Factory := {method := false, body := [], returns := .lambda [] (p 0)}
private def method : Factory := {free with method := true}
private def make : Stmt := .make 0 (p 0)
private def localResult : Factory := {free with body := [lam], returns := .closure 0}
private def effectfulMake : Stmt := .make 0 (.checked .add (p 0) (.lit 1))
private def localEffect : Factory := {method with body := [lam, .assign .field (.lit 1)], returns := .closure 0}
private def holderResult : Factory := {free with body := [lam], returns := .lambda [] (.call .direct ⟨1, 0⟩ (p 0))}
private def longFactory : Factory := {free with body := List.replicate 4 (.value (.lit 1))}

private def captureRefusals : List (String × Plan) := [
  ("no step", {factories := [], steps := []}),
  ("eleven steps", {factories := [], steps := List.replicate 11 observe}),
  ("no observation", {factories := [], steps := [lam]}),
  ("an undeclared local", {factories := [], steps := [.observe (v 0 0)]}),
  ("an undeclared closure", {factories := [], steps := [.observe (.call .direct ⟨0, 0⟩ (.lit 1))]}),
  ("five Word locals", {factories := [], steps := List.replicate 5 (.value (.lit 1)) ++ [observe]}),
  ("five closures", {factories := [], steps := List.replicate 5 lam ++ [observe]}),
  ("a lambda naming its own closure", {factories := [], steps := [.lambda [] (.call .direct ⟨1, 0⟩ (.lit 1)), observe]}),
  ("an observation in a lambda", {factories := [], steps := [.lambda [observe] (.lit 0), observe]}),
  ("a loop in a lambda", {factories := [], steps := [.lambda [.loop 2 [observe]] (.lit 0), observe]}),
  ("a closure in a loop", {factories := [], steps := [.loop 2 [lam], observe]}),
  ("a loop of four", {factories := [], steps := [.loop 4 [observe]]}),
  ("an empty loop", {factories := [], steps := [.loop 2 [], observe]}),
  ("a depth-three lambda", {factories := [], steps := [.lambda [.lambda [.lambda [] (.lit 0)] (.lit 0)] (.lit 0), observe]}),
  ("a body of four", {factories := [], steps := [.lambda (List.replicate 4 (.value (.lit 1))) (.lit 0), observe]}),
  ("a closure capturing a closure passed to sc_apply", {factories := [], steps := [lam, holder,
    .observe (.call .apply ⟨0, 1⟩ (.lit 1))]}),
  ("a body rebinding a closure to one capturing a closure", {factories := [], steps := [lam, holder,
    .lambda [.realias ⟨1, 0⟩ ⟨1, 1⟩] (.lit 0), observe]}),
  ("a lambda capturing a closure that captures a closure", {factories := [], steps := [lam, holder,
    .lambda [] (.call .direct ⟨1, 1⟩ (p 0)), observe]}),
  ("a literal past a Word", {factories := [], steps := [.observe (.lit (2 ^ 256))]}),
  ("a factory", {factories := [free], steps := [make, observe]})]

private def factoryRefusals : List (String × Plan) := [
  ("no factory", {factories := [], steps := [observe]}),
  ("no factory call", {factories := [free], steps := [observe]}),
  ("three factories", {factories := [free, free, free], steps := [make, observe]}),
  ("the field in a free factory", {factories := [{free with body := [.assign .field (.lit 1)]}], steps := [make, observe]}),
  ("a method called from a free factory", {factories := [method, {free with body := [make]}], steps := [.make 1 (p 0)]}),
  ("a later factory", {factories := [{free with body := [.make 1 (.lit 1)]}, free], steps := [make, observe]}),
  ("an effectful factory returning its closure", {factories := [localEffect], steps := [make, observe]}),
  ("a factory returning a lambda that captures its closure", {factories := [holderResult], steps := [make, observe]}),
  ("an effectful argument to a factory returning its closure", {factories := [localResult], steps := [effectfulMake, observe]}),
  ("a factory of four statements", {factories := [longFactory], steps := [make, observe]}),
  ("an observation in a factory", {factories := [{free with body := [observe]}], steps := [make, observe]})]

private def admissionChecks : IO Unit := do
  for (label, plan) in captureRefusals do
    ensure (!plan.capturesAdmitted) ("closure capture admission accepted " ++ label)
  for (label, plan) in factoryRefusals do
    ensure (!plan.factoriesAdmitted) ("closure factory admission accepted " ++ label)
  for plan in [captureA, captureB, {factories := [], steps := [lam, holder, .observe (.call .direct ⟨0, 1⟩ (.lit 1))]}] do
    ensure plan.capturesAdmitted ("closure capture admission refused a control: " ++ reprStr plan)
    ensure (!plan.factoriesAdmitted) "closure factory admission accepted a plan without a factory"
  for plan in [factoryA, factoryB, {factories := [free], steps := [make, observe]}] do
    ensure plan.factoriesAdmitted ("closure factory admission refused a control: " ++ reprStr plan)
    ensure (!plan.capturesAdmitted) "closure capture admission accepted a plan with a factory"

/-! The reference against the interpreter. -/

private def modelChecks : IO Unit := do
  let mut outcomes := 0
  let mut stops : List String := []
  let mut returns := 0
  for (generate, admitted) in [(generateCaptures, Plan.capturesAdmitted), (generateFactories, Plan.factoriesAdmitted)] do
    let mut checked := 0
    for seed in List.range 200 do
      let plan := (generate (UInt64.ofNat seed)).fit Captures.defaultNodes
      unless admitted plan do continue
      ensure (plan.applied Word.zero).check s!"seed {seed} failed the Core checker"
      checked := checked + 1
      for input in inputs do
        let expected := interpreterText plan input
        ensure (referenceText plan input == expected) s!"seed {seed}: reference and interpreter differ at {input}"
        outcomes := outcomes + 1
        if expected.startsWith "0x4e487b71" then
          unless stops.contains expected do stops := stops ++ [expected]
        else returns := returns + 1
    ensure (checked ≥ 185) s!"only {checked} of 200 seeds drew an admitted plan"
  ensure (outcomes ≥ 4440 && returns > 3000) s!"the model checks reached {outcomes} outcomes, {returns} returns"
  ensure (stops.length == 2) s!"the model checks reached {stops.length} kinds of revert data"

/-! Generation and replay. -/

private def shapeValues (shapes : List (String × List String)) : List (String × String) :=
  shapes.flatMap fun (dimension, values) => values.map (dimension, ·)

private def generationChecks : IO Unit := do
  for (profile, count, inventory) in [(ClosureCaptures.profile, 500, capturesInventory),
      (ClosureFactories.profile, 200, factoriesInventory)] do
    let mut seen : List (String × String) := []
    for seed in List.range count do
      let plan := (profile.generate (UInt64.ofNat seed)).fit Captures.defaultNodes
      ensure (plan == (profile.generate (UInt64.ofNat seed)).fit Captures.defaultNodes) "generation is not deterministic"
      unless profile.admitted plan do continue
      for value in shapeValues (profile.shapes plan) do
        unless seen.contains value do seen := seen ++ [value]
    let all := shapeValues inventory
    for value in seen do
      ensure (all.contains value) s!"{profile.label}: {value.1} {value.2} is outside the inventory"
    for value in all do
      ensure (seen.contains value) s!"{profile.label}: {value.1} {value.2} is never drawn"
    let corpus := profile.generateCases (Seed.ofNat 1) Captures.defaultNodes 64 400 fuel
    let cases ← expect (corpus.getObjValAs? (Array Json) "cases")
    ensure (cases.size == 64) (profile.label ++ ": generation did not complete 64 cases")
    for case in cases do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a generated case does not replay")
    let seeded := profile.generateCases (Seed.ofNat 7) Captures.defaultNodes 24 400 fuel .seeded .nonIdentity
    for case in ← expect (seeded.getObjValAs? (Array Json) "cases") do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a seeded case does not replay")
    let small := (List.range 200).any fun seed =>
      ((profile.generate (UInt64.ofNat seed)).fit profile.minimumNodes).steps.length <
        (profile.generate (UInt64.ofNat seed)).steps.length
    ensure small (profile.label ++ ": the minimum budget never drops a step")
    let below := profile.generateCases (Seed.ofNat 1) (profile.minimumNodes - 1) 8 8 fuel
    ensure ((below.getObjValAs? (Array Json) "cases").toOption.map (·.size) == some 0)
      (profile.label ++ ": generation accepted a budget below the minimum")

/-! Tampering and reduction. -/

private def setObj (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | other => other

private def tamperChecks : IO Unit := do
  for (name, profile, plan, _, _) in fixtures do
    let some checkedPlan := Captures.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError name)
    let case ← expect (profile.emitCase checkedPlan (Word.ofNatModulo 2) (Json.mkObj [("kind", toJson "imported")]) fuel)
    ensure ((profile.replayCase case fuel).toOption == some case) (name ++ " does not replay")
    let source ← expect (case.getObjValAs? String "source")
    let provenance ← expect (case.getObjVal? "provenance")
    let contract ← expect (case.getObjVal? "contract")
    let calldata ← expect (contract.getObjValAs? String "calldata")
    for (label, tampered) in [
        ("source", setObj case "source" (toJson (source ++ "\n"))),
        ("input", setObj case "input" (toJson "3")),
        ("program", setObj case "program" (Json.mkObj [])),
        ("plan", setObj case profile.planKey (profile.planJson {plan with steps := plan.steps.dropLast})),
        ("shapes", setObj case "provenance" (setObj provenance profile.shapesKey (Json.mkObj []))),
        ("generator version", setObj case "provenance" (setObj provenance "generatorVersion" (toJson "core-arrays-v1"))),
        ("calldata", setObj case "contract" (setObj contract "calldata" (toJson (calldata ++ "00")))),
        ("wrapper", setObj case "contract" (setObj contract "name" (toJson "SynthesizedRevertData")))] do
      ensure (profile.replayCase tampered fuel).toOption.isNone (name ++ ": replay accepted an altered " ++ label)
    let forged := setObj case "directCore" (Json.mkObj [("stage", toJson "execution"), ("status", toJson "returned"),
      ("word", toJson "7")])
    ensure ((profile.replayCase forged fuel).toOption == some case) (name ++ ": replay trusted the saved observation")
    let shrunk ← expect (profile.shrinkCases case 64 fuel)
    let candidates ← expect (shrunk.getObjValAs? (Array Json) "cases")
    ensure (candidates.size ≥ 8) (name ++ " has too few reductions")
    for candidate in candidates do
      ensure ((profile.replayCase candidate fuel).toOption == some candidate) (name ++ ": a reduction does not replay")
  let reduced (profile : Profile) (plan : Plan) : IO (List Plan) := do
    let some source := Captures.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError "fixture")
    return (Captures.reductions ⟨source, Word.ofNatModulo 2⟩).map (·.candidate.plan.plan)
  let captures ← reduced ClosureCaptures.profile captureA
  ensure (captures.any fun plan => plan.steps.length < captureA.steps.length) "no reduction removes a step"
  let emptied : Plan := {captureA with steps := captureA.steps.set 1 (.lambda [] (.lit 0))}
  ensure (captures.contains emptied) "no reduction empties a lambda"
  let once : Stmt := .loop 1 [.observe (.call .apply ⟨0, 1⟩ (p 0)), .assign .field (add n (.lit 1))]
  let shortened : Plan := {captureA with steps := captureA.steps.set 6 once}
  ensure (captures.contains shortened) "no reduction shortens the loop"
  let factories ← reduced ClosureFactories.profile factoryA
  ensure (factories.any fun plan => plan.factories != factoryA.factories) "no reduction changes a factory"

def testSourceClosureCaptureCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceClosureCaptureCases
end
