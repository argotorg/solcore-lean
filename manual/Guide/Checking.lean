import VersoManual
import Solcore.Core.Check

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "What checking guarantees" =>
%%%
tag := "checking-a-program"
file := "checking-a-program"
%%%

Imagine a program that binds the Boolean value `true` to a local variable and
then refers to that variable. We declare that the program's result has Boolean
type. In Core, `letE` introduces the binding, and `var 0` refers to the nearest
binding. The empty context `[]` means there are no pre-existing local variables.

```lean
open Solcore.Core

def acceptedProgram : Program where
  resultType := .bool
  body := .letE (.bool true) (.var 0)

theorem acceptedCheck :
    acceptedProgram.checkDetailedIn [] = .ok .bool := by
  rfl
```

The equality is checked during the manual build. It says that the checker
accepts this program with Boolean type. It does not execute the program or
assert its returned value.

# Change the declared result
%%%
tag := "rejected-program"
%%%

Keep the body but declare a Word result, a 256-bit unsigned integer type.
The checker reports a mismatch between the declared Word type and the inferred
Boolean type. An empty diagnostic path places the error at the program boundary.

```lean
def rejectedProgram : Program :=
  { acceptedProgram with resultType := .word }

example : rejectedProgram.checkDetailedIn [] = .error {
    path := []
    data := .declaredResultTypeMismatch .word .bool } := by
  rfl
```

This is a valid Lean assertion about a rejected Core program. Both the accepted
and rejected cases must keep matching the library for this chapter to build.

# Connect acceptance to a proven guarantee
%%%
tag := "checking-guarantee"
%%%

The specification and theorem below come directly from the library, including
their signatures and source documentation.

{docstring Solcore.Core.Program.WellTypedIn +hideFields +hideStructureConstructor}

{docstring Solcore.Core.Program.checkDetailedIn_iff_wellTyped}

Applying this theorem connects our concrete checker result to that specification:

```lean
example : acceptedProgram.WellTypedIn [] :=
  Program.checkDetailedIn_iff_wellTyped.mp acceptedCheck
```

The proven guarantee here is about Core well-typedness. It does not establish
that a program implements its author's intent or that a Rust compiler preserves
its meaning through EVM bytecode generation. Evaluation and its correspondence
theorems are separate parts of the model.

# The checker declaration
%%%
tag := "checker-declaration"
%%%

The following signature and documentation come from the library. They are
included directly, so this page does not maintain a second copy of the API text.

{docstring Solcore.Core.Program.checkDetailedIn}

The examples in {ref "checking-a-program"}[this chapter] and the theorem
application are checked by Lean. Declaration references resolve against the
imported library. These checks help keep the guide synchronized with code;
the English explanation still needs review when the model changes.
