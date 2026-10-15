module

/-
The shared proof parser. `Core` implements the grammar; `Datatypes` elaborates
datatype templates and sort constructors and provides the `parseProof` entry point.
-/

public import Logos.Parser.Datatypes
import all Logos.Parser.Datatypes
