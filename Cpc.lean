module

-- This module serves as the root of the `Cpc` library.
-- Import modules here that should be built as part of the library.
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import Cpc.SmtTranslate
import all Cpc.SmtTranslate
public import Cpc.Api
import all Cpc.Api

-- Model semantics and correctness proofs belong to the verification project.
-- This root and both executable targets import only the static SMT interface.

public section
