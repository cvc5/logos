module

-- This module serves as the root of the `Logos` library, which holds the
-- signature-independent parts of the checker: the s-expression reader and the
-- table-driven proof parser that the generated `Cpc.Parser` configuration
-- plugs into.
public import Logos.Sexp
import all Logos.Sexp
public import Logos.Parser
import all Logos.Parser

public section
