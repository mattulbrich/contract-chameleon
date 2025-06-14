package org.contract_lib.lang.contract_lib.ast;

import java.util.List;
import java.util.Map;

public record Abstraction(
    SortDec.Def identifier,
    DatatypeDec datatypeDec
) implements ContractLibAstElement {}
