package org.contract_lib.lang.contract_lib.ast;

public record SelectorDec(
  Symbol symbol,
  Sort sort
) implements ContractLibAstElement {}
