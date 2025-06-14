package org.contract_lib.lang.contract_lib.ast;


public interface SortDec extends ContractLibAstElement {
  public record Def(
    Symbol name, //TODO: replace Symbol with String
    Numeral rank
  ) implements SortDec {}

  public record Parameter(
    Symbol name //TODO: replace Symbol with String
  ) implements SortDec {}
}
