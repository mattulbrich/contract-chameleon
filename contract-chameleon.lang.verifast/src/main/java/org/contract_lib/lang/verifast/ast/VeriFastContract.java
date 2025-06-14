package org.contract_lib.lang.verifast.ast;

public record VeriFastContract(
  VeriFastExpression requires,
  VeriFastExpression ensures
) {}
