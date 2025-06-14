package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class OperatorApplication implements Term {

  private String identifier;
  private List<FieldOwner> parameter;

  void print(PrintStream out) {
    out.print(identifier);
    out.print("(");
    parameter.print(out);
    out.print(")");
  }
}
