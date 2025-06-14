

package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class OperatorApplication implements Term {

  private Operator operator;
  private List<Term> parameter;

  void print(PrintStream out) {
    operator.print(out, parameter);
  }
}
