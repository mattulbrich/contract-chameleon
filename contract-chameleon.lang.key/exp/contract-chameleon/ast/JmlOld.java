
package org.contractlib.contract_chameleon.ast;

public class JmlOld {
  private Field field;

  void print(PrintStream out) {
    out.print("\\old(");
    field.print(out);
    out.print(")");
  }
}
