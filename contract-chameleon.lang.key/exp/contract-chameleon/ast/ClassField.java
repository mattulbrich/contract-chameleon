

package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class ClassField {

  private Visibility visibility;
  private boolean isFinal;
  private boolean isStatic;
  private Field field;

  void print(PrintStream out) {
    
    visibility.print(out);
    out.print(" ");
    isStatic.print(out);
    out.print(" ");
    isStatic.print(out);
    out.print(" ");
    field.print(out);
    out.print(";");
  }
}
