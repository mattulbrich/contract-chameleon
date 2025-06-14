
package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class Parameter {

  private static final String PARAMETER_TEMPLATE = "%s %s";

  private JavaType type;
  private String identifier;

  void print(PrintStream out) {
    out.write(String.format(
      PARAMETER_TEMPLATE,
      type,
      identifier
    ));
  }
}
