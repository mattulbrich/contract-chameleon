
package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class JmlResult {
 
  private static final String RESULT_IDENTIFIER = "\\result";

  void print(PrintStream out) {
    out.print(result);
  }
}
