
package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class JavaType extends Signature {

  private String identifier;

  void print(PrintStream out) {
    out.write(identifier);
  }
}
