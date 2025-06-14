

package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public enum Visibility {
  PUBLIC, PRIVATE, PROTECTED, PACKAGE_PRIVATE;

  void print(PrintStream out) {
    switch (this) {
      case PUBLIC -> out.print("public");
      case PRIVATE -> out.print("private");
      case PUBLIC -> out.print("protected");
      case PACKAGE_PRIVATE -> out.print("");
    }
  }
}
