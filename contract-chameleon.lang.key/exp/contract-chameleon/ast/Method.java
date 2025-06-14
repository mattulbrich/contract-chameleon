
package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class Method {

  private boolean isAbstract;
  private String methodName;
  private Visibility visibility;

  private List<Parameter> parameters;          // TODO: Add type
  private JavaType returnType;                 // TODO: Add type
  
  Method() {
    //TODO: Implement
  }

  private JmlContract jmlContract;

  void print(PrintStream out) {
    jmlContract.print(out);
    out.print(visibility);
    out.print(isAbstract ? "abstract" : "");
    returnType.print(out);

    out.print(methodName);
    out.print("(");
    out.print(parameters.stream().collect(Collectors.joining(",")));
    out.print(")");
    if (isAbstract) {
      out.print(";");
    } else {
      out.print(" {");
      out.print("  //TODO: Implement");
      if (!returnType.equals("Void")) {
        out.print("  return null;");
      }
      out.print("}");
    }
  }
}
