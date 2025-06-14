
package org.contractlib.contract_chameleon.ast;



public class Field implements FieldOwner {

    private static final String FIELD_SEPARATOR = ".";

    private String identifier;
    private FieldOwner owner;

    void print(PrintStream out) {
      owner.print(out);
      out.print(FIELD_SEPARATOR);
      out.print(identifier); 
  }
}
