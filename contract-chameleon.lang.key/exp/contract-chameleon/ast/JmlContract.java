
package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public class JmlContract {

  private static final String JML_CONTRACT_TEMPLATE = """
  /*@
    @ default_behavior %s %s %s %s
    @ accessible %s;
    @ assignable %s;
    @*/
  """;

  private Set<String> requirements;
  private Set<String> ensures;

  private Set<String> invariants; //TODO: Necessary?

  private Set<Field> accessible; //TODO: Add type
  private Set<Field> assignable; //TODO: Add type 
  
  void print(PrintStream out) {
    String requiredInvariants = ""; //TODO: Implement
    String ensuredInvariants = ""; //TODO: Implement, they might be implicit for this

    out.print(String.format(
      JML_CONTRACT_TEMPLATE,
      requirements,
      requiredInvariants,
      ensures,
      ensuredInvariants,
      accessible,
      assignable
    ));
  }
}

