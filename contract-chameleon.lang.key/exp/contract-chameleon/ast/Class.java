
package org.contractlib.contract_chameleon.ast;

import java.io.PrintStream;

public class Class {

  private boolean isAbstract; //TODO: Define extra type for abstract classes?
  private String className;
  private visibility visibility;

  private List<ClassField> fields;          // TODO: Do they really get created?
  private List<String> constructors;    // TODO: Do they really get created?
  private List<Method> methods;         // TODO: Define extra field for abstract and static methods?

  private List<Method> staticMethds;    // TODO: Define extra type?
  private List<ClassField> staticFields;    // TODO: Define extra type?
  
  private List<String> jmlInvariant;    // TODO: Add type
  private List<String> jmlGhostsFields;    // TODO: Add type
  private List<String> jmlModelFields;    // TODO: Add type

  public Class(
    String className,
    String visibility
  ) {
    /*
    this.isAbstract = abstract;
    this.className = className;
    this.visibility = visibility;
    
    this.fields = fields;
    this.constructors = constructors;
    this.methods = methods;

    this.staticFields = staticFields;
    this.staticMethds = staticMethds;
    */
  } 
  
  public void print(PrintStream out) {
    String abstractTag = this.isAbstract ? "abstract" : "";
    
    String fields = this.fields.stream().collect(Collectors.joining(System.lineSeparator()));
    String constructors = this.constructors.stream().collect(Collectors.joining(System.lineSeparator()));
    String methods = this.methods.stream().collect(Collectors.joining(System.lineSeparator()));

    String staticFields = this.staticFields.stream().collect(Collectors.joining(System.lineSeparator()));
    String staticMethds = this.staticMethds.stream().collect(Collectors.joining(System.lineSeparator()));

    out.println(String.format("""
    %s %s class %s {
      %s
      %s
      %s
      %s
      %s
    }
    """,
      visibility,
      abstractTag,
      className,
      fields,
      constructors,
      methods,
      staticFields,
      staticMethds
    ));//TODO: Check order
  }

}
