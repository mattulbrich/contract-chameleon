package org.contract_lib.adapters.translation;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;

public record PredicateTranslation(
  String field,
  String owner,
  boolean old
) {
  private static final String UNDERSCOPE = "_"; 
  private static final String OLD_SUFFIX = "_old"; 

  public String createName() {
    if (old) {
      return this.owner() + UNDERSCOPE + this.field() + OLD_SUFFIX;
    } else {
      return this.owner() + UNDERSCOPE + this.field() ;
    }
  }

  public VeriFastExpression.Variable generateVariable() {
    return new VeriFastExpression.Variable(this.createName());
  }
}
