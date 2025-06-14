
package org.contract_lib.adapters.translation;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;
import org.contract_lib.lang.verifast.ast.VeriFastType;

public final record AbstractionTranslation(
    Sort clibSort,
    VeriFastType verifastType) implements TypeTranslation {

  public Sort getClibSort() {
    return this.clibSort();
  }

  public VeriFastType getVerifastType(
      TypeTranslator typeTranslator,
      Sort sort) {
    return this.verifastType();
  }

  public List<VeriFastExpression> getHelper() {
    return List.of();
  }

  public String getDefaultValue() {
    return "null";
  }
}
