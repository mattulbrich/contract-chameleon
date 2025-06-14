package org.contract_lib.adapters.translation;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;
import org.contract_lib.lang.verifast.ast.VeriFastType;

public interface TypeTranslation {
  Sort getClibSort();

  VeriFastType getVerifastType(
      TypeTranslator translator,
      Sort sort);

  List<VeriFastExpression> getHelper();

  String getDefaultValue();

  public static List<Sort> getInner(Sort sort) {
    return sort.perform((p) -> List.of(),
        (p) -> p.arguments());
  }
}
