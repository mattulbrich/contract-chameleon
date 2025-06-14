package org.contract_lib.adapters.translations.types;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;

public record AbstractionTypeTranslation(
    String clib,
    Type javaType) implements ImportTypeTranslation {

  public Sort getSort() {
    return new Sort.Type(clib);
  }

  public Type getJavaType() {
    return javaType;
  }

  public List<Expression> requiredHelper(String fieldName, Type type) {
    return List.of();
  }
}
