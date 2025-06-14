
package org.contract_lib.adapters.translations.types;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;

public record PrimitiveTypeTranslation(
    String clibSort,
    PrimitiveType.Primitive javaType) implements ImportTypeTranslation {

  public Sort getSort() {
    return new Sort.Type(clibSort);
  }

  public Type getJavaType() {
    return new PrimitiveType(javaType);
  }

  public List<Expression> requiredHelper(String fieldName, Type type) {
    return List.of();
  }

  public static List<PrimitiveTypeTranslation> getAll() {
    return List.of(
        new PrimitiveTypeTranslation("Int", PrimitiveType.Primitive.INT),
        new PrimitiveTypeTranslation("Bool", PrimitiveType.Primitive.BOOLEAN));
  }
}
