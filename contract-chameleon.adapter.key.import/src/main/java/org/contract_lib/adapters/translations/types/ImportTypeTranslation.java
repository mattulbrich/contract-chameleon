
package org.contract_lib.adapters.translations.types;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.type.Type;

public interface ImportTypeTranslation {

  Sort getSort();

  Type getJavaType();

  List<Expression> requiredHelper(String fieldName, Type type);
}
