
package org.contract_lib.adapters.translations.terms;

import java.util.Optional;

import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Term;

import com.github.javaparser.ast.expr.Expression;

public interface ImportTermTranslation {

  Optional<Term> translate(Expression expression,
      ImportTermTranslator termTranslator,
      ImportTypeTranslator typeTranslator);
}
