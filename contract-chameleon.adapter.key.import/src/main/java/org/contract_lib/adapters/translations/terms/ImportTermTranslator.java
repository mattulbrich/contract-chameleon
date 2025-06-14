package org.contract_lib.adapters.translations.terms;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Term;

import com.github.javaparser.ast.expr.Expression;

public final class ImportTermTranslator {
  private final List<ImportTermTranslation> importTermTranslations;
  private final ImportTypeTranslator importTypeTranslator;

  public ImportTermTranslator(List<ImportTermTranslation> importTermTranslations,
      ImportTypeTranslator importTypeTranslator) {
    this.importTermTranslations = importTermTranslations;
    this.importTypeTranslator = importTypeTranslator;
  }

  public Optional<Term> translate(Expression expression) {
    List<Term> terms = this.importTermTranslations.stream()
        .map((t) -> t.translate(expression, this, this.importTypeTranslator))
        .filter(Optional::isPresent)
        .map(Optional::get)
        .collect(Collectors.toList());

    if (terms.isEmpty()) {
      System.err.println("Could not translate expression: " + expression + " " + expression.getClass());
      return Optional.empty();
    }
    if (terms.size() > 1) {
      System.err.println("translation of expression is ambiguous: " + expression);
    }
    return Optional.of(terms.get(0));
  }
}
