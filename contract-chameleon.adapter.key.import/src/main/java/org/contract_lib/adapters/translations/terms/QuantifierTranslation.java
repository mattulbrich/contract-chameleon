package org.contract_lib.adapters.translations.terms;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.contract_lib.adapters.translations.types.ImportTypeTranslationResult;
import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Quantor;
import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.SortedVar;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.contract_lib.ast.Term;

import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlBinder;
import com.github.javaparser.ast.jml.expr.JmlQuantifiedExpr.JmlDefaultBinder;

public record QuantifierTranslation(
    JmlBinder binder,
    QuantifierExpressionCreator creator)
    implements ImportTermTranslation {

  @FunctionalInterface
  public interface QuantifierExpressionCreator {
    Term translate(List<SortedVar> parameters, Term term);
  }

  public Optional<Term> translate(
      Expression expression,
      ImportTermTranslator termTranslator,
      ImportTypeTranslator typeTranslator) {
    return expression.toJmlQuantifiedExpr()
        .flatMap(e -> this.translateQuantifierExpression(e, termTranslator, typeTranslator));
  }

  public Optional<Term> translateQuantifierExpression(JmlQuantifiedExpr expr, ImportTermTranslator termTranslator,
      ImportTypeTranslator importTypeTranslator) {
    if (!expr.getBinder().equals(this.binder)) {
      return Optional.empty();
    }
    //TODO: Handle partial translation
    List<Term> terms = expr.getExpressions().stream()
        .map(termTranslator::translate)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .collect(Collectors.toList());

    List<SortedVar> vars = expr.getVariables().stream()
        .map(p -> QuantifierTranslation.translateVariable(p, importTypeTranslator))
        .collect(Collectors.toList());

    if (terms.isEmpty()) {
      System.err.println("Quantifier is empty.");
      return Optional.empty();
    }
    if (terms.size() > 1) {
      System.err.println("Quantifier with multiple terms are not supported yet.");
      return Optional.empty();
    }

    return Optional.of(this.creator.translate(vars, terms.get(0)));
  }

  public static List<QuantifierTranslation> getAll() {
    //TODO: This are just the most simple translations without any checks
    return List.of(
        new QuantifierTranslation(JmlDefaultBinder.EXISTS, (p, t) -> new Term.QuantorBinding(Quantor.EXISTS, p, t)),
        new QuantifierTranslation(JmlDefaultBinder.FORALL, (p, t) -> new Term.QuantorBinding(Quantor.ALL, p, t)));
  }

  public static SortedVar translateVariable(Parameter parameter, ImportTypeTranslator typeTranslator) {
    Optional<ImportTypeTranslationResult> ts = typeTranslator.translateType(parameter.getType());
    if (ts.isEmpty()) {
      //TODO: translate parameter
      System.err.println("Parameter could not be translated: " + parameter);
    }
    return new SortedVar(new Symbol(parameter.getNameAsString()), ts.get().sort());
  }
}
