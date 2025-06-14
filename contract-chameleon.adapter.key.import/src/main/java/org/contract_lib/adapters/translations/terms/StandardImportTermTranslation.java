package org.contract_lib.adapters.translations.terms;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.contract_lib.ast.Term;
import org.contract_lib.lang.contract_lib.ast.Term.BooleanLiteral;
import org.contract_lib.lang.contract_lib.ast.Term.NumberLiteral;
import org.contract_lib.lang.contract_lib.ast.Term.Identifier.IdentifierValue;

import com.github.javaparser.ast.expr.BooleanLiteralExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;

public record StandardImportTermTranslation(
    TermTranslationInput translation) implements ImportTermTranslation {

  @FunctionalInterface
  private interface TermTranslationInput {
    Optional<Term> translate(Expression expression, ImportTermTranslator termTranslator);
  }

  public Optional<Term> translate(Expression expression, ImportTermTranslator termTranslator,
      ImportTypeTranslator typeTranslator) {
    return this.translation.translate(expression, termTranslator);
  }

  public static List<StandardImportTermTranslation> getAll() {
    return List.of(
        new StandardImportTermTranslation(
            (e, t) -> e.toEnclosedExpr()
                .map(EnclosedExpr::getInner)
                .flatMap(t::translate)),
        new StandardImportTermTranslation(
            (e, t) -> e.toBooleanLiteralExpr()
                .map(BooleanLiteralExpr::getValue)
                .map(BooleanLiteral::new)),
        new StandardImportTermTranslation(
            (e, t) -> e.toIntegerLiteralExpr()
                .map(IntegerLiteralExpr::getValue)
                .map(NumberLiteral::new)),

        // Translate this
        new StandardImportTermTranslation(
            (e, t) -> e.toThisExpr()
                .map((s) -> new IdentifierValue(new Symbol("this")))),

        // Name expressions (\result as special case)
        new StandardImportTermTranslation(
            (e, t) -> e.toNameExpr()
                .flatMap(f -> StandardImportTermTranslation.translateNameExpression(f, t))),

        // Name methodCallExpr
        new StandardImportTermTranslation(
            (e, t) -> e.toMethodCallExpr()
                .flatMap(f -> StandardImportTermTranslation.translateMethodCallExpression(f, t))),

        // Field access expressions
        new StandardImportTermTranslation(
            (e, t) -> e.toFieldAccessExpr()
                .flatMap(f -> StandardImportTermTranslation.translateFieldAccessExpression(f, t))));
  }

  public static Optional<Term> translateMethodCallExpression(MethodCallExpr methodCallExpr,
      ImportTermTranslator importTermTranslator) {
    //TODO: print error for not successful translation
    List<Term> arguments = methodCallExpr.getArguments()
        .stream()
        .map(importTermTranslator::translate)
        .filter(Optional::isPresent)
        .map(Optional::get)
        .collect(Collectors.toList());

    //TODO: Allow more methd translations
    if (methodCallExpr.getNameAsString().equals("\\old")) {
      return Optional.of(new Term.MethodApplication(new IdentifierValue(new Symbol("old")), arguments));
    }

    //This simply ignores fresh statments
    if (methodCallExpr.getNameAsString().equals("\\fresh")) {
      return Optional.empty();
    }
    if (methodCallExpr.getNameAsString().equals("\\new_elems_fresh")) {
      return Optional.empty();
    }

    return Optional
        .of(new Term.MethodApplication(new IdentifierValue(new Symbol(methodCallExpr.getNameAsString())), arguments));
  }

  public static Optional<Term> translateNameExpression(NameExpr nameExpr,
      ImportTermTranslator importTermTranslator) {
    //TODO: allow extension of special translations
    if (nameExpr.getNameAsString().equals("\\result")) {
      return Optional.of(new IdentifierValue(new Symbol("result")));
    }
    return Optional.of(new IdentifierValue(new Symbol(nameExpr.getNameAsString())));
  }

  public static Optional<Term> translateFieldAccessExpression(FieldAccessExpr fieldAccessExpr,
      ImportTermTranslator importTermTranslator) {
    Optional<Term> scope = importTermTranslator.translate(fieldAccessExpr.getScope());
    return scope
        .map((s) -> new Term.MethodApplication(new IdentifierValue(new Symbol(fieldAccessExpr.getNameAsString())),
            List.of(s)));
  }

}
