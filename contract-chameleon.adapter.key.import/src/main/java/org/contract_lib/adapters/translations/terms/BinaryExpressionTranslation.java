
package org.contract_lib.adapters.translations.terms;

import java.util.List;
import java.util.Optional;

import org.contract_lib.adapters.translations.types.ImportTypeTranslator;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.contract_lib.ast.Term;
import org.contract_lib.lang.contract_lib.ast.Term.Identifier.IdentifierValue;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.BinaryExpr.Operator;

public record BinaryExpressionTranslation(
    Operator operator,
    BinaryExpressionTranslationCreator creator)
    implements ImportTermTranslation {

  @FunctionalInterface
  public interface BinaryExpressionTranslationCreator {
    Term translate(Term left, Term right);
  }

  public Optional<Term> translate(
      Expression expression,
      ImportTermTranslator termTranslator,
      ImportTypeTranslator typeTranslator) {
    return expression.toBinaryExpr().flatMap(b -> this.translateBinaryExpression(b, termTranslator));
  }

  public Optional<Term> translateBinaryExpression(BinaryExpr expr, ImportTermTranslator termTranslator) {
    if (!expr.operator().equals(this.operator)) {
      return Optional.empty();
    }
    Optional<Term> left = termTranslator.translate(expr.left());
    Optional<Term> right = termTranslator.translate(expr.right());
    return left.flatMap(l -> right.map(r -> creator.translate(l, r)));
  }

  private static BinaryExpressionTranslation create(Operator operator, String translation) {
    return new BinaryExpressionTranslation(operator,
        (l, r) -> new Term.MethodApplication(new IdentifierValue(new Symbol(translation)), List.of(l, r)));
  }

  public static List<BinaryExpressionTranslation> getAll() {
    return List.of(
        BinaryExpressionTranslation.create(Operator.AND, "and"),
        BinaryExpressionTranslation.create(Operator.BINARY_AND, "and"),
        BinaryExpressionTranslation.create(Operator.OR, "or"),
        BinaryExpressionTranslation.create(Operator.BINARY_OR, "or"),
        BinaryExpressionTranslation.create(Operator.XOR, "xor"),

        BinaryExpressionTranslation.create(Operator.EQUALS, "="), //TODO: check semantics
        BinaryExpressionTranslation.create(Operator.EQUIVALENCE, "="), // TODO: check semantics
        BinaryExpressionTranslation.create(Operator.NOT_EQUALS, "distinct"), // TODO: check semantics
        BinaryExpressionTranslation.create(Operator.ANTIVALENCE, "distinct"), // TODO: check semantics

        BinaryExpressionTranslation.create(Operator.GREATER_EQUALS, ">="),
        BinaryExpressionTranslation.create(Operator.LESS_EQUALS, "<="),
        BinaryExpressionTranslation.create(Operator.GREATER, ">"),
        BinaryExpressionTranslation.create(Operator.LESS, "<"),

        BinaryExpressionTranslation.create(Operator.PLUS, "+"),
        BinaryExpressionTranslation.create(Operator.MINUS, "-"),
        BinaryExpressionTranslation.create(Operator.MULTIPLY, "*"),
        BinaryExpressionTranslation.create(Operator.DIVIDE, "/"),
        BinaryExpressionTranslation.create(Operator.REMAINDER, "mod"),

        BinaryExpressionTranslation.create(Operator.IMPLICATION, "=>"),
        new BinaryExpressionTranslation(Operator.RIMPLICATION, //reverse implication
            (l, r) -> new Term.MethodApplication(new IdentifierValue(new Symbol("=>")), List.of(r, l))));

    /* Untranslatable
      BinaryExpressionTranslation.create(Operator.LEFT_SHIFT, "x"),
      BinaryExpressionTranslation.create(Operator.SIGNED_RIGHT_SHIFT, "x"),
      BinaryExpressionTranslation.create(Operator.UNSIGNED_RIGHT_SHIFT, "x"),
      BinaryExpressionTranslation.create(Operator.SUBTYPE, "x"), // TODO: check semantics
      BinaryExpressionTranslation.create(Operator.SUB_LOCK, "x"), // TODO: check semantics
      BinaryExpressionTranslation.create(Operator.SUB_LOCKE, "x"), // TODO: check semantics
    */

  }
}
