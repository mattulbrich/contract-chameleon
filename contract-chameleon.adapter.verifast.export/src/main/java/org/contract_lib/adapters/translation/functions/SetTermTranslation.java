package org.contract_lib.adapters.translation.functions;

import java.util.List;

import org.contract_lib.adapters.translation.TermTranslation;
import org.contract_lib.adapters.translation.TermTranslationProvider;
import org.contract_lib.lang.contract_lib.ast.Sort;
import org.contract_lib.lang.contract_lib.ast.Term;
import org.contract_lib.lang.contract_lib.ast.Symbol;
import org.contract_lib.lang.verifast.ast.VeriFastExpression;
import org.contract_lib.lang.verifast.ast.VeriFastType;

import static org.contract_lib.adapters.translation.TermTranslation.UnaryOperatorTranslation;
import static org.contract_lib.adapters.translation.TermTranslation.BinaryOperatorTranslation;
import static org.contract_lib.adapters.translation.TermTranslation.FixpointOperatorTranslation;
import static org.contract_lib.adapters.translation.TermTranslation.VeriFastExpressionTranslation;

public final record SetTermTranslation() implements TermTranslationProvider {

  public final static Sort.Type CLIB_BOOLEAN = new Sort.Type("Bool");
  public final static Sort.Type CLIB_GEN = new Sort.Type("A");
  public final static Sort.Type CLIB_SET = new Sort.Type("Seq");
  public final static VeriFastType VERIFAST_BOOLEAN = new VeriFastType("boolean");
  public final static VeriFastType VERIFAST_SET = new VeriFastType("list<A>");
  public final static VeriFastType VERIFAST_GEN = new VeriFastType("A");

  public List<TermTranslation> getAll() {
    return List.of(
        new VeriFastExpressionTranslation(
            new Term.Identifier.IdentifierValue(new Symbol("set.member")),
            (args) -> {
              if (args.size() != 2) {
                System.err.println("expected arguments (set, element) for set.member");
                return new VeriFastExpression.BooleanValue(false);
              } else {
                return new VeriFastExpression.Fixpoint("mem",
                    List.of(args.get(1), args.get(0)));
              }
            },
            List.of(CLIB_SET, CLIB_GEN),
            List.of(VERIFAST_GEN, VERIFAST_GEN),
            CLIB_BOOLEAN,
            VERIFAST_BOOLEAN),
        new VeriFastExpressionTranslation(
            new Term.Identifier.IdentifierValue(new Symbol("set.singleton")),
            (args) -> {
              if (args.size() != 1) {
                System.err.println("expected arguments (elemnt) for set.unit");
                return new VeriFastExpression.BooleanValue(false);
              } else {
                return new VeriFastExpression.Fixpoint("cons",
                    List.of(args.get(0), new VeriFastExpression.Variable("nil")));
              }
            },
            List.of(CLIB_GEN),
            List.of(VERIFAST_GEN),
            CLIB_SET,
            VERIFAST_SET));
  }
}
