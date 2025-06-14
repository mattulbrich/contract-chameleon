

package org.contractlib.contract_chameleon.ast;

import io.PrintStream;

public enum Operator {
  NOT,
  AND,
  OR,
  IMPLIES,
  EQUIVALENCE,
  NOT_EQUIVALENCE;

  void print(PrintStream out, List<Term> parameter) {
    switch (this) {
      case NOT -> printNot(out, parameter);
      case AND -> printAnd(out, parameter);
      case OR -> printOr(out, parameter);
      case IMPLIES -> printImplies(out, parameter); //TODO: check syntax
      case NOT_EQUIVALENCE -> printNotEquivalence(out, parameter);//TODO: check syntax
      case EQUIVALENCE -> printEquivalence(out, parameter);//TODO: check syntax
    }
  }

  void printNot(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("!" + parameter.get(0));
  }
  void printAnd(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("(");
    out.print(parameter.get(0));
    out.print("&");
    out.print(parameter.get(1));
    out.print(")");
  }
  void printOr(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("(");
    out.print(parameter.get(0));
    out.print("|");
    out.print(parameter.get(1));
    out.print(")");
  }

  void printImplies(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("(");
    out.print(parameter.get(0));
    out.print("==>");
    out.print(parameter.get(1));
    out.print(")");
  }
  void printEquivalence(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("(");
    out.print(parameter.get(0));
    out.print("<==>");
    out.print(parameter.get(1));
    out.print(")");
  }

  void printNotEquivalence(PrintStream out, List<Term> parameter) {
    //TODO: Error handlig?
    out.print("(");
    out.print(parameter.get(0));
    out.print("<=!=>");
    out.print(parameter.get(1));
    out.print(")");
  }
}
