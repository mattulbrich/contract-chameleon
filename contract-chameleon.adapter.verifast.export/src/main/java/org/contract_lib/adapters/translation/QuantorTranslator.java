package org.contract_lib.adapters.translation;

import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Optional;

import org.contract_lib.contract_chameleon.error.ChameleonMessageManager;

import org.contract_lib.lang.contract_lib.ast.Term;
import org.contract_lib.lang.contract_lib.ast.PrePostPair;
import org.contract_lib.lang.contract_lib.ast.Quantor;
import org.contract_lib.lang.contract_lib.ast.SortedVar;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;

public final class QuantorTranslator {

  private final ChameleonMessageManager messageManager;
  private final TermTranslator termTranslator;
  private final TypeTranslator typeTranslator;
  private final PredicateTranslator predTranslator;
  private final HelperTranslator helperTranslator;
  private final List<QuantorTranslation> translations;
 
  public QuantorTranslator(
    List<QuantorTranslation> translations,
    ChameleonMessageManager messageManager,
    TermTranslator termTranslator,
    TypeTranslator typeTranslator,
    PredicateTranslator predTranslator,
    HelperTranslator helperTranslator
  ) {
    this.translations = translations;
    this.messageManager = messageManager;
    this.termTranslator = termTranslator;
    this.typeTranslator = typeTranslator;
    this.predTranslator = predTranslator;
    this.helperTranslator = helperTranslator;
  }

  public VeriFastExpression translate(
    List<VeriFastExpression> predicateList,
    Term.QuantorBinding quantorTerm
  ) {

    Optional<VeriFastExpression> firstTrans = translations.stream()
      .map((q) -> q.translate(
        predicateList,
        quantorTerm,
        termTranslator,
        typeTranslator,
        predTranslator,
        helperTranslator
      ))
      .filter(Optional::isPresent)
      .map(Optional::get)
      .findFirst();

    if (!firstTrans.isPresent()) {
      //TODO: proper error handling
      System.err.println("This quantor term is not supported by this adapter yet: " + quantorTerm);
      return new VeriFastExpression.BooleanValue(true);
    }
    
    return firstTrans.get();
  }
}
