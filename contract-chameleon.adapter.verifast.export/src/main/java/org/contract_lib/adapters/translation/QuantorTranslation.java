
package org.contract_lib.adapters.translation;

import java.util.Optional;
import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Term;

import org.contract_lib.lang.verifast.ast.VeriFastExpression;

public interface QuantorTranslation {
  Optional<VeriFastExpression> translate(
    List<VeriFastExpression> predicateList,
    Term.QuantorBinding quantorTerm,
    TermTranslator TermTranslator,
    TypeTranslator typeTranslator,
    PredicateTranslator predTranslator,
    HelperTranslator helperTranslator
  );
}
