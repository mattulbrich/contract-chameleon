package org.contract_lib.adapters.translations.types;

import java.util.List;

import org.contract_lib.lang.contract_lib.ast.Sort;

import com.github.javaparser.ast.expr.Expression;

public record ImportTypeTranslationResult(
    Sort sort,
    List<Expression> expressions) {
}
