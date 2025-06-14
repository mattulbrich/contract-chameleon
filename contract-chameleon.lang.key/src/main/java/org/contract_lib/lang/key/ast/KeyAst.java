package org.contract_lib.lang.key.ast;

import java.util.List;

public record KeyAst(
  List<KeySort> sorts,
  List<KeyFunction> functions,
  List<KeyDatatype> datatypes
) {}
