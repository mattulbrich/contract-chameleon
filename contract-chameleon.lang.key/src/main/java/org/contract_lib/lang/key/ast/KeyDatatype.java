package org.contract_lib.lang.key.ast;

import java.util.List;

public record KeyDatatype(
    KeySort.Custom datatype,
    List<KeyDatatypeConstructor> constructors) {
}
