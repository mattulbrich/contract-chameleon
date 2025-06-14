
package org.contract_lib.contract_chameleon.error;

import java.lang.Boolean;

import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.stream.Stream;

public class ChameleonMessageManager {
  
  List<ChameleonReportable> messages = new ArrayList();

  public void report(ChameleonReportable message) {
    messages.add(message);
  }
  
  public Stream<ChameleonReportable> getMessages() {
    return messages.stream();
  }

  public void writeStdErr() {
    System.err.println();
    System.err.println(new ChameleonMessageGroup(messages).getMessage());
  }

  public void check() throws ChameleonMessageGroup {
    if (!messages.isEmpty()) {
      throw new ChameleonMessageGroup(messages);
    }
  }
} 
