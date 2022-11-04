package javacc;

import javacc.Token;

public interface TokenManager {
    //TODO how to make created TokenManagers actually implement this?
    Token getNextToken();

    String getGrammarFileName();
}
