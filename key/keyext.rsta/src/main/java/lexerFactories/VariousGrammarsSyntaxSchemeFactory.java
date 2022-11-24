package lexerFactories;

import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import rsta.LanguageSupportFactory;
import rsta.Lexer;

import javax.annotation.Nullable;
import java.util.Map;

public class VariousGrammarsSyntaxSchemeFactory implements LanguageSupportFactory {

    private LexerDelegationMap lexerDelegationMap;

    public VariousGrammarsSyntaxSchemeFactory(LexerDelegationMap lexerDelegationMap) {
        this.lexerDelegationMap = lexerDelegationMap;
    }

    @Nullable
    @Override
    public Lexer create(String toLex) {
        return null;
        /*return new Lexer() {

            int nextTokenType, newStartIndex = 0;
            int ne

            @Override
            public void step() {

            }

            @Override
            public boolean finished() {
                return false;
            }

            @Override
            public String nextTokenText() {
                return null;
            }

            @Override
            public Integer nextStartIndex() {
                return null;
            }

            @Override
            public Integer nextTokenType() {
                return null;
            }

            @Override
            public Integer eofTokenType() {
                return null;
            }

            @Override
            public String eofTokenText() {
                return null;
            }
        }*/
    }

    @Override
    public SyntaxScheme getSyntaxScheme() {
        return null;
    }

    /**
     * Note that the lexer order in the map may be relevant.
     */
    public static class LexerDelegationMap {

        private final Map<Lexer, Map<Integer, Lexer>> delegationMap;

        public LexerDelegationMap(Map<Lexer, Map<Integer, Lexer>> delegationMap) {
            this.delegationMap = delegationMap;
        }

        @Nullable
        public Lexer getNextLexer(Lexer currentLexer, Integer tokenType) {
            return delegationMap.get(currentLexer).get(tokenType);
        }

    }
}
