package lexerFactories;

import lexerFacade.Lexer;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import javax.annotation.Nullable;
import java.lang.reflect.InvocationTargetException;
import java.util.Map;

public interface LanguageSupportFactory {

    @Nullable
    Lexer create(String toLex);

    Map<Integer, String> allTokenTypeNames();

    SyntaxScheme getSyntaxScheme();

    static SyntaxScheme createSyntaxScheme(String grammarName) {
        try {
            Class<SyntaxScheme> syntaxSchemeClass
                    = (Class<SyntaxScheme>) Class.forName(grammarName + "SyntaxScheme");
            return syntaxSchemeClass.getConstructor().newInstance();
        } catch (ClassNotFoundException | NoSuchMethodException | InstantiationException |
                 IllegalAccessException | InvocationTargetException e) {
            e.printStackTrace();
        }
        return null;
    }

}
