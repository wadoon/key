package lexerFactories;

import lexerFacade.Lexer;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.lang.reflect.InvocationTargetException;
import java.util.Collection;
import java.util.Map;

public interface LanguageSupportFactory {

    @Nullable
    Lexer create(String toLex);

    Map<Integer, String> allTokenTypeNames();

    SyntaxScheme getSyntaxScheme();

    Map<Integer, String> allModes();
}
