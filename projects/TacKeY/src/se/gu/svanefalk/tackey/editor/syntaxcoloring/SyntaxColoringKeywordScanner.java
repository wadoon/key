package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import java.util.ArrayList;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

import se.gu.svanefalk.tackey.constants.TacletKeywords;
import se.gu.svanefalk.tackey.editor.colors.ColorManager;
import se.gu.svanefalk.tackey.editor.colors.TacletEditorColors;

public class SyntaxColoringKeywordScanner extends RuleBasedScanner {

    private static ColorManager colorManager = ColorManager.INSTANCE;

    public static SyntaxColoringKeywordScanner createDefaultInstance() {

        final SyntaxColoringKeywordScanner scanner = new SyntaxColoringKeywordScanner();

        final ArrayList<IRule> rules = new ArrayList<>();

        /*
         * Setup the rules for coloring the keywords.
         */
        final Color keywordColor = SyntaxColoringKeywordScanner.colorManager.getColor(TacletEditorColors.KEYWORD);
        final WordRule keywordColoringRule = new WordRule(
                KeywordDetector.getInstance());

        for (final String keyword : TacletKeywords.getAsList()) {

            // TODO: Creating new Tokens for each word only because they are
            // mutable...but is this mutability actually used by the runtime?
            final IToken keywordColoringToken = new Token(new TextAttribute(
                    keywordColor));

            keywordColoringRule.addWord(keyword, keywordColoringToken);
        }

        rules.add(keywordColoringRule);

        /*
         * Add the rules to the scanner
         */
        final IRule[] rawRules = new IRule[rules.size()];
        rules.toArray(rawRules);
        scanner.setRules(rawRules);

        return scanner;
    }

    private SyntaxColoringKeywordScanner() {
    }
}
