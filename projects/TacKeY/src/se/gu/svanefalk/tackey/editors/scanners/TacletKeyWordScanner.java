package se.gu.svanefalk.tackey.editors.scanners;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordPatternRule;

import se.gu.svanefalk.tackey.editors.KeywordDetector;
import se.gu.svanefalk.tackey.editors.WhitespaceDetector;
import se.gu.svanefalk.tackey.editors.colors.ColorManager;
import se.gu.svanefalk.tackey.editors.colors.TacletEditorColors;

public class TacletKeyWordScanner extends RuleBasedScanner {

    private final ColorManager colorManager = ColorManager.INSTANCE;

    public TacletKeyWordScanner() {
        super();
        IToken keywordToken = new Token(new TextAttribute(
                colorManager.getColor(TacletEditorColors.KEYWORD)));

        // ArrayList<IPredicateRule> rules = new ArrayList<>();
        IRule[] rules = new IRule[3];

        /*
         * Setup the rules which detect indivdual keywords
         */
        
        rules[0] = new WordPatternRule(KeywordDetector.getInstance(), "\\",
                " ", keywordToken, '\\');
        rules[1] = new WordPatternRule(KeywordDetector.getInstance(), "\\",
                "(", keywordToken, '\\');
                
        rules[2] = new WhitespaceRule(WhitespaceDetector.getInstance());

        /*
         * Add the rules to the scanner
         */
        setRules(rules);
    }
}