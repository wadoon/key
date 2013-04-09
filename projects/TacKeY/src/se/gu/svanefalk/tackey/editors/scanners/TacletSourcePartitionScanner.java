package se.gu.svanefalk.tackey.editors.scanners;

import java.util.ArrayList;
import java.util.regex.Pattern;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordPatternRule;

import se.gu.svanefalk.tackey.editors.rules.TacletDeclarationRule;
import se.gu.svanefalk.tackey.editors.rules.TacletKeywordRule;

public class TacletSourcePartitionScanner extends RuleBasedPartitionScanner {

    public static final String KEYWORD = "keyword";
    public static final String DECLARATION = "declaration";
    public static final String OPENING_BRACE = "opening_brace";
    public static final String CLOSING_BRACE = "close_brace";

    public TacletSourcePartitionScanner() {

        ArrayList<IPredicateRule> rules = new ArrayList<>();

        /*
         * Setup the partitioning rules.
         */
        rules.add(new TacletDeclarationRule());
        rules.add(new SingleLineRule("{", "{", new Token(OPENING_BRACE)));
        rules.add(new TacletKeywordRule());
        rules.add(new SingleLineRule("}", ";", new Token(CLOSING_BRACE)));

        /*
         * Add the rules to the scanner
         */
        IPredicateRule[] rawRules = new IPredicateRule[rules.size()];
        rules.toArray(rawRules);
        setPredicateRules(rawRules);
    }
}
