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

import se.gu.svanefalk.tackey.constants.TacletComparators;
import se.gu.svanefalk.tackey.constants.TacletKeywords;
import se.gu.svanefalk.tackey.constants.TacletOperators;
import se.gu.svanefalk.tackey.constants.TacletTypes;
import se.gu.svanefalk.tackey.editor.colors.ColorManager;
import se.gu.svanefalk.tackey.editor.colors.TacletEditorColors;
import se.gu.svanefalk.tackey.editor.rules.NestedCommentRule;
import se.gu.svanefalk.tackey.editor.rules.SingleCommentRule;

public class SyntaxColoringKeywordScanner extends RuleBasedScanner {

    private static ColorManager colorManager = ColorManager.INSTANCE;

    public static SyntaxColoringKeywordScanner createInstance() {

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
                    keywordColor, null, SWT.BOLD));

            keywordColoringRule.addWord(keyword, keywordColoringToken);
        }

        rules.add(keywordColoringRule);

        /*
         * Setup the rules for coloring types
         */
        final WordRule typeRule = new WordRule(NonNumericDetector.getInstance());

        for (final String keyword : TacletTypes.getAsList()) {

            final IToken typeColoringToken = new Token(new TextAttribute(
                    keywordColor, null, SWT.BOLD));

            typeRule.addWord(keyword, typeColoringToken);
        }

        rules.add(typeRule);

        /*
         * Setup the rules for coloring the comparators
         */
        final WordRule comparatorRule = new WordRule(
                NonNumericDetector.getInstance());

        for (final String comparator : TacletComparators.getAsList()) {

            final IToken comparatorColoringToken = new Token(new TextAttribute(
                    keywordColor, null, SWT.BOLD));

            comparatorRule.addWord(comparator, comparatorColoringToken);
        }

        rules.add(comparatorRule);

        /*
         * Setup the rules for coloring the operators
         */
        final WordRule operatorRule = new WordRule(
                NonNumericDetector.getInstance());

        for (final String operator : TacletOperators.getAsList()) {

            final IToken operatorColoringToken = new Token(new TextAttribute(
                    keywordColor, null, SWT.BOLD));

            operatorRule.addWord(operator, operatorColoringToken);
        }

        rules.add(operatorRule);

        /*
         * Setup the rules for coloring comments within the declaration
         */
        final Color singleCommentColor = colorManager.getColor(TacletEditorColors.SINGLE_COMMENT);
        final Color nestedCommentColor = colorManager.getColor(TacletEditorColors.NESTED_COMMENT);

        IToken singleCommentColoringToken = new Token(new TextAttribute(
                singleCommentColor));
        IToken nestedCommentColoringToken = new Token(new TextAttribute(
                nestedCommentColor));

        rules.add(SingleCommentRule.createCustomInstance(singleCommentColoringToken));
        rules.add(NestedCommentRule.createCustomInstance(nestedCommentColoringToken));

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
