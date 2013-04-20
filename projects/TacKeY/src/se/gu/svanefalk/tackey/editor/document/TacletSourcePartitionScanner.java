package se.gu.svanefalk.tackey.editor.document;

import java.util.ArrayList;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;
import se.gu.svanefalk.tackey.editor.rules.NestedCommentRule;
import se.gu.svanefalk.tackey.editor.rules.SingleCommentRule;

/**
 * This scanner is used in order to pick out the essential elements of a Taclet
 * source file for the purpose of partitioning it.
 * 
 * @author christopher
 * 
 */
public class TacletSourcePartitionScanner extends RuleBasedPartitionScanner {

    public TacletSourcePartitionScanner() {

        final ArrayList<IPredicateRule> rules = new ArrayList<>();

        /*
         * Setup the partitioning rules.
         */
        rules.add(SingleCommentRule.createDefaultInstance());
        rules.add(NestedCommentRule.createDefaultInstance());
        rules.add(TacletSourceDeclarationRule.createDefaultInstance());

        /*
         * Add the rules to the scanner
         */
        final IPredicateRule[] rawRules = new IPredicateRule[rules.size()];
        rules.toArray(rawRules);
        this.setPredicateRules(rawRules);
    }
}