package se.gu.svanefalk.tackey.editor.rules;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;

public class NestedCommentRule extends MultiLineRule {

    private NestedCommentRule(String startSequence, String endSequence,
            IToken token) {
        super(startSequence, endSequence, token);
    }

    public static NestedCommentRule createDefaultInstance() {

        IToken singleCommentToken = new Token(
                TacletSourceElements.NESTED_COMMENT);

        return createCustomInstance(singleCommentToken);

    }

    public static NestedCommentRule createCustomInstance(IToken token) {

        return new NestedCommentRule("/*", "*/", token);
    }
}
