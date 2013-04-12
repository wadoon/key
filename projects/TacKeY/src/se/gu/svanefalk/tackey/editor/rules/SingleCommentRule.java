package se.gu.svanefalk.tackey.editor.rules;

import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;

public class SingleCommentRule extends SingleLineRule {

    private SingleCommentRule(String startSequence, String endSequence,
            IToken token) {
        super(startSequence, endSequence, token);
        // TODO Auto-generated constructor stub
    }

    public static SingleCommentRule createDefaultInstance() {

        IToken singleCommentToken = new Token(
                TacletSourceElements.SINGLE_COMMENT);

        return createCustomInstance(singleCommentToken);

    }

    public static SingleCommentRule createCustomInstance(IToken token) {

        return new SingleCommentRule("//", "\n", token);
    }
}
