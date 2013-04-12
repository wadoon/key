package se.gu.svanefalk.tackey.editor.syntaxcoloring;

import java.util.ArrayList;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.ITokenScanner;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.swt.graphics.Color;

import se.gu.svanefalk.tackey.editor.colors.ColorManager;
import se.gu.svanefalk.tackey.editor.colors.TacletEditorColors;
import se.gu.svanefalk.tackey.editor.rules.NestedCommentRule;
import se.gu.svanefalk.tackey.editor.rules.SingleCommentRule;

public class CommentColoringScanner extends RuleBasedScanner {

    private static ColorManager colorManager = ColorManager.INSTANCE;

    public static CommentColoringScanner createInstance() {

        final CommentColoringScanner scanner = new CommentColoringScanner();

        final ArrayList<IRule> rules = new ArrayList<>();

        final Color singleCommentColor = colorManager.getColor(TacletEditorColors.SINGLE_COMMENT);
        final Color nestedCommentColor = colorManager.getColor(TacletEditorColors.NESTED_COMMENT);

        IToken singleCommentColoringToken = new Token(new TextAttribute(
                singleCommentColor));
        IToken nestedCommentColoringToken = new Token(new TextAttribute(
                nestedCommentColor));

        rules.add(SingleCommentRule.createCustomInstance(singleCommentColoringToken));
        rules.add(NestedCommentRule.createCustomInstance(nestedCommentColoringToken));

        final IRule[] rawRules = new IRule[rules.size()];
        rules.toArray(rawRules);
        scanner.setRules(rawRules);

        return scanner;
    }
}