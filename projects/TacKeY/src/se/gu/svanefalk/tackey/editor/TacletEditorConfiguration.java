package se.gu.svanefalk.tackey.editor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.formatter.ContentFormatter;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;
import se.gu.svanefalk.tackey.editor.colors.ColorManager;
import se.gu.svanefalk.tackey.editor.formatting.DeclarationFormattingStrategy;
import se.gu.svanefalk.tackey.editor.formatting.DefaultFormattingStrategy;
import se.gu.svanefalk.tackey.editor.syntaxcoloring.CommentColoringScanner;
import se.gu.svanefalk.tackey.editor.syntaxcoloring.SyntaxColoringKeywordScanner;

/**
 * This configuration class contains the settings, as well as the bulk of
 * business logic, for the {@link TacletEditor} it is associated with.
 * 
 * @author christopher
 * 
 */
public class TacletEditorConfiguration extends SourceViewerConfiguration {

    /**
     * Determines what actions to take when the user doubleclicks an element in
     * the Taclet being edited.
     */
    private ITextDoubleClickStrategy doubleClickStrategy;

    /**
     * Used in order to pick out Taclet language keywords in the document being
     * worked with.
     */
    private RuleBasedScanner keywordColoringScanner = null;

    private RuleBasedScanner commentColoringScanner = null;

    public TacletEditorConfiguration(final ColorManager colorManager) {
        super();
    }

    @Override
    public String[] getConfiguredContentTypes(final ISourceViewer sourceViewer) {

        return new String[] { TacletSourceElements.DECLARATION,
                TacletSourceElements.STATEMENT,
                TacletSourceElements.OPENING_BRACE,
                TacletSourceElements.CLOSING_BRACE };
    }

    /**
     * Sets the doubleclick strategy to be used for the associated Taclet
     * editor.
     */
    @Override
    public ITextDoubleClickStrategy getDoubleClickStrategy(
            final ISourceViewer sourceViewer, final String contentType) {
        if (this.doubleClickStrategy == null) {
            this.doubleClickStrategy = new TacletDoubleClickStrategy();
        }
        return this.doubleClickStrategy;
    }

    /**
     * Lazily retrieve a {@link RuleBasedScanner} for coloring Taclet keywords
     * in the scope of this editor.
     * 
     * @return the scanner
     */
    private RuleBasedScanner getKeywordColoringScanner() {
        if (this.keywordColoringScanner == null) {
            this.keywordColoringScanner = SyntaxColoringKeywordScanner.createInstance();
        }
        return this.keywordColoringScanner;
    }

    private RuleBasedScanner getCommentColoringScanner() {
        if (this.commentColoringScanner == null) {
            this.commentColoringScanner = CommentColoringScanner.createInstance();
        }
        return this.commentColoringScanner;
    }

    @Override
    public IPresentationReconciler getPresentationReconciler(
            final ISourceViewer sourceViewer) {

        final PresentationReconciler reconciler = new PresentationReconciler();

        final DefaultDamagerRepairer keywordRepairer = new DefaultDamagerRepairer(
                this.getKeywordColoringScanner());

        DefaultDamagerRepairer commentRepairer = new DefaultDamagerRepairer(
                getCommentColoringScanner());

        reconciler.setDamager(keywordRepairer, TacletSourceElements.DECLARATION);
        reconciler.setRepairer(keywordRepairer,
                TacletSourceElements.DECLARATION);

        reconciler.setDamager(commentRepairer,
                TacletSourceElements.SINGLE_COMMENT);
        reconciler.setRepairer(commentRepairer,
                TacletSourceElements.SINGLE_COMMENT);

        reconciler.setDamager(commentRepairer,
                TacletSourceElements.NESTED_COMMENT);
        reconciler.setRepairer(commentRepairer,
                TacletSourceElements.NESTED_COMMENT);

        return reconciler;
    }

    @Override
    public IContentFormatter getContentFormatter(ISourceViewer sourceViewer) {

        ContentFormatter formatter = new ContentFormatter();

        formatter.setFormattingStrategy(new DefaultFormattingStrategy(),
                IDocument.DEFAULT_CONTENT_TYPE);
        formatter.setFormattingStrategy(new DeclarationFormattingStrategy(),
                TacletSourceElements.DECLARATION);
        formatter.setFormattingStrategy(new DeclarationFormattingStrategy(),
                TacletSourceElements.KEYWORD);
        formatter.setFormattingStrategy(new DeclarationFormattingStrategy(),
                TacletSourceElements.STATEMENT);
        formatter.setFormattingStrategy(new DeclarationFormattingStrategy(),
                TacletSourceElements.SINGLE_COMMENT);
        formatter.setFormattingStrategy(new DeclarationFormattingStrategy(),
                TacletSourceElements.NESTED_COMMENT);

        return formatter;
    }
}