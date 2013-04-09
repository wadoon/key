package se.gu.svanefalk.tackey.editors;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.swt.graphics.Color;

import se.gu.svanefalk.tackey.editors.colors.ColorManager;
import se.gu.svanefalk.tackey.editors.scanners.TacletKeyWordScanner;
import se.gu.svanefalk.tackey.editors.scanners.TacletSourcePartitionScanner;

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
    private RuleBasedScanner tacletKeyWordScanner;

    /**
     * Used in order to get {@link Color} instances for various elements in the
     * source code being edited.
     */
    private final ColorManager colorManager;

    public TacletEditorConfiguration(ColorManager colorManager) {
        super();
        this.colorManager = colorManager;
    }

    /**
     * Sets the doubleclick strategy to be used for the associated Taclet
     * editor.
     */
    @Override
    public ITextDoubleClickStrategy getDoubleClickStrategy(
            ISourceViewer sourceViewer, String contentType) {
        if (doubleClickStrategy == null)
            doubleClickStrategy = new TacletDoubleClickStrategy();
        return doubleClickStrategy;
    }

    public IPresentationReconciler getPresentationReconciler(
            ISourceViewer sourceViewer) {
        PresentationReconciler reconciler = new PresentationReconciler();
        /*
         * DefaultDamagerRepairer damagerRepairer = new DefaultDamagerRepairer(
         * getTacletKeywordScanner()); reconciler.setDamager(damagerRepairer,
         * TacletSourcePartitionScanner.KEYWORD);
         * reconciler.setRepairer(damagerRepairer,
         * TacletSourcePartitionScanner.KEYWORD);
         */
        return reconciler;
    }

    /**
     * Lazily retrieve a {@link RuleBasedScanner} for handling Taclet keywords.
     * 
     * @return
     */
    private RuleBasedScanner getTacletKeywordScanner() {
        if (tacletKeyWordScanner == null) {
            tacletKeyWordScanner = new TacletKeyWordScanner();
        }
        return tacletKeyWordScanner;
    }

    @Override
    public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {

        return new String[] { TacletSourcePartitionScanner.DECLARATION,
                TacletSourcePartitionScanner.KEYWORD,
                TacletSourcePartitionScanner.OPENING_BRACE,
                TacletSourcePartitionScanner.CLOSING_BRACE };
    }
}