package se.gu.svanefalk.tackey.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;

import se.gu.svanefalk.tackey.editor.colors.ColorManager;
import se.gu.svanefalk.tackey.editor.document.TacletDocumentProvider;

/**
 * Instances of this class represent the main interface for the Taclet editor in
 * TacKeY.
 * 
 * @author christopher
 * 
 */
public class TacletEditor extends TextEditor {
    
    /**
     * The {@link ColorManager} is used in order to handle colors for various
     * partitions of the document being edited.
     */
    private final ColorManager colorManager;

    /**
     * The {@link IDocumentProvider} is used in order to supply the edior with
     * the {@link IDocument} instances which it will work with.
     */
    private final IDocumentProvider documentProvider;

    /**
     * The {@link SourceViewerConfiguration} instance is used in order to
     * customize the behavior of the Taclet editor, and will hence contain the
     * majority of its business logic.
     */
    private final SourceViewerConfiguration tacletEditorConfiguration;

    public TacletEditor() {
        super();

        /*
         * Setup the configuration for this editor
         */
        this.colorManager = ColorManager.INSTANCE;
        this.tacletEditorConfiguration = new TacletEditorConfiguration(
                this.colorManager);
        this.setSourceViewerConfiguration(this.tacletEditorConfiguration);

        /*
         * Setup the document provider
         */
        this.documentProvider = new TacletDocumentProvider();
        this.setDocumentProvider(this.documentProvider);
    }

    @Override
    public void dispose() {
        this.colorManager.dispose();
        super.dispose();
    }

    /**
     * Connects an instance of {@link IEditorInput} to this editor instance,
     * effectively meaning that the editor will be processing user input from
     * this instance until a new one is connected, or until the editor as a
     * whole is disposed of.
     */
    @Override
    protected void doSetInput(final IEditorInput input) throws CoreException {
        super.doSetInput(input);

    }

    @Override
    public Object getAdapter(Class required) {
        return super.getAdapter(required);
    }
}