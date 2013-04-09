package se.gu.svanefalk.tackey.editors;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;

import se.gu.svanefalk.tackey.editors.colors.ColorManager;

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
     * The {@link SourceViewerConfiguration} instance is used in order to
     * customize the behavior of the Taclet editor, and will hence contain the
     * majority of its business logic.
     */
    private final SourceViewerConfiguration tacletEditorConfiguration;

    /**
     * The {@link IDocumentProvider} is used in order to supply the edior with
     * the {@link IDocument} instances which it will work with.
     */
    private final IDocumentProvider documentProvider;

    /**
     * The IEditorInput instance is used to handle user input to this editor.
     */
    private IEditorInput editorInput;

    public TacletEditor() {
        super();

        /*
         * Setup the configuration for this editor
         */
        colorManager = ColorManager.INSTANCE;
        tacletEditorConfiguration = new TacletEditorConfiguration(colorManager);
        setSourceViewerConfiguration(tacletEditorConfiguration);

        /*
         * Setup the document provider
         */
        documentProvider = new TacletDocumentProvider();
        setDocumentProvider(documentProvider);
    }

    /**
     * Connects an instance of {@link IEditorInput} to this editor instance,
     * effectively meaning that the editor will be processing user input from
     * this instance until a new one is connected, or until the editor as a
     * whole is disposed of.
     */
    @Override
    protected void doSetInput(IEditorInput input) throws CoreException {
        super.doSetInput(input);

        this.editorInput = input;

    }

    @Override
    public void dispose() {
        colorManager.dispose();
        super.dispose();
    }
}
