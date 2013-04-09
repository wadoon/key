package se.gu.svanefalk.tackey.editor.document;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.ui.editors.text.FileDocumentProvider;

import se.gu.svanefalk.tackey.constants.TacletKeyWords;

/**
 * Provides {@link IDocument} instances representing Taclet source files, stored
 * on disk.
 * 
 * @author christopher
 * 
 */
public class TacletDocumentProvider extends FileDocumentProvider {

    @Override
    protected IDocument createDocument(Object element) throws CoreException {

        /*
         * Create the document according to the standard implementation.
         */
        IDocument document = super.createDocument(element);

        /*
         * Connect this document to a TacletSourcePartitioner before returning
         * it.
         */
        if (document != null) {

            IDocumentPartitioner documentPartitioner = TacletSourcePartitioner.createDefaultInstance();
            documentPartitioner.connect(document);
            document.setDocumentPartitioner(documentPartitioner);
        }

        return document;
    }
}
