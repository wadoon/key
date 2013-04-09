package se.gu.svanefalk.tackey.editors;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.ui.editors.text.FileDocumentProvider;

import se.gu.svanefalk.tackey.constants.TacletKeyWords;
import se.gu.svanefalk.tackey.editors.scanners.TacletSourcePartitionScanner;

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

            TacletSourcePartitionScanner tacletPartitionScanner = new TacletSourcePartitionScanner();
            String[] legalContentTypes = new String[] {
                    TacletSourcePartitionScanner.OPENING_BRACE,
                    TacletSourcePartitionScanner.CLOSING_BRACE,
                    TacletSourcePartitionScanner.DECLARATION,
                    TacletSourcePartitionScanner.KEYWORD };
            IDocumentPartitioner documentPartitioner = new TacletSourcePartitioner(
                    tacletPartitionScanner, legalContentTypes);

            documentPartitioner.connect(document);
            document.setDocumentPartitioner(documentPartitioner);
        }

        return document;
    }
}
