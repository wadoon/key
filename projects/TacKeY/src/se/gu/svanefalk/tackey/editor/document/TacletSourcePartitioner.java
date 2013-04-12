package se.gu.svanefalk.tackey.editor.document;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.rules.FastPartitioner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;

import se.gu.svanefalk.tackey.constants.TacletSourceElements;

/**
 * Instances of this class are used in order to partition Taclet source files.
 * 
 * @author christopher
 * 
 */
public class TacletSourcePartitioner extends FastPartitioner {

    /**
     * Creates a custome implementation of the Taclet source partitioner.
     * 
     * @param scanner
     *            scanner to use
     * @param legalContentTypes
     *            content type to look for
     * @return the custom implementation
     */
    public static TacletSourcePartitioner createCustomInstance(
            final IPartitionTokenScanner scanner,
            final String[] legalContentTypes) {
        return new TacletSourcePartitioner(scanner, legalContentTypes);
    }

    /**
     * @return a default implementation of the Taclet source partitioner,
     *         recognizing the basic source elements and partitioning
     *         accordingly.
     */
    public static TacletSourcePartitioner createDefaultInstance() {

        final TacletSourcePartitionScanner tacletPartitionScanner = new TacletSourcePartitionScanner();

        final String[] legalContentTypes = new String[] {
                TacletSourceElements.DECLARATION,
                TacletSourceElements.SINGLE_COMMENT,
                TacletSourceElements.NESTED_COMMENT };

        return new TacletSourcePartitioner(tacletPartitionScanner,
                legalContentTypes);
    }

    private TacletSourcePartitioner(final IPartitionTokenScanner scanner,
            final String[] legalContentTypes) {
        super(scanner, legalContentTypes);
    }

    /**
     * Connects this Taclet source partitioner to an {@link IDocument}
     * representing a Taclet source file.
     */
    @Override
    public void connect(final IDocument document,
            final boolean delayInitialization) {
        super.connect(document, delayInitialization);
        this.printPartitions(document);
    }

    /**
     * Test method to write out partitions.
     * 
     * @param document
     */
    public void printPartitions(final IDocument document) {
        final StringBuffer buffer = new StringBuffer();

        final ITypedRegion[] partitions = this.computePartitioning(0,
                document.getLength());
        for (int i = 0; i < partitions.length; i++) {
            try {
                buffer.append("Partition type: " + partitions[i].getType()
                        + ", offset: " + partitions[i].getOffset()
                        + ", length: " + partitions[i].getLength());
                buffer.append("\n");
                buffer.append("Text:\n");
                buffer.append(document.get(partitions[i].getOffset(),
                        partitions[i].getLength()));
                buffer.append("\n---------------------------\n\n\n");
            } catch (final BadLocationException e) {
                e.printStackTrace();
            }
        }
        System.out.print(buffer);
    }
}