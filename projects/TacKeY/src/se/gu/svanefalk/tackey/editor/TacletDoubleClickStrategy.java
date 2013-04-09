package se.gu.svanefalk.tackey.editor;

import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;

/**
 * This Strategy determines what takes place when the user doubleclicks various
 * aspects of a document edited by the associated {@link TacletEditor} instance.
 * 
 * @author christopher
 * 
 */
public class TacletDoubleClickStrategy implements ITextDoubleClickStrategy {

    @Override
    public void doubleClicked(final ITextViewer viewer) {
        System.out.println("Click!");
    }
}
