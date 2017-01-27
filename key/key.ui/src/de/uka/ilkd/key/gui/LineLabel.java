package de.uka.ilkd.key.gui;

import javax.swing.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;


/**Label representing a line number and the breakpoint icon
 * Created by sarah on 1/27/17.
 */
public class LineLabel extends JLabel implements MouseListener {

    public Icon getBreakpointIcon() {
        return breakpoint;
    }


    public boolean isBreakPointSet() {
        return breakPointSet;
    }

    public void setBreakPointSet(boolean breakPointSet) {
        this.breakPointSet = breakPointSet;
    }

    //temp icon
    private Icon breakpoint = IconFactory.next(10);
    private DummyIcon dummy = new DummyIcon();
    private boolean breakPointSet;

    public int getLineNumber() {
        return lineNumber;
    }

    private int lineNumber;

    public LineLabel(int lineNumber){
        this.lineNumber = lineNumber;
        this.setBreakPointSet(false);
        this.setIcon(dummy);
        this.setText(String.valueOf(lineNumber));
        this.addMouseListener(this);
    }

    /**
     * Change icon and breakpoint field according to click
     * @param mouseEvent
     */
    @Override
    public void mouseClicked(MouseEvent mouseEvent) {
        if(mouseEvent.getClickCount() == 2) {
            if(isBreakPointSet()){
                this.setIcon(dummy);
                this.setBreakPointSet(false);
            }else{
                this.setIcon(this.getBreakpointIcon());
                this.setBreakPointSet(true);
            }
        }
    }

    @Override
    public void mousePressed(MouseEvent mouseEvent) {

    }

    @Override
    public void mouseReleased(MouseEvent mouseEvent) {

    }

    @Override
    public void mouseEntered(MouseEvent mouseEvent) {

    }

    @Override
    public void mouseExited(MouseEvent mouseEvent) {

    }
}
