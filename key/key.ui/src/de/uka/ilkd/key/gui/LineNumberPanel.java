package de.uka.ilkd.key.gui;

import javax.swing.*;
import java.util.LinkedList;
import java.util.List;

/**
 * Panel that conatins all linenumber labels
 * Created by sarah on 1/27/17.
 */
public class LineNumberPanel extends JPanel {

    List<LineLabel> labels;
    int currLineCount;

    public LineNumberPanel(){
        super();
        labels = new LinkedList<>();
        currLineCount = 1;
        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        this.createNewLabel(currLineCount);
    }

   public void createNewLabel(int i){

        LineLabel number = new LineLabel(i);
        labels.add(number);
        update();
    }

    public void update(){
        this.removeAll();
        for (LineLabel label : labels) {
            this.add(label);
        }

        this.revalidate();
        this.repaint();
    }


    public void removeLabel(){
        labels.remove(currLineCount);
        update();
    }
}
