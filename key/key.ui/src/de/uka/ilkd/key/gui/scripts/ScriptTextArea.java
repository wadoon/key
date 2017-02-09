package de.uka.ilkd.key.gui.scripts;

import org.antlr.misc.IntArrayList;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;

import javax.swing.text.BadLocationException;
import java.awt.*;

/**
 * Created by sarah on 2/8/17.
 */
public class ScriptTextArea extends RSyntaxTextArea {

    public ScriptTextArea(){
        super();
        this.setHighlightCurrentLine(false);
    }

    public void highlightLine(int line){
        Color c = this.getCurrentLineHighlightColor();
        try {
            this.addLineHighlight(line, c);
        } catch (BadLocationException e) {
            e.printStackTrace();
        }
    }

    //has a bug
    public void highlightLinesatPos(int from, int to){


        String[] split = this.getText().split("\n");
        IntArrayList lines = new IntArrayList();
        String s;
        int size;
        int counter = -1;
        for(int i = 0; i < split.length; i++){
            s = split[i];
            size = s.length();
            counter += size;
            if(counter >= from && counter <= to){
                lines.add(i);
                System.out.println("Line "+i);

            }

        }
        for (int line : lines) {
            highlightLine(line);
        }

    }

}
