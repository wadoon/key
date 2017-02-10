package de.uka.ilkd.key.gui.scripts;

import org.antlr.misc.IntArrayList;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;

import javax.swing.text.BadLocationException;
import java.awt.*;

/**
 * Textarea for the proof script
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

    /**
     * Highlight the lines that fall into the range from and to
     * @param from
     * @param to
     */
    public void highlightLinesatPos(int from, int to){

        String[] split = this.getText().split("\n");
        IntArrayList lines = new IntArrayList();

        String s;
        int size;

        int counter = 0;

        for(int i = 0; i < split.length; i++){
            s = split[i];
            size = s.length();
            counter += size;
            if(counter > from && counter <= to){
                lines.add(i);
            }

        }
        for (int line : lines) {
            highlightLine(line);
        }

    }

    public void loadCurrentScriptToTextarea(ScriptView view){

        ActualScript script = view.getCurrentScript();
        if(script.getCurrentRoot() != null ) {
            String repr = script.getTextReprOfScript();

            this.setText(repr);
        }else{
            this.setText("");
        }
        this.repaint();

    }

}
