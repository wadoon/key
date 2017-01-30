package de.uka.ilkd.key.gui;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;
import java.util.List;


/**
 * Created by sarah on 1/26/17.
 */
public class Gutter extends JPanel {

    private int numberList;

    private LineNumberPanel num;

    public Gutter(JTextArea textarea){
        this.numberList = 1;


        this.setSize(new Dimension(5, textarea.getHeight()));
        this.setLayout(new BorderLayout());

        this.num = new LineNumberPanel();

        textarea.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent documentEvent) {
                numberList = textarea.getLineCount();

                if(num.currLineCount < numberList){
                    while(num.currLineCount < numberList){
                        num.currLineCount++;
                        num.createNewLabel(num.currLineCount);
                    }
                }

            }

            @Override
            public void removeUpdate(DocumentEvent documentEvent) {
                numberList = textarea.getLineCount();
                if(num.currLineCount > numberList){
                    while(num.currLineCount > numberList){
                        num.currLineCount--;
                        num.removeLabel();
                    }
                }

            }

            @Override
            public void changedUpdate(DocumentEvent documentEvent) {

            }
        });

        this.add(num, BorderLayout.CENTER);

    }

    public List<Integer> getBreakpointLines(){
        return num.retrieveBreakpoints();
    }


}
