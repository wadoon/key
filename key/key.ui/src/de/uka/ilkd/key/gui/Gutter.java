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

    public JTextArea textarea;

    public Gutter(JTextArea textarea){
        this.numberList = 1;
        this.textarea = textarea;

        this.setSize(new Dimension(5, textarea.getHeight()));
        this.setLayout(new BorderLayout());

        this.num = new LineNumberPanel();

        this.textarea.getDocument().addDocumentListener(new MyDocumentListener(textarea, numberList));

        this.add(num, BorderLayout.CENTER);

    }

    public List<Integer> getBreakpointLines(){
        return num.retrieveBreakpoints();
    }


    private class MyDocumentListener implements DocumentListener {
        JTextArea textarea;
        int numberList;

        public MyDocumentListener(JTextArea textarea, int numberList) {
            this.textarea = textarea;
            this.numberList = numberList;
        }

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
    }
}
