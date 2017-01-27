package de.uka.ilkd.key.gui;

import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.awt.*;

/**
 * Created by sarah on 1/26/17.
 */
public class Gutter extends JPanel {

    int numberList;
    JTextArea lineNumbers;
    LineNumberPanel num;

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
               // updateNumbers();
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
                //updateNumbers();
            }

            @Override
            public void changedUpdate(DocumentEvent documentEvent) {


            }
        });

        this.add(num,BorderLayout.CENTER);

      /*  lineNumbers = new JTextArea();
        lineNumbers.setEditable(false);
        lineNumbers.setSize(this.getSize());*/


      //  lineNumbers.setText("1");

       // this.add(lineNumbers, BorderLayout.WEST);


    }

    private void updateNumbers() {
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i < numberList; i++){
                sb.append(i+"\n");
                   }
        lineNumbers.setText(sb.toString());

    }

}
