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
    public Gutter(JTextArea textarea){
        this.setSize(new Dimension(5, textarea.getHeight()));
        this.numberList = 1;
        textarea.getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent documentEvent) {
                numberList = textarea.getLineCount();

                updateNumbers();
            }

            @Override
            public void removeUpdate(DocumentEvent documentEvent) {
                numberList = textarea.getLineCount();

                updateNumbers();
            }

            @Override
            public void changedUpdate(DocumentEvent documentEvent) {


            }
        });
        lineNumbers = new JTextArea();
        lineNumbers.setEditable(false);
        lineNumbers.setSize(this.getSize());

        this.setLayout(new BorderLayout());
        lineNumbers.setText("1");

        this.add(lineNumbers, BorderLayout.CENTER);

    }

    private void updateNumbers() {
        StringBuilder sb = new StringBuilder();
        for (int i = 1; i < numberList; i++){
                sb.append(i+"\n");
                   }
        lineNumbers.setText(sb.toString());
    }

}
