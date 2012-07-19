// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * @author koenn
 *
 */
package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.pp.ILogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.rule.Taclet;

public class TacletView implements ActionListener{

    private JDialog frame;
    private JTextArea content;
    private JScrollPane scrollPane;

    private static TacletView instance = null;


    public static TacletView getInstance() {
        if (instance == null) {
            instance = new TacletView();
        }
        return instance;
    }
    

    private TacletView() {

        frame = new JDialog();
        frame.setTitle("Taclet View");
        frame.setLocationByPlatform(true);

        frame.getContentPane().setLayout(new BorderLayout());

        content = new JTextArea("", 15, 30);       
        content.setEditable(false);
        content.setLineWrap(true);
        content.setWrapStyleWord(true);

        scrollPane = new JScrollPane(content,
                ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

        scrollPane.setWheelScrollingEnabled(true);

        scrollPane.setBorder(BorderFactory.createTitledBorder("Taclet"));	             

        JButton button = new JButton("Close");
        button.addActionListener(this);

        JPanel buttonPane = new JPanel();           
        buttonPane.add(button);

        frame.getContentPane().add(scrollPane, BorderLayout.CENTER);
        frame.getContentPane().add(buttonPane, BorderLayout.SOUTH);

        frame.pack();	   
    }

    
    public void actionPerformed(ActionEvent e){
        frame.setVisible(false);
    }
    
    
    private void showTacletView(Taclet tac, boolean modal, UIConfiguration uic){
	frame.setModal(modal);
        scrollPane.setBorder(BorderFactory.createTitledBorder
                (getDisplayName(tac)));
        content.setText(getTacletByName(tac, uic));

        content.setCaretPosition(0);

        frame.validate();
        frame.setVisible(true);	
    }

    
    public void showTacletView(DefaultMutableTreeNode node, UIConfiguration uic){
        Taclet tac;
        if (node.getUserObject() instanceof Taclet) {
            tac = (Taclet) node.getUserObject();        
        } else return;
        showTacletView(tac,false, uic);

    }

    
    private String getDisplayName(Taclet tac){
        return tac.displayName();
    }


    private String getTacletByName(Taclet tac, UIConfiguration uic){
        String rule;
        ILogicPrinter lp = 
            uic.createLogicPrinter(null, true);
        lp.printTaclet(tac);
        rule = lp.toString();

        return rule;
    }
}
