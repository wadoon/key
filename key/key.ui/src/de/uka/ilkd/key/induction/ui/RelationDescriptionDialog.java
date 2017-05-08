package de.uka.ilkd.key.induction.ui;

import java.awt.Dialog;
import java.awt.Frame;
import java.awt.GraphicsConfiguration;
import java.awt.Toolkit;
import java.awt.Dimension;
import java.awt.Window;
import java.util.LinkedList;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.induction.AtomicRelationDescription;
import de.uka.ilkd.key.induction.RelationDescription;
import de.uka.ilkd.key.induction.RelationDescriptionFactory;
import de.uka.ilkd.key.induction.TacletGenTest;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.TacletApp;

public class RelationDescriptionDialog extends JDialog {

	private static final int DIALOG_WIDTH = 800;
	private static final int DIALOG_HEIGHT = 600;
	
	private JLabel headline;
	private JLabel content;
	private LinkedList<RelationDescription> relationdescriptions;
	
	public RelationDescriptionDialog(JFrame parent, Term term, Services s) {
		super(parent, "Atomic Relation Descriptions");
		
		Dimension screenDim = Toolkit.getDefaultToolkit().getScreenSize();
		
		this.setVisible(true);
		this.setSize(DIALOG_WIDTH, DIALOG_HEIGHT);
		this.setLocation(
				(screenDim.width - DIALOG_WIDTH) / 2, 
				(screenDim.height - DIALOG_HEIGHT) / 2
		);
		
		this.headline = new JLabel("Relationen Descriptions for " + term.toString());
		this.content = new JLabel();
		
		this.add(headline);
		this.add(content);
		
		this.relationdescriptions = RelationDescriptionFactory.generate(term, s);
		this.displayRelationDescriptions();
	}

	private void displayRelationDescriptions(){
		JTextArea textarea = new JTextArea(30,10);
		JScrollPane scrollpane;
		StringBuilder sb = new StringBuilder();
		for(RelationDescription rd : relationdescriptions){
			sb.append("Relation Description:(");
			for(AtomicRelationDescription ard : rd.getAtomics()){
				sb.append(ard.toString());
				sb.append("\n\n");
			}
			sb.append(")\n\n\n");
		}
		
		textarea.setLineWrap(true);
		textarea.setWrapStyleWord(true);
		textarea.setText(sb.toString());
		textarea.setEditable(false);
		scrollpane  = new JScrollPane(textarea);
		this.add(scrollpane);
		
	}
}
