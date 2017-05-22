package de.uka.ilkd.key.induction.ui;

import java.awt.Dimension;
import java.awt.Toolkit;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import de.uka.ilkd.key.induction.AtomicRelationDescription;
import de.uka.ilkd.key.induction.InductionFormulaCreator;
import de.uka.ilkd.key.induction.InductionTacletGenerator;
import de.uka.ilkd.key.induction.RelationDescription;
import de.uka.ilkd.key.induction.RelationDescriptionGenerator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

public class RelationDescriptionDialog extends JDialog {

	private static final int DIALOG_WIDTH = 800;
	private static final int DIALOG_HEIGHT = 600;
	
	private JLabel headline;
	private JLabel content;
	private List<RelationDescription> relationdescriptions;
	
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
		
		this.relationdescriptions = RelationDescriptionGenerator.generate(term, s);
		this.displayRelationDescriptions();
		
		//testing section
			
			//System.out.println(InductionFormulaCreator.buildFormula(term, s).toString());
			InductionTacletGenerator.generate(term, s);
		//testing section
		
	}

	private void displayRelationDescriptions(){
		JTextArea textarea = new JTextArea(30,10);
		JScrollPane scrollpane;
		StringBuilder sb = new StringBuilder();
		boolean morethenten = false;
		for(RelationDescription rd : relationdescriptions){
			sb.append("Relation Description for ");
			sb.append(rd.getOperator().name().toString());
			sb.append("(");
			LinkedList<AtomicRelationDescription> ards = rd.getAtomics();
			while(ards.size() > 10){	//ensure there is a maximum of 10 AtomicRelationDescriptions displayed.
				ards.removeLast();
				morethenten = true;
			}
			for(AtomicRelationDescription ard : ards){
				sb.append(ard.toString());
				sb.append("\n\n");
			}
			if(morethenten){
				sb.append("...\n\n");
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
