package de.uka.ilkd.key.induction.ui;

import java.awt.Dialog;
import java.awt.Frame;
import java.awt.GraphicsConfiguration;
import java.awt.Window;
import java.util.LinkedList;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.induction.AtomicRelationDescription;
import de.uka.ilkd.key.induction.RelationDescription;
import de.uka.ilkd.key.induction.TacletGenTest;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.TacletApp;

public class RelationDescriptionDialog extends JDialog {

	private JLabel headline;
	private JLabel content;
	private RelationDescription relationdescription;
	
	public RelationDescriptionDialog(JFrame parent, Term term, Services s) {
		super(parent, "Atomic Relation Descriptions");
		
		//TODO: REMOVE this is only for testing
		//TacletGenTest tgt = new TacletGenTest(term, s);
		//tgt.tacletGen();
		//until here
		
		this.setVisible(true);
		this.setSize(350, 175);
		
		this.headline = new JLabel("Relationen Descriptions for " + term.toString());
		this.content = new JLabel();
		
		this.add(headline);
		this.add(content);
		
		this.relationdescription = new RelationDescription(term, s);
		this.displayRelationDescriptions();
	}

	private void displayRelationDescriptions(){
		LinkedList<AtomicRelationDescription> loard = relationdescription.getAtomics();
		
		StringBuilder sb = new StringBuilder();
		for(AtomicRelationDescription ard : loard){
			sb.append(ard.toString());
		}
		
	}
}
