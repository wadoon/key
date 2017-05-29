package de.uka.ilkd.key.induction.ui;

import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.Toolkit;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.List;

import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;

import de.uka.ilkd.key.induction.InductionTacletGenerator;
import de.uka.ilkd.key.induction.RelationDescription;
import de.uka.ilkd.key.induction.RelationDescriptionGenerator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

public class RelationDescriptionDialog extends JDialog {

	private static final int DIALOG_WIDTH = 400;
	private static final int DIALOG_HEIGHT = 300;
	
	private JLabel headline;
	private JLabel content;
	private List<RelationDescription> relationdescriptions;
	private RelationDescription selected;
	private Term t;
	private Services s;
	
	public RelationDescriptionDialog(JFrame parent, Term term, Services s) {
		super(parent, "Atomic Relation Descriptions");
		
		t = term;
		this.s= s;
		selected = null;
		Dimension screenDim = Toolkit.getDefaultToolkit().getScreenSize();
		JButton confirmBtn = new JButton("confirm");
		
		
		this.setSize(DIALOG_WIDTH, DIALOG_HEIGHT);
		this.setLocation(
				(screenDim.width - DIALOG_WIDTH) / 2, 
				(screenDim.height - DIALOG_HEIGHT) / 2
		);
		
		this.headline = new JLabel("Relationen Descriptions for " + term.toString());
		
		this.add(headline);
		
		this.relationdescriptions = RelationDescriptionGenerator.generate(term, s);
		this.displayRelationDescriptions();
		
		//testing section
			
			//System.out.println(InductionFormulaCreator.buildFormula(term, s).toString());
			
		//testing section
			
		confirmBtn.addMouseListener(new MouseListener(){

			@Override
			public void mouseClicked(MouseEvent e) {
				if(selected != null){
					InductionTacletGenerator.generate(t, RelationDescriptionDialog.this.s, selected);
					RelationDescriptionDialog.this.setVisible(false);
					RelationDescriptionDialog.this.dispose();
				}
			}

			@Override
			public void mouseEntered(MouseEvent e) {/*do nothing*/}

			@Override
			public void mouseExited(MouseEvent e) {/*do nothing*/}

			@Override
			public void mousePressed(MouseEvent e) {/*do nothing*/}

			@Override
			public void mouseReleased(MouseEvent e) {/*do nothing*/}
			
		});
		this.setLayout(new GridLayout(3,1));
		this.add(confirmBtn);
		this.setVisible(true);
			
	}

	private void displayRelationDescriptions(){
		JScrollPane scrollpane;
		JPanel scrollcontent = new JPanel();
		scrollcontent.setLayout(new GridLayout(relationdescriptions.size(), 1));
		ButtonGroup group = new ButtonGroup();
		for(RelationDescription rd : relationdescriptions){
			JRadioButton radio = new JRadioButton(rd.toString());
			group.add(radio);
			radio.addMouseListener(new RadioMouseListener(rd, radio));
			scrollcontent.add(radio);
		}
		scrollpane  = new JScrollPane(scrollcontent);
		this.add(scrollpane);
	
	}
	
	private class RadioMouseListener implements MouseListener{

		private RelationDescription rd;
		private JRadioButton radio;
		
		public RadioMouseListener(RelationDescription rd, JRadioButton radio){
			this.rd = rd;
			this.radio = radio;
		}
		
		@Override
		public void mouseClicked(MouseEvent e) {
			if(radio.isSelected()){
				selected = rd;
			}
		}

		@Override
		public void mouseEntered(MouseEvent e) {/*do nothing*/}

		@Override
		public void mouseExited(MouseEvent e) {/*do nothing*/}

		@Override
		public void mousePressed(MouseEvent e) {/*do nothing*/}

		@Override
		public void mouseReleased(MouseEvent e) {/*do nothing*/}
		
	}
}
