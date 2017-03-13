package de.uka.ilkd.key.induction;

import java.awt.Frame;

import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JTextField;
import javax.swing.JTextPane;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class SortsDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = -6799043942993370045L;
	
	public SortsDialog(Frame parent, Term t){
		super(parent, "Sorts of Subterm");
		this.setVisible(true);
		this.setSize(350, 175);
		this.displaySorts(t);
	}
	
	private void displaySorts(Term t){
		InductionHypothesisFinder ihf = new InductionHypothesisFinder();
		ihf.addTerm(t);
		ImmutableArray<Sort> sorts = ihf.getSorts();
		JLabel sortsAsText = new JLabel();
		
		StringBuilder sb = new StringBuilder();
		sb.append("Sorts: ");
		boolean first = true;
		for(Sort s: sorts){
			if(!first){
				sb.append(", ");
			}
			else{
				first = false;
			}
			sb.append(s.declarationString());
		}
		sortsAsText.setText(sb.toString());
		this.add(sortsAsText);
	}
	
}
