package de.uka.ilkd.key.induction.ui;

import java.awt.Dialog;
import java.awt.Frame;
import java.awt.GraphicsConfiguration;
import java.awt.Window;

import javax.swing.JDialog;
import javax.swing.JLabel;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.induction.ConstructorExtractor;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

public class ConstructorDialog extends JDialog {

	public ConstructorDialog(Frame parent, Term t, Namespace func_ns) {
		super(parent, "Constructors");
		
		this.setVisible(true);
		this.setSize(350, 175);
		
		//display constructors
		ConstructorExtractor ce = new ConstructorExtractor(t, func_ns);
		ImmutableArray<Function> constructors = ce.getConstructors();
		JLabel constructorsAsText = new JLabel();
		
		StringBuilder sb = new StringBuilder();
		sb.append("Constructos: ");
		boolean first = true;
		for(Function f: constructors){
			if(!first){
				sb.append(", ");
			}
			else{
				first = false;
			}
			sb.append(f.toString());
		}
		constructorsAsText.setText(sb.toString());
		this.add(constructorsAsText);
	}

}
