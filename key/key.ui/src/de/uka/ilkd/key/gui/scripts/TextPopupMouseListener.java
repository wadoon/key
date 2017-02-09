package de.uka.ilkd.key.gui.scripts;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.scripts.actions.GoToNodeAction;
import de.uka.ilkd.key.gui.scripts.actions.ParseScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.ResetScriptAction;
import de.uka.ilkd.key.gui.scripts.actions.ShowPathAction;
import de.uka.ilkd.key.macros.scripts.ScriptNode;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

/**
 * Created by sarah on 2/7/17.
 */
public class TextPopupMouseListener extends MouseAdapter {
        ScriptView view;
        ActualScript script;

        public TextPopupMouseListener(ScriptView view, ActualScript script){
            super();
            this.view = view;
            this.script = script;
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            if(SwingUtilities.isRightMouseButton(e)) {
                int pos = view.getTextArea().viewToModel(e.getPoint());
                textPopup(e.getPoint(), pos);
            }
        }

    protected void textPopup(Point p, final int pos) {
        final ScriptNode node;
        if(script.getCurrentRoot() != null) {
            node = view.getNodeAtPos(script.getCurrentRoot(), pos);
        } else {
            node = null;
        }

        //JPopupMenu pm = view.getTextArea().getComponentPopupMenu();
        JPopupMenu pm = new JPopupMenu();
        {
            JMenuItem m = new JMenuItem("Show node exception");
            if (node == null || node.getEncounteredException() == null) {
                m.setEnabled(false);
            }
            m.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    ExceptionDialog.showDialog(view.getMainWindow(), node.getEncounteredException());
                }
            });
            pm.add(m);
        }
        /*{
            // TODO Implement me!
            JMenuItem m = new JMenuItem("Reparse from here");
            m.addActionListener(new ActionListener() {
                @Override
                public void actionPerformed(ActionEvent actionEvent) {
                    reparseFromCurrentPos();
                }
            });
            // if (node == null)
            {
                m.setEnabled(false);
            }
            pm.add(m);
        }*/
        {
            JMenuItem m = new JMenuItem(new GoToNodeAction(this.view));
            if (node == null) {
                m.setEnabled(false);
            }

            pm.add(m);
        }
        {
            JMenuItem m = new JMenuItem(new ShowPathAction(this.view));
            if (node == null) {
                m.setEnabled(true);
            }
            pm.add(m);
        }

        pm.addSeparator();
        {
            JMenuItem m = new JMenuItem(new ParseScriptAction(this.view));
            if (script.getAssociatedProof() == null) {
                m.setEnabled(false);
            }

            pm.add(m);
        }
        {
            JMenuItem m = new JMenuItem(new ResetScriptAction(this.view));
            pm.add(m);
        }
        view.getTextArea().setComponentPopupMenu(pm);
        pm.show(view.getTextArea(), p.x, p.y);
    }

}
